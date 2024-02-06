/*
 *  GRUB  --  GRand Unified Bootloader
 *  Copyright (C) 2012  Free Software Foundation, Inc.
 *
 *  GRUB is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  GRUB is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with GRUB.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <grub/loader.h>
#include <grub/file.h>
#include <grub/err.h>
#include <grub/types.h>
#include <grub/mm.h>
#include <grub/cpu/linux.h>
#include <grub/command.h>
#include <grub/i18n.h>
#include <grub/lib/cmdline.h>
#include <grub/efi/efi.h>
#include <grub/386/efi/linux.h>
#include <grub/cpu/efi/memory.h>
#include <grub/tpm.h>
#include <grub/safemath.h>

GRUB_MOD_LICENSE ("GPLv3+");

static grub_dl_t my_mod;

static grub_command_t cmd_linux, cmd_initrd;
static grub_command_t cmd_linuxefi, cmd_initrdefi;

struct grub_linuxefi_context {
  void *kernel_mem;
  grub_uint64_t kernel_size;
  grub_uint32_t handover_offset;
  struct linux_kernel_params *params;
  char *cmdline;
  int nx_supported;
  void *initrd_mem;
};

#define MIN(a, b) \
  ({ typeof (a) _a = (a); \
     typeof (b) _b = (b); \
     _a < _b ? _a : _b; })

#define BYTES_TO_PAGES(bytes)   (((bytes) + 0xfff) >> 12)

struct allocation_choice {
    grub_efi_physical_address_t addr;
    grub_efi_allocate_type_t alloc_type;
};

enum {
    KERNEL_PREF_ADDRESS,
    KERNEL_4G_LIMIT,
    KERNEL_NO_LIMIT,
};

static struct allocation_choice max_addresses[] =
  {
    /* the kernel overrides this one with pref_address and
     * GRUB_EFI_ALLOCATE_ADDRESS */
    [KERNEL_PREF_ADDRESS] =
      { GRUB_EFI_MAX_ALLOCATION_ADDRESS, GRUB_EFI_ALLOCATE_MAX_ADDRESS },
    /* If the flag in params is set, this one gets changed to be above 4GB. */
    [KERNEL_4G_LIMIT] =
      { GRUB_EFI_MAX_ALLOCATION_ADDRESS, GRUB_EFI_ALLOCATE_MAX_ADDRESS },
    /* this one is always below 4GB, which we still *prefer* even if the flag
     * is set. */
    [KERNEL_NO_LIMIT] =
      { GRUB_EFI_MAX_ALLOCATION_ADDRESS, GRUB_EFI_ALLOCATE_MAX_ADDRESS },
    { NO_MEM, 0, 0 }
  };

static struct allocation_choice saved_addresses[4];

#define save_addresses() grub_memcpy(saved_addresses, max_addresses, sizeof(max_addresses))
#define restore_addresses() grub_memcpy(max_addresses, saved_addresses, sizeof(max_addresses))

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wcast-align"
#pragma GCC diagnostic ignored "-Wint-to-pointer-cast"

grub_err_t
grub_efi_check_nx_image_support (grub_addr_t kernel_addr,
				 grub_size_t kernel_size,
				 int *nx_supported)
{
  struct grub_dos_header *doshdr;
  grub_size_t sz = sizeof (*doshdr);

  struct grub_pe32_header_32 *pe32;
  struct grub_pe32_header_64 *pe64;

  int image_is_compatible = 0;
  int is_64_bit;

  if (kernel_size < sz)
    return grub_error (GRUB_ERR_BAD_OS, N_("kernel is too small"));

  doshdr = (void *)kernel_addr;

  if ((doshdr->magic & 0xffff) != GRUB_DOS_MAGIC)
    return grub_error (GRUB_ERR_BAD_OS, N_("kernel DOS magic is invalid"));

  sz = doshdr->lfanew + sizeof (*pe32);
  if (kernel_size < sz)
    return grub_error (GRUB_ERR_BAD_OS, N_("kernel is too small"));

  pe32 = (struct grub_pe32_header_32 *)(kernel_addr + doshdr->lfanew);
  pe64 = (struct grub_pe32_header_64 *)pe32;

  if (grub_memcmp (pe32->signature, GRUB_PE32_SIGNATURE,
		   GRUB_PE32_SIGNATURE_SIZE) != 0)
    return grub_error (GRUB_ERR_BAD_OS, N_("kernel PE magic is invalid"));

  switch (pe32->coff_header.machine)
    {
    case GRUB_PE32_MACHINE_ARMTHUMB_MIXED:
    case GRUB_PE32_MACHINE_I386:
    case GRUB_PE32_MACHINE_RISCV32:
      is_64_bit = 0;
      break;
    case GRUB_PE32_MACHINE_ARM64:
    case GRUB_PE32_MACHINE_IA64:
    case GRUB_PE32_MACHINE_RISCV64:
    case GRUB_PE32_MACHINE_X86_64:
      is_64_bit = 1;
      break;
    default:
      return grub_error (GRUB_ERR_BAD_OS, N_("PE machine type 0x%04hx unknown"),
			 pe32->coff_header.machine);
    }

  if (is_64_bit)
    {
      sz = doshdr->lfanew + sizeof (*pe64);
      if (kernel_size < sz)
	return grub_error (GRUB_ERR_BAD_OS, N_("kernel is too small"));

      if (pe64->optional_header.dll_characteristics & GRUB_PE32_NX_COMPAT)
	image_is_compatible = 1;
    }
  else
    {
      if (pe32->optional_header.dll_characteristics & GRUB_PE32_NX_COMPAT)
	image_is_compatible = 1;
    }

  *nx_supported = image_is_compatible;
  return GRUB_ERR_NONE;
}

grub_err_t
grub_efi_check_nx_required (int *nx_required)
{
  grub_efi_status_t status;
  grub_efi_guid_t guid = GRUB_EFI_SHIM_LOCK_GUID;
  grub_size_t mok_policy_sz = 0;
  char *mok_policy = NULL;
  grub_uint32_t mok_policy_attrs = 0;

  status = grub_efi_get_variable_with_attributes ("MokPolicy", &guid,
						  &mok_policy_sz,
						  (void **)&mok_policy,
						  &mok_policy_attrs);
  if (status == GRUB_EFI_NOT_FOUND ||
      mok_policy_sz == 0 ||
      mok_policy == NULL)
    {
      *nx_required = 0;
      return GRUB_ERR_NONE;
    }

  *nx_required = 0;
  if (mok_policy_sz < 1 ||
      mok_policy_attrs != (GRUB_EFI_VARIABLE_BOOTSERVICE_ACCESS |
			   GRUB_EFI_VARIABLE_RUNTIME_ACCESS) ||
      (mok_policy[mok_policy_sz-1] & GRUB_MOK_POLICY_NX_REQUIRED))
    *nx_required = 1;

  return GRUB_ERR_NONE;
}

typedef void (*handover_func) (void *, grub_efi_system_table_t *, void *);

grub_err_t
grub_efi_linux_boot (grub_addr_t kernel_addr, grub_size_t kernel_size,
		     grub_off_t handover_offset, void *kernel_params,
		     int nx_supported)
{
  grub_efi_loaded_image_t *loaded_image = NULL;
  handover_func hf;
  int offset = 0;
  grub_uint64_t stack_set_attrs = GRUB_MEM_ATTR_R |
				  GRUB_MEM_ATTR_W |
				  GRUB_MEM_ATTR_X;
  grub_uint64_t stack_clear_attrs = 0;
  grub_uint64_t kernel_set_attrs = stack_set_attrs;
  grub_uint64_t kernel_clear_attrs = stack_clear_attrs;
  grub_uint64_t attrs;
  int nx_required = 0;

#ifdef __x86_64__
  offset = 512;
#endif

  /*
   * Since the EFI loader is not calling the LoadImage() and StartImage()
   * services for loading the kernel and booting respectively, it has to
   * set the Loaded Image base address.
   */
  loaded_image = grub_efi_get_loaded_image (grub_efi_image_handle);
  if (loaded_image)
    loaded_image->image_base = (void *)kernel_addr;
  else
    grub_dprintf ("linux", "Loaded Image base address could not be set\n");

  grub_dprintf ("linux", "kernel_addr: %p handover_offset: %p params: %p\n",
		(void *)kernel_addr, (void *)handover_offset, kernel_params);


  if (nx_required && !nx_supported)
    return grub_error (GRUB_ERR_BAD_OS, N_("kernel does not support NX loading required by policy"));

  if (nx_supported)
    {
      kernel_set_attrs &= ~GRUB_MEM_ATTR_W;
      kernel_clear_attrs |= GRUB_MEM_ATTR_W;
      stack_set_attrs &= ~GRUB_MEM_ATTR_X;
      stack_clear_attrs |= GRUB_MEM_ATTR_X;
    }

  grub_dprintf ("nx", "Setting attributes for 0x%"PRIxGRUB_ADDR"-0x%"PRIxGRUB_ADDR" to r%cx\n",
		    kernel_addr, kernel_addr + kernel_size - 1,
		    (kernel_set_attrs & GRUB_MEM_ATTR_W) ? 'w' : '-');
  grub_update_mem_attrs (kernel_addr, kernel_size,
			 kernel_set_attrs, kernel_clear_attrs);

  grub_get_mem_attrs (kernel_addr, 4096, &attrs);
  grub_dprintf ("nx", "permissions for 0x%"PRIxGRUB_ADDR" are %s%s%s\n",
		(grub_addr_t)kernel_addr,
		(attrs & GRUB_MEM_ATTR_R) ? "r" : "-",
		(attrs & GRUB_MEM_ATTR_W) ? "w" : "-",
		(attrs & GRUB_MEM_ATTR_X) ? "x" : "-");
  if (grub_stack_addr != (grub_addr_t)-1ll)
    {
      grub_dprintf ("nx", "Setting attributes for stack at 0x%"PRIxGRUB_ADDR"-0x%"PRIxGRUB_ADDR" to rw%c\n",
		    grub_stack_addr, grub_stack_addr + grub_stack_size - 1,
		    (stack_set_attrs & GRUB_MEM_ATTR_X) ? 'x' : '-');
      grub_update_mem_attrs (grub_stack_addr, grub_stack_size,
			     stack_set_attrs, stack_clear_attrs);

      grub_get_mem_attrs (grub_stack_addr, 4096, &attrs);
      grub_dprintf ("nx", "permissions for 0x%"PRIxGRUB_ADDR" are %s%s%s\n",
		    grub_stack_addr,
		    (attrs & GRUB_MEM_ATTR_R) ? "r" : "-",
		    (attrs & GRUB_MEM_ATTR_W) ? "w" : "-",
		    (attrs & GRUB_MEM_ATTR_X) ? "x" : "-");
    }

#if defined(__i386__) || defined(__x86_64__)
  asm volatile ("cli");
#endif

  hf = (handover_func)((char *)kernel_addr + handover_offset + offset);
  hf (grub_efi_image_handle, grub_efi_system_table, kernel_params);

  return GRUB_ERR_BUG;
}

#pragma GCC diagnostic pop

static inline void
kernel_free(void *addr, grub_efi_uintn_t size)
{
  if (addr && size)
    grub_efi_free_pages ((grub_efi_physical_address_t)(grub_addr_t)addr,
                         BYTES_TO_PAGES(size));
}

static void *
kernel_alloc(grub_efi_uintn_t size,
	     grub_efi_memory_type_t memtype,
	     const char * const errmsg)
{
  void *addr = 0;
  unsigned int i;
  grub_efi_physical_address_t prev_max = 0;

  for (i = 0; max_addresses[i].addr != 0 && addr == 0; i++)
    {
      grub_uint64_t max = max_addresses[i].addr;
      grub_efi_uintn_t pages;

      /*
       * When we're *not* loading the kernel, or >4GB allocations aren't
       * supported, these entries are basically all the same, so don't re-try
       * the same parameters.
       */
      if (max == prev_max)
        continue;

      pages = BYTES_TO_PAGES(size);
      grub_dprintf ("linux", "Trying to allocate %lu pages from %p\n",
                   (unsigned long)pages, (void *)(unsigned long)max);
      size = pages * GRUB_EFI_PAGE_SIZE;

      prev_max = max;
      addr = grub_efi_allocate_pages_real (max, pages,
                                           max_addresses[i].alloc_type,
                                           memtype);
      if (addr)
	{
	  grub_dprintf ("linux", "Allocated at %p\n", addr);
	  grub_update_mem_attrs ((grub_addr_t)addr, size,
				 GRUB_MEM_ATTR_R|GRUB_MEM_ATTR_W,
				 GRUB_MEM_ATTR_X);
	}
    }

  while (grub_error_pop ())
    {
      ;
    }

  if (addr == NULL)
    grub_error (GRUB_ERR_OUT_OF_MEMORY, "%s", errmsg);

  return addr;
}

static grub_err_t
grub_linuxefi_boot (void *data)
{
  struct grub_linuxefi_context *context = (struct grub_linuxefi_context *) data;

  int offset = 0;

#ifdef __x86_64__
  offset = 512;
#endif
  asm volatile ("cli");

  return grub_efi_linux_boot ((grub_addr_t)context->kernel_mem,
			      context->kernel_size,
			      context->handover_offset,
			      context->params,
			      context->nx_supported);
}

static grub_err_t
grub_linuxefi_unload (void *data)
{
  struct grub_linuxefi_context *context = (struct grub_linuxefi_context *) data;
  struct linux_kernel_params *params = context->params;

  grub_dl_unref (my_mod);
  kernel_free (context->initrd_mem, params->ramdisk_size);
  kernel_free (context->cmdline, params->cmdline_size + 1);
  kernel_free (context->kernel_mem, context->kernel_size);
  kernel_free (params, sizeof(*params));
  cmd_initrd->data = 0;
  cmd_initrdefi->data = 0;
  grub_free (context);

  return GRUB_ERR_NONE;
}

#define BOUNCE_BUFFER_MAX 0x1000000ull

static grub_ssize_t
read(grub_file_t file, grub_uint8_t *bufp, grub_size_t len)
{
  grub_ssize_t bufpos = 0;
  static grub_size_t bbufsz = 0;
  static char *bbuf = NULL;

  if (bbufsz == 0)
    bbufsz = MIN(BOUNCE_BUFFER_MAX, len);

  while (!bbuf && bbufsz)
    {
      bbuf = grub_malloc(bbufsz);
      if (!bbuf)
        bbufsz >>= 1;
    }
  if (!bbuf)
    grub_error (GRUB_ERR_OUT_OF_MEMORY, N_("cannot allocate bounce buffer"));

  while (bufpos < (long long)len)
    {
      grub_ssize_t sz;

      sz = grub_file_read (file, bbuf, MIN(bbufsz, len - bufpos));
      if (sz < 0)
        return sz;
      if (sz == 0)
        break;

      grub_memcpy(bufp + bufpos, bbuf, sz);
      bufpos += sz;
    }

  return bufpos;
}

#define LOW_U32(val) ((grub_uint32_t)(((grub_addr_t)(val)) & 0xffffffffull))
#define HIGH_U32(val) ((grub_uint32_t)(((grub_addr_t)(val) >> 32) & 0xffffffffull))

static grub_err_t
grub_cmd_initrd (grub_command_t cmd, int argc, char *argv[])
{
  grub_file_t *files = 0;
  int i, nfiles = 0;
  grub_size_t size = 0;
  grub_uint8_t *ptr;
  struct grub_linuxefi_context *context = (struct grub_linuxefi_context *) cmd->data;
  struct linux_kernel_params *params;
  void *initrd_mem = 0;

 if (argc == 0)
    {
      grub_error (GRUB_ERR_BAD_ARGUMENT, N_("filename expected"));
      goto fail;
    }

  if (!context)
    {
      grub_error (GRUB_ERR_BAD_ARGUMENT, N_("you need to load the kernel first"));
      goto fail;
    }

  params = context->params;

  files = grub_calloc (argc, sizeof (files[0]));
  if (!files)
    goto fail;

  for (i = 0; i < argc; i++)
    {
      files[i] = grub_file_open (argv[i], GRUB_FILE_TYPE_LINUX_INITRD | GRUB_FILE_TYPE_NO_DECOMPRESS);
      if (! files[i])
        goto fail;
      nfiles++;
      if (grub_add (size, ALIGN_UP (grub_file_size (files[i]), 4), &size))
	{
	  grub_error (GRUB_ERR_OUT_OF_RANGE, N_("overflow is detected"));
	  goto fail;
	}
    }

  initrd_mem = kernel_alloc(size, GRUB_EFI_RUNTIME_SERVICES_DATA,
			    N_("can't allocate initrd"));
  if (initrd_mem == NULL)
    goto fail;
  grub_dprintf ("linux", "initrd_mem = %p\n", initrd_mem);

  params->ramdisk_size = LOW_U32(size);
  params->ramdisk_image = LOW_U32(initrd_mem);
#if defined(__x86_64__)
  params->ext_ramdisk_size = HIGH_U32(size);
  params->ext_ramdisk_image = HIGH_U32(initrd_mem);
#endif

  ptr = initrd_mem;

  for (i = 0; i < nfiles; i++)
    {
      grub_ssize_t cursize = grub_file_size (files[i]);
      if (read (files[i], ptr, cursize) != cursize)
        {
          if (!grub_errno)
            grub_error (GRUB_ERR_FILE_READ_ERROR, N_("premature end of file %s"),
                        argv[i]);
          goto fail;
        }
      ptr += cursize;
      grub_memset (ptr, 0, ALIGN_UP_OVERHEAD (cursize, 4));
      ptr += ALIGN_UP_OVERHEAD (cursize, 4);
    }

  kernel_free(context->initrd_mem, params->ramdisk_size);

  context->initrd_mem = initrd_mem;
  params->ramdisk_size = size;

 fail:
  for (i = 0; i < nfiles; i++)
    grub_file_close (files[i]);
  grub_free (files);

  if (initrd_mem && grub_errno)
    kernel_free (initrd_mem, size);

  return grub_errno;
}

#define MIN(a, b) \
  ({ typeof (a) _a = (a);  \
    typeof (b) _b = (b); \
     _a < _b ? _a : _b; })

static grub_err_t
grub_cmd_linux (grub_command_t cmd __attribute__ ((unused)),
                int argc, char *argv[])
{
  grub_file_t file = 0;
  struct linux_i386_kernel_header *lh = NULL;
  grub_ssize_t start, filelen;
  void *kernel = NULL;
  int setup_header_end_offset;
  void *kernel_mem = 0;
  grub_uint64_t kernel_size = 0;
  grub_uint32_t handover_offset;
  struct linux_kernel_params *params = 0;
  char *cmdline = 0;
  int nx_supported = 1;
  struct grub_linuxefi_context *context = 0;
  grub_err_t err;

  grub_dl_ref (my_mod);

  if (argc == 0)
    {
      grub_error (GRUB_ERR_BAD_ARGUMENT, N_("filename expected"));
      goto fail;
    }

  file = grub_file_open (argv[0], GRUB_FILE_TYPE_LINUX_KERNEL);
  if (! file)
    goto fail;

  filelen = grub_file_size (file);

  kernel = grub_malloc(filelen);

  if (!kernel)
    {
      grub_error (GRUB_ERR_OUT_OF_MEMORY, N_("cannot allocate kernel buffer"));
      goto fail;
    }

  if (grub_file_read (file, kernel, filelen) != filelen)
    {
      grub_error (GRUB_ERR_FILE_READ_ERROR, N_("Can't read kernel %s"),
                  argv[0]);
      goto fail;
    }

  err = grub_efi_check_nx_image_support ((grub_addr_t)kernel, filelen,
					 &nx_supported);
  if (err != GRUB_ERR_NONE)
    return err;
  grub_dprintf ("linux", "nx is%s supported by this kernel\n",
		nx_supported ? "" : " not");

  lh = (struct linux_i386_kernel_header *)kernel;
  grub_dprintf ("linux", "original lh is at %p\n", kernel);

  grub_dprintf ("linux", "checking lh->boot_flag\n");
  if (lh->boot_flag != grub_cpu_to_le16 (0xaa55))
    {
      grub_error (GRUB_ERR_BAD_OS, N_("invalid magic number"));
      goto fail;
    }

  grub_dprintf ("linux", "checking lh->setup_sects\n");
  if (lh->setup_sects > GRUB_LINUX_MAX_SETUP_SECTS)
    {
      grub_error (GRUB_ERR_BAD_OS, N_("too many setup sectors"));
      goto fail;
    }

  grub_dprintf ("linux", "checking lh->version\n");
  if (lh->version < grub_cpu_to_le16 (0x020b))
    {
      grub_error (GRUB_ERR_BAD_OS, N_("kernel too old"));
      goto fail;
    }

  grub_dprintf ("linux", "checking lh->handover_offset\n");
  if (!lh->handover_offset)
    {
      grub_error (GRUB_ERR_BAD_OS, N_("kernel doesn't support EFI handover"));
      goto fail;
    }

#if defined(__x86_64__)
  grub_dprintf ("linux", "checking lh->xloadflags\n");
  if (!(lh->xloadflags & LINUX_XLF_KERNEL_64))
    {
      grub_error (GRUB_ERR_BAD_OS, N_("kernel doesn't support 64-bit CPUs"));
      goto fail;
    }
#endif

#if defined(__i386__)
  if ((lh->xloadflags & LINUX_XLF_KERNEL_64) &&
      !(lh->xloadflags & LINUX_XLF_EFI_HANDOVER_32))
    {
      grub_error (GRUB_ERR_BAD_OS,
                  N_("kernel doesn't support 32-bit handover"));
      goto fail;
    }
#endif
#if defined(__x86_64__)
  if (lh->xloadflags & LINUX_XLF_CAN_BE_LOADED_ABOVE_4G)
    {
      grub_dprintf ("linux", "Loading kernel above 4GB is supported; enabling.\n");
      max_addresses[KERNEL_NO_LIMIT].addr = GRUB_EFI_MAX_USABLE_ADDRESS;
    }
  else
    {
      grub_dprintf ("linux", "Loading kernel above 4GB is not supported\n");
    }
#endif

  params = kernel_alloc (sizeof(*params), GRUB_EFI_RUNTIME_SERVICES_DATA,
			 "cannot allocate kernel parameters");
  if (!params)
      goto fail;
  grub_dprintf ("linux", "params = %p\n", params);

  grub_memset (params, 0, sizeof(*params));

  setup_header_end_offset = *((grub_uint8_t *)kernel + 0x201);
  grub_dprintf ("linux", "copying %lu bytes from %p to %p\n",
               (unsigned long)
                MIN((grub_size_t)0x202+setup_header_end_offset,
                    sizeof (*params)) - 0x1f1,
                (grub_uint8_t *)kernel + 0x1f1,
                (grub_uint8_t *)params + 0x1f1);
  grub_memcpy ((grub_uint8_t *)params + 0x1f1,
               (grub_uint8_t *)kernel + 0x1f1,
                MIN((grub_size_t)0x202+setup_header_end_offset,sizeof (*params)) - 0x1f1);

  lh = (struct linux_i386_kernel_header *)params;
  grub_dprintf ("linux", "new lh is at %p\n", lh);

  grub_dprintf ("linux", "setting up cmdline\n");
  cmdline = kernel_alloc (lh->cmdline_size + 1,
			  GRUB_EFI_RUNTIME_SERVICES_DATA,
			  N_("can't allocate cmdline"));
  if (!cmdline)
      goto fail;
  grub_dprintf ("linux", "cmdline = %p\n", cmdline);

  grub_memcpy (cmdline, LINUX_IMAGE, sizeof (LINUX_IMAGE));
  grub_create_loader_cmdline (argc, argv,
                              cmdline + sizeof (LINUX_IMAGE) - 1,
                              lh->cmdline_size - (sizeof (LINUX_IMAGE) - 1),
                              GRUB_VERIFY_KERNEL_CMDLINE);

  grub_dprintf ("linux", "cmdline:%s\n", cmdline);
  grub_dprintf ("linux", "setting lh->cmd_line_ptr to 0x%08x\n",
		LOW_U32(cmdline));
  lh->cmd_line_ptr = LOW_U32(cmdline);
#if defined(__x86_64__)
  if ((grub_efi_uintn_t)cmdline > 0xffffffffull)
    {
      grub_dprintf ("linux", "setting params->ext_cmd_line_ptr to 0x%08x\n",
		    HIGH_U32(cmdline));
      params->ext_cmd_line_ptr = HIGH_U32(cmdline);
    }
#endif

  handover_offset = lh->handover_offset;
  grub_dprintf("linux", "handover_offset: 0x%08x\n", handover_offset);

  start = (lh->setup_sects + 1) * 512;

  /*
   * AFAICS >4GB for kernel *cannot* work because of params->code32_start being
   * 32-bit and getting called unconditionally in head_64.S from either entry
   * point.
   *
   * so nerf that out here...
   */
  save_addresses();
  grub_dprintf ("linux", "lh->pref_address: %p\n", (void *)(grub_addr_t)lh->pref_address);
  if (lh->pref_address < (grub_uint64_t)GRUB_EFI_MAX_ALLOCATION_ADDRESS)
    {
      max_addresses[KERNEL_PREF_ADDRESS].addr = lh->pref_address;
      max_addresses[KERNEL_PREF_ADDRESS].alloc_type = GRUB_EFI_ALLOCATE_ADDRESS;
    }
  max_addresses[KERNEL_4G_LIMIT].addr = GRUB_EFI_MAX_ALLOCATION_ADDRESS;
  max_addresses[KERNEL_NO_LIMIT].addr = GRUB_EFI_MAX_ALLOCATION_ADDRESS;
  kernel_size = lh->init_size;
  kernel_mem = kernel_alloc (kernel_size, GRUB_EFI_RUNTIME_SERVICES_CODE,
			     N_("can't allocate kernel"));

  restore_addresses();
  if (!kernel_mem)
    goto fail;

  grub_dprintf("linux", "kernel_mem = %p\n", kernel_mem);


  grub_dprintf ("linux", "setting lh->code32_start to 0x%08x\n",
                LOW_U32(kernel_mem));
  lh->code32_start = LOW_U32(kernel_mem);

  grub_memcpy (kernel_mem, (char *)kernel + start, filelen - start);

  params->type_of_loader = 0x21;
  lh->type_of_loader = 0x6;
  grub_dprintf ("linux", "setting lh->type_of_loader = 0x%02x\n",
                lh->type_of_loader);

  params->ext_loader_type = 0;
  params->ext_loader_ver = 2;
  grub_dprintf ("linux",
                "setting lh->ext_loader_{type,ver} = {0x%02x,0x%02x}\n",
                params->ext_loader_type, params->ext_loader_ver);

  context = grub_zalloc (sizeof (*context));
  if (!context)
    goto fail;
  context->kernel_mem = kernel_mem;
  context->kernel_size = kernel_size;
  context->handover_offset = handover_offset;
  context->params = params;
  context->cmdline = cmdline;
  context->nx_supported = nx_supported;

  grub_loader_set_ex (grub_linuxefi_boot, grub_linuxefi_unload, context, 0);

  cmd_initrd->data = context;
  cmd_initrdefi->data = context;

  grub_file_close (file);
  grub_free (kernel);
  return 0;

fail:
  if (file)
    grub_file_close (file);

  grub_dl_unref (my_mod);
  if (lh)
    kernel_free (cmdline, lh->cmdline_size + 1);

  kernel_free (kernel_mem, kernel_size);
  kernel_free (params, sizeof(*params));

  grub_free (context);
  grub_free (kernel);

  return grub_errno;
}

static grub_command_t cmd_linux, cmd_initrd;
static grub_command_t cmd_linuxefi, cmd_initrdefi;

GRUB_MOD_INIT(linux)
{
  cmd_linux =
    grub_register_command ("linux", grub_cmd_linux,
                           0, N_("Load Linux."));
  cmd_linuxefi =
    grub_register_command ("linuxefi", grub_cmd_linux,
                           0, N_("Load Linux."));
  cmd_initrd =
    grub_register_command ("initrd", grub_cmd_initrd,
                           0, N_("Load initrd."));
  cmd_initrdefi =
    grub_register_command ("initrdefi", grub_cmd_initrd,
                           0, N_("Load initrd."));
  my_mod = mod;
}

GRUB_MOD_FINI(linux)
{
  grub_unregister_command (cmd_linux);
  grub_unregister_command (cmd_linuxefi);
  grub_unregister_command (cmd_initrd);
  grub_unregister_command (cmd_initrdefi);
}
