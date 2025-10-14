/*
 *  GRUB  --  GRand Unified Bootloader
 *  Copyright (C) 2017  Free Software Foundation, Inc.
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
 *
 *  Verifiers helper.
 */

#include <grub/file.h>
#include <grub/verify.h>
#include <grub/dl.h>
#if defined (GRUB_MACHINE_EFI) && defined (__x86_64__)
#include <grub/cpu/efi/memory.h> /* GRUB_EFI_MAX_ALLOCATION_ADDRESS */
#include <grub/efi/memory.h> /* GRUB_EFI_PAGE_SIZE */
#include <grub/efi/efi.h> /* grub_efi_allocate_pages_real grub_efi_free_pages */
#include <grub/efi/api.h> /* GRUB_EFI_ALLOCATE_MAX_ADDRESS GRUB_EFI_LOADER_CODE */
#include <grub/mm.h> /* grub_update_mem_attrs GRUB_MEM_ATTR_R|W|X */
#endif

GRUB_MOD_LICENSE ("GPLv3+");

struct grub_file_verifier *grub_file_verifiers;

struct grub_verified
{
  grub_file_t file;
  void *buf;
  grub_off_t size;
};
typedef struct grub_verified *grub_verified_t;

#if defined (GRUB_MACHINE_EFI) && defined (__x86_64__)
static void *efi_buff_malloc (grub_efi_uintn_t size);
static void  verified_efi_free (grub_verified_t verified);
#define verified_free(verified) verified_efi_free (verified)
#else
static void
verified_free (grub_verified_t verified)
{
  if (verified)
    {
      grub_free (verified->buf);
      grub_free (verified);
    }
}
#endif

static grub_ssize_t
verified_read (struct grub_file *file, char *buf, grub_size_t len)
{
  grub_verified_t verified = file->data;

  grub_memcpy (buf, (char *) verified->buf + file->offset, len);
  return len;
}

static grub_err_t
verified_close (struct grub_file *file)
{
  grub_verified_t verified = file->data;

  grub_file_close (verified->file);
  verified_free (verified);
  file->data = 0;

  /* Device and name are freed by parent. */
  file->device = 0;
  file->name = 0;

  return grub_errno;
}

struct grub_fs verified_fs =
{
  .name = "verified_read",
  .fs_read = verified_read,
  .fs_close = verified_close
};

static grub_file_t
grub_verifiers_open (grub_file_t io, enum grub_file_type type)
{
  grub_verified_t verified = NULL;
  struct grub_file_verifier *ver;
  void *context;
  grub_file_t ret = 0;
  grub_err_t err;
  int defer = 0;

  grub_dprintf ("verify", "file: %s type: %d\n", io->name, type);

  if ((type & GRUB_FILE_TYPE_MASK) == GRUB_FILE_TYPE_SIGNATURE
      || (type & GRUB_FILE_TYPE_MASK) == GRUB_FILE_TYPE_VERIFY_SIGNATURE
      || (type & GRUB_FILE_TYPE_SKIP_SIGNATURE))
    return io;

  if (io->device->disk &&
      (io->device->disk->dev->id == GRUB_DISK_DEVICE_MEMDISK_ID
       || io->device->disk->dev->id == GRUB_DISK_DEVICE_PROCFS_ID))
    return io;

  FOR_LIST_ELEMENTS(ver, grub_file_verifiers)
    {
      enum grub_verify_flags flags = 0;
      err = ver->init (io, type, &context, &flags);
      if (err)
	goto fail_noclose;
      if (flags & GRUB_VERIFY_FLAGS_DEFER_AUTH)
	{
	  defer = 1;
	  continue;
	}
      if (!(flags & GRUB_VERIFY_FLAGS_SKIP_VERIFICATION))
	break;
    }

  if (!ver)
    {
      if (defer)
	{
	  grub_error (GRUB_ERR_ACCESS_DENIED,
		      N_("verification requested but nobody cares: %s"), io->name);
	  goto fail_noclose;
	}

      /* No verifiers wanted to verify. Just return underlying file. */
      return io;
    }

  ret = grub_malloc (sizeof (*ret));
  if (!ret)
    {
      goto fail;
    }
  *ret = *io;

  ret->fs = &verified_fs;
  ret->not_easily_seekable = 0;
  if (ret->size >> (sizeof (grub_size_t) * GRUB_CHAR_BIT - 1))
    {
      grub_error (GRUB_ERR_NOT_IMPLEMENTED_YET,
		  N_("big file signature isn't implemented yet"));
      goto fail;
    }
  verified = grub_malloc (sizeof (*verified));
  if (!verified)
    {
      goto fail;
    }
  /* Just for the buffer allocation, we request EFI memory avoiding
     possible OOM */
#if defined (GRUB_MACHINE_EFI) && defined (__x86_64__)
  verified->size = ret->size;
  verified->buf = efi_buff_malloc (ret->size);
#else
  verified->buf = grub_malloc (ret->size);
#endif

  if (!verified->buf)
    {
      goto fail;
    }
  if (grub_file_read (io, verified->buf, ret->size) != (grub_ssize_t) ret->size)
    {
      if (!grub_errno)
	grub_error (GRUB_ERR_FILE_READ_ERROR, N_("premature end of file %s"),
		    io->name);
      goto fail;
    }

  err = ver->write (context, verified->buf, ret->size);
  if (err)
    goto fail;

  err = ver->fini ? ver->fini (context) : GRUB_ERR_NONE;
  if (err)
    goto fail;

  if (ver->close)
    ver->close (context);

  FOR_LIST_ELEMENTS_NEXT(ver, grub_file_verifiers)
    {
      enum grub_verify_flags flags = 0;
      err = ver->init (io, type, &context, &flags);
      if (err)
	goto fail_noclose;
      if (flags & GRUB_VERIFY_FLAGS_SKIP_VERIFICATION ||
	  /* Verification done earlier. So, we are happy here. */
	  flags & GRUB_VERIFY_FLAGS_DEFER_AUTH)
	continue;
      err = ver->write (context, verified->buf, ret->size);
      if (err)
	goto fail;

      err = ver->fini ? ver->fini (context) : GRUB_ERR_NONE;
      if (err)
	goto fail;

      if (ver->close)
	ver->close (context);
    }

  verified->file = io;
  ret->data = verified;
  return ret;

 fail:
  if (ver->close)
    ver->close (context);
 fail_noclose:
  verified_free (verified);
  grub_free (ret);
  return NULL;
}

grub_err_t
grub_verify_string (char *str, enum grub_verify_string_type type)
{
  struct grub_file_verifier *ver;

  grub_dprintf ("verify", "string: %s, type: %d\n", str, type);

  FOR_LIST_ELEMENTS(ver, grub_file_verifiers)
    {
      grub_err_t err;
      err = ver->verify_string ? ver->verify_string (str, type) : GRUB_ERR_NONE;
      if (err)
	return err;
    }
  return GRUB_ERR_NONE;
}

void
grub_verifiers_init (void)
{
  grub_file_filter_register (GRUB_FILE_FILTER_VERIFY, grub_verifiers_open);
}

#if defined (GRUB_MACHINE_EFI) && defined (__x86_64__)

#define BYTES_TO_PAGES(bytes)   (((bytes) + 0xfff) >> 12)

static void *
efi_buff_malloc (grub_efi_uintn_t size)
{
  void *addr = 0;
  grub_uint64_t max;
  grub_efi_uintn_t pages;
  grub_efi_memory_type_t memtype;

  pages = BYTES_TO_PAGES(size);
  grub_dprintf ("verify", "Trying to allocate %lu pages (%lu bytes) from %p\n",
		(unsigned long)pages, (unsigned long)size,
		(void *)(unsigned long)GRUB_EFI_MAX_ALLOCATION_ADDRESS);

  size = pages * GRUB_EFI_PAGE_SIZE;

  addr = grub_efi_allocate_pages_real (GRUB_EFI_MAX_ALLOCATION_ADDRESS,
				       pages,
				       GRUB_EFI_ALLOCATE_MAX_ADDRESS,
				       GRUB_EFI_LOADER_CODE);
  if (addr)
      grub_update_mem_attrs ((grub_addr_t)addr, size,
			     GRUB_MEM_ATTR_R|GRUB_MEM_ATTR_W,
			     GRUB_MEM_ATTR_X);

  while (grub_error_pop ());

  if (addr == NULL)
    grub_error (GRUB_ERR_OUT_OF_MEMORY, "%s", N_("can't allocate kernel"));

  grub_dprintf ("verify", "Allocated %lu pages (%lu bytes) at %p\n",
		(unsigned long)pages, (unsigned long)size, addr);

  return addr;
}

static void
verified_efi_free (grub_verified_t verified)
{
  void *addr;
  grub_off_t size;

  if (verified)
    {
      addr = verified->buf;
      size = verified->size;
      if (addr && size)
	{
	  grub_dprintf ("verify", "Trying to free addr %p size %lu pages %lu\n",
			(grub_addr_t)addr, (unsigned long)size,
			(unsigned long)BYTES_TO_PAGES(size));
	  grub_efi_free_pages ((grub_efi_physical_address_t)(grub_addr_t)addr,
			       BYTES_TO_PAGES(size));
	}
      grub_free (verified);
    }
}
#endif
