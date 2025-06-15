/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#include "stdc.h"
#include "region.h"
#include "cbor.h"
#include "ast_common.h"
#include "ast_python_core.h"
#include "ast_nki.h"
#include "serde_common.h"
#include "serde_python_core.h"
#include "serde_nki.h"
#include "frontend.h"

#include <stdio.h>

typedef bool (*ser_fn)(FILE*, const void*);
typedef bool (*des_fn)(FILE*, struct region*, void**);

#define ERR(s) { res.err = s; goto error; }

static struct SerResult
write_file(
  const char *file,
  const char *format,
  ser_fn f,
  const void *value)
{
  struct SerResult res = { .ok = false };

  // TODO copy these from Lean defaults
  // Not too relevant now since we haven't defined the meta-data yet
  struct Serde_KLRFile clsFile = {
    .major = 0,
    .minor = 0,
    .patch = 10,
  };
  struct Serde_KLRMetaData data = {
    .format = (char*)format
  };

  FILE *out = fopen(file, "wb");
  if (!out)
    ERR("could not open output file for writing");

  if (fwrite(out, sizeof(clsFile), 1, out) != 1)
    ERR("error writing file header");
  if (fwrite(out, sizeof(data), 1, out) != 1)
    ERR("error writing file meta-data");
  if (!f(out, value))
    ERR("error writing file data");
  if (fclose(out))
    ERR("error closing KLR data file");

  data.format = "CALL";
  char *buf = NULL;
  size_t size = 0;
  out = open_memstream(&buf, &size);
  if (!out)
    ERR("could not create call-site buffer");
  if (fwrite(out, sizeof(clsFile), 1, out) != 1)
    ERR("error writing call-site header");
  if (fwrite(out, sizeof(data), 1, out) != 1)
    ERR("error writing call-site meta-data");
  if (!String_ser(out, format))
    ERR("Error writing call-site buffer");
  if (fclose(out))
    ERR("Error finalizing call-site buffer");
  if (!buf || size <= 0) {
    if (buf) free(buf);
    ERR("Error creating call-site buffer");
  }

  res.ok = true;
  res.err = NULL;
  res.bytes = (u8*)buf;
  res.size = size;
  return res;

error:
  if (out)
    fclose(out);
  res.ok = false;
  return res;
}

static struct DesResult
read_file(
  const u8 *buf,
  u64 size,
  const char *format,
  des_fn f)
{
  // TODO: current deserializers are unsafe, to be fixed in code generator
  (void)size;
  struct DesResult res = { .ok = false };
  struct Serde_KLRFile *file = NULL;
  struct Serde_KLRMetaData *data = NULL;

  FILE *in = NULL;
  res.region = region_create();
  if (!res.region)
    ERR("could not create memory region");

  in = fmemopen((void*)buf, size, "r");
  if (!in)
    ERR("could not read call-site buffer");
  if (!Serde_KLRFile_des(in, res.region, &file))
    ERR("could not read call-site header");
  if (file->major != 0 || file->minor != 0 || file->patch != 10)
    ERR("KLR version mismatch");
  if (!Serde_KLRMetaData_des(in, res.region, &data))
    ERR("could not read call-site meta-data");
  if (strcmp(data->format, "CALL"))
    ERR("Invalid call-site format");

  char *kernel_file = NULL;
  if (!String_des(in, res.region, &kernel_file))
    ERR("could not read call site archive file");
  if (fclose(in))
    ERR("error completing call-site read");

  in = fopen(kernel_file, "r");
  if (!in)
    ERR("could not read kernel file");
  if (!Serde_KLRFile_des(in, res.region, &file))
    ERR("could not read kernel header");
  if (file->major != 0 || file->minor != 0 || file->patch != 10)
    ERR("KLR version mismatch");
  if (!Serde_KLRMetaData_des(in, res.region, &data))
    ERR("could not read kernel meta-data");
  if (strcmp(data->format, format))
    ERR("Invalid call-site format");
  if (!f(in, res.region, (void**)&res.python))
    ERR("could not parse KLR file");

  res.ok = true;
  res.err = NULL;
  return res;

error:
  res.ok = false;
  if (res.region)
    region_destroy(res.region);
  if (in)
    fclose(in);
  res.region = NULL;
  return res;
}

struct SerResult
serialize_python(const char *file, const struct Python_Kernel *k) {
  return write_file(file, "Python", (ser_fn)Python_Kernel_ser, k);
}

struct DesResult
deserialize_python(const u8 *buf, u64 size) {
  struct DesResult res = read_file(buf, size, "Python", (des_fn)Python_Kernel_des);
  res.isNki = false;
  return res;
}

struct SerResult
serialize_nki(const char *file, const struct NKI_Kernel *k) {
  return write_file(file, "NKI", (ser_fn)NKI_Kernel_ser, k);
}

struct DesResult
deserialize_nki(const u8 *buf, u64 size) {
  struct DesResult res = read_file(buf, size, "NKI", (des_fn)Python_Kernel_des);
  res.isNki = true;
  return res;
}
