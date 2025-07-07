/*
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Govereau, Sean McLaughlin
*/
#include "stdc.h"
#include "region.h"
#include "cbor.h"
#include "serde_python_core.h"
#include "serde_nki.h"
#include "serde_file.h"
#include "frontend.h"

#include <stdio.h>

typedef bool (*ser_fn)(FILE*, const void*);
typedef bool (*des_fn)(FILE*, struct region*, void**);

#define ERR(s) { res.err = s; goto error; }

static struct SerResult
write_file(const char *file, struct File_Contents *contents) {
  struct SerResult res = { .ok = false };

  // TODO copy these from Lean defaults
  // Not too relevant now since we haven't defined the meta-data yet
  struct Serde_KLRFile clsFile = {
    .major = 0,
    .minor = 0,
    .patch = 12,
  };
  struct Serde_KLRMetaData data = {
    .format = "KLR"
  };

  FILE *out = fopen(file, "wb");
  if (!out)
    ERR("could not open output file for writing");

  if (!Serde_KLRFile_ser(out, &clsFile))
    ERR("error writing file header");
  if (!Serde_KLRMetaData_ser(out, &data))
    ERR("error writing file meta-data");
  if (!File_Contents_ser(out, contents))
    ERR("error writing file contents");
  if (fclose(out))
    ERR("error closing KLR data file");

  struct File_Contents call = {
    .tag = File_Contents_hlo,
    .hlo = { .name = (char*)file }
  };
  char *buf = NULL;
  size_t size = 0;
  out = open_memstream(&buf, &size);
  if (!out)
    ERR("could not create call-site buffer");
  if (!Serde_KLRFile_ser(out, &clsFile))
    ERR("error writing call-site header");
  if (!Serde_KLRMetaData_ser(out, &data))
    ERR("error writing call-site meta-data");
  if (!File_Contents_ser(out, &call))
    ERR("error writing call-site contents");
  if (fclose(out))
    ERR("error finalizing call-site buffer");
  if (!buf || size <= 0) {
    if (buf) free(buf);
    ERR("error creating call-site buffer");
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
read_file(const u8 *buf, u64 size, enum File_Contents_Tag tag) {
  // TODO: current deserializers are unsafe, to be fixed in code generator
  (void)size;
  struct DesResult res = { .ok = false };
  struct Serde_KLRFile *file = NULL;
  struct Serde_KLRMetaData *data = NULL;
  struct File_Contents *contents = NULL;

  FILE *in = NULL;
  res.region = region_create();
  if (!res.region)
    ERR("could not create memory region");

  in = fmemopen((void*)buf, size, "r");
  if (!in)
    ERR("could not read call-site buffer");
  if (!Serde_KLRFile_des(in, res.region, &file))
    ERR("could not read call-site header");
  if (file->major != 0 || file->minor != 0 || file->patch != 12)
    ERR("KLR version mismatch");
  if (!Serde_KLRMetaData_des(in, res.region, &data))
    ERR("could not read call-site meta-data");
  if (!File_Contents_des(in, res.region, &contents))
    ERR("could not read call-site contents");
  if (contents->tag != File_Contents_hlo)
    ERR("invalid call-site contents");
  if (fclose(in))
    ERR("error completing call-site read");

  in = fopen(contents->hlo.name, "r");
  if (!in)
    ERR("could not read kernel file");
  if (!Serde_KLRFile_des(in, res.region, &file))
    ERR("could not read kernel header");
  if (file->major != 0 || file->minor != 0 || file->patch != 12)
    ERR("KLR version mismatch");
  if (!Serde_KLRMetaData_des(in, res.region, &data))
    ERR("could not read kernel meta-data");
  if (!File_Contents_des(in, res.region, &contents))
    ERR("could not read kernel contents");
  if (fclose(in))
    ERR("error completing kernel read");

  if (contents->tag != tag)
    ERR("invalid kernel contents");

  switch (tag) {
  case File_Contents_python:
    res.python = contents->python.kernel;
    break;
  case File_Contents_nki:
    res.nki = contents->nki.kernel;
    break;
  default:
    ERR("unsupported kernel contents");
  }

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

// This is a temporary hack for compatibility with Lean
// Proper fixes in next PR
#define Contents_python 0
#define Contents_nki 1

struct SerResult
serialize_python(const char *file, struct Python_Kernel *k) {
  struct File_Contents contents = {
    .tag = File_Contents_python,
    .python = { .kernel = k }
  };
  return write_file(file, &contents);
}

struct DesResult
deserialize_python(const u8 *buf, u64 size) {
  struct DesResult res = read_file(buf, size, File_Contents_python);
  res.isNki = false;
  return res;
}

struct SerResult
serialize_nki(const char *file, struct NKI_Kernel *k) {
  struct File_Contents contents = {
    .tag = File_Contents_nki,
    .nki = { .kernel = k }
  };
  return write_file(file, &contents);
}

struct DesResult
deserialize_nki(const u8 *buf, u64 size) {
  struct DesResult res = read_file(buf, size, File_Contents_nki);
  res.isNki = true;
  return res;
}
