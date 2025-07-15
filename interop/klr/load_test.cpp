/*
A simple example of using the C++ deserialization API.
This file can be compiled and run with:

# gcc -std=c17 -Wall -c region.c cbor.c
# g++ --std=c++17 -Wall load_test.cpp klir_serde.cpp klir_common.cpp cbor.o region.o
# ./a.out test.klr
*/

#include <iostream>
#include "klir_ast.hpp"
#include "klir_serde.hpp"

using namespace std;
using namespace klr;

int main() {
  FILE *in = fopen("test.klr", "r");
  if (!in) {
    perror("fopen");
    return 1;
  }

  Ptr<KLRFile> file = KLRFile_des(in);
  if (file->major != 0 || file->minor != 0 || file->patch != 12)
    throw runtime_error("Wrong KLR version");

  cout << "KLR file header, version: " <<
    file->major << "." <<
    file->minor << "." <<
    file->patch << endl;

  Ptr<KLRMetaData> data = KLRMetaData_des(in);
  cout << "KLR meta data : " <<
    data->format << endl;

  Ptr<Contents> contents = Contents_des(in);
  cout << "KLR content type : " <<
    static_cast<unsigned>(contents->tag) << endl;

  if (contents->tag != Contents::Tag::klir)
    throw runtime_error("Wrong KLIR content type");

  ContentsKlirWrapper *w = static_cast<ContentsKlirWrapper*>(contents.get());
  Ptr<Kernel> k = w->kernel;
  cout << "KLR Kernel : " << k << endl;

  fclose(in);

  return 0;
}
