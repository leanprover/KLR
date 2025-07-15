
extern "C" {
#include "stdc.h"
//#include "region.h"
#include "cbor.h"
#include "ast_klir.h"

//#include <stdio.h>
//#include "serde_klir.h"
}


int main() {
  struct Core_Kernel* k = NULL;
  /*
  struct region *region = region_create();

  FILE *in = fopen("test.klr", "r");
  if (!in) {
    perror("fopen");
    return 1;
  }

  if (!Core_Kernel_des(in, region, &k)) {
    printf("Deserialization failed\n");
    return 1;
  }

  fclose(in);

  printf("got a kernel %p\n", k);
  region_destroy(region);
  */
  return 0;

}
