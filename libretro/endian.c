/******************************************************
 * Ngaro
 ******************************************************/

#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>

#include "functions.h"
#include "vm.h"

void retro_internal_swapEndian(VM *vm)
{
  int x, a;
  int b1, b2, b3, b4;

  for(a = 0; a < IMAGE_SIZE; a++)
  {
    x = vm->image[a];
    b1 = (x >>  0) & 0xff;
    b2 = (x >>  8) & 0xff;
    b3 = (x >> 16) & 0xff;
    b4 = (x >> 24) & 0xff;
    vm->image[a] = b1 << 24 | b2 << 16 | b3 << 8 | b4 << 0;
  }
}
