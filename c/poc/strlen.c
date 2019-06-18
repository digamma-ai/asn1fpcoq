#include <stddef.h>

size_t strlen(const unsigned char *s)
{
  size_t i = 0;

  while(*s++)
      i++;

  return i;
}
