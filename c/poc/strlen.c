typedef unsigned int size_t;

size_t strlen(const unsigned char *s) {
  size_t i;
  unsigned char c;

  i = 0;
  c = s[i];
  while ('\0' != c) {
    i++;
    c = s[i];
    
  }

  return i;
}
