int a, b, c;
int t;

if (a>b) {
  t = a;
  a = b;
  b = t;
}
if (b>c) {
  t = b;
  b = c;
  c = t;
}
if (a>b) {
  t = a;
  a = b;
  b = t;
}

assert (a<b) && (b<c);	/* Is there a better way to specify this? */
