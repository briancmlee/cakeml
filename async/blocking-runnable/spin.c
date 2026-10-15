/* Calibration for cpu_bench.py: a pure busy loop (non-blocking polls, like
   a polling event loop with nothing to do).  Its CPU% is what "one core,
   fully busy" measures as in the current environment (a niced or
   background-throttled process gets less than 100%). */
#include <poll.h>
int main(void) { for (;;) poll(0, 0, 0); }
