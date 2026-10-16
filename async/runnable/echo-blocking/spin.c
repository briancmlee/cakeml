/* Calibration for cpu_bench.py: a busy-polling loop (non-blocking polls,
   like a polling event loop with nothing to do).  Its CPU% is what busy
   polling costs in the current environment.  (In a background-QoS session
   on macOS this is well below 100%, while a pure arithmetic loop still
   gets ~99%: the kernel throttles the poll calls, not the process.) */
#include <poll.h>
int main(void) { for (;;) poll(0, 0, 0); }
