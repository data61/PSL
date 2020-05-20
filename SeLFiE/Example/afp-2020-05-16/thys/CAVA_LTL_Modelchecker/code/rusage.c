/*
 * Wrapper around getrusage for MLton.
 *
 * Returning the max RSS size can be seen as an equivalent for max heap size.
 */

#include <sys/time.h>
#include <sys/resource.h>

long get_max_rss () {
    struct rusage r;

    if (getrusage(RUSAGE_SELF, &r) == -1)
        return (long) 0;
    else
        return r.ru_maxrss;
}
