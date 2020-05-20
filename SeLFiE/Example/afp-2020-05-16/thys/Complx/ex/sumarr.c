/*
 * Copyright 2016, DATA61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */
#if defined(GCC)
# include <pthread.h>
# include <string.h>
# include <stdio.h>
# include <stdlib.h>
#else
# define NULL ((void *)0)
# define fprintf(...) NULL
typedef struct { int l; } pthread_mutex_t;
void lock(void);
void unlock(void);
#endif

#define NTHREADS 2
#define NSUM 10
#define MAXSUM 1500

int error(int e, char *str)
{
  fprintf(stderr, "%s\n", str);
  return e;
}

struct thread_info {    /* Used as argument to thread_start() */
        unsigned int id;
        unsigned int *arr;
};
unsigned int gsum;

pthread_mutex_t glock;

#if defined(GCC)
static void lock(void)
{
        /* AWAIT(glock == 0) { glock = 1; } */
        pthread_mutex_lock(&glock);
}

static void unlock(void)
{
        /* AWAIT (TRUE) { glock = 0; } */
        pthread_mutex_unlock(&glock);
}
#endif

unsigned int garr[NTHREADS][NSUM] = {
        {22, 33, 56, 66, 88, 423, 199, 199, 88, 847},
        {40, 32, 29, 829, 12, 94, 19, 67, 61, 72},
};

unsigned int gdone;

void sumarray(unsigned int *tarr, unsigned int tid)
{
    unsigned int ti;
    unsigned int tsum;

    tsum = 0;
    for (ti = 0; ti < NSUM; ti++) {
            tsum += tarr[ti];
            if (tsum >= MAXSUM || tarr[ti] >= MAXSUM) {
                tsum = MAXSUM;
                break;
            }
    }
    lock();
    gsum += tsum;
    gdone |= tid;
    unlock();
}

static void *thread_start(void *arg)
{
    struct thread_info *tinfo = arg;

    fprintf(stdout, "Thread %d, arr=%p\n",
            tinfo->id, tinfo->arr);

    sumarray(tinfo->arr, tinfo->id);
    return NULL;
}

#if defined(GCC)
int main(int ac, char **av)
{
	int s, i, opt;
	struct thread_info *tinfo;
	pthread_t threads[2];
	pthread_attr_t attr;
	void *res;

       /* Initialize thread creation attributes */
       s = pthread_attr_init(&attr);
       if (s != 0)
           return error(s, "pthread_attr_init");

       /* Allocate memory for pthread_create() arguments */

       tinfo = calloc(NTHREADS, sizeof(struct thread_info));
       if (tinfo == NULL)
           return error(1, "calloc");

       /* Initialise global lock */
        pthread_mutex_init(&glock, NULL);

       /* Initialise gdone */
       gdone = 0;

       /* Create one thread for each command-line argument */
       for (i = 0; i < NTHREADS; i++) {
           tinfo[i].id = i+1;
           tinfo[i].arr = garr[i];

           /* The pthread_create() call stores the thread ID into
              corresponding element of tinfo[] */

           s = pthread_create(&threads[i], &attr,
                              &thread_start, &tinfo[i]);
           if (s != 0)
               error(s, "pthread_create");
       }

       /* Destroy the thread attributes object, since it is no
          longer needed */

       s = pthread_attr_destroy(&attr);
       if (s != 0)
           error(s, "pthread_attr_destroy");

       /* Now join with each thread, and display its returned value */

       for (i = 0; i < NTHREADS; i++) {
           s = pthread_join(threads[i], &res);
           if (s != 0)
               error(s, "pthread_join");

           fprintf(stdout, "Joined with thread %d\n",
                   tinfo[i].id);
       }
        fprintf(stdout, "Global sum is %d, gdone=%x\n", gsum, gdone);

       free(tinfo);
       exit(EXIT_SUCCESS);
       return 0;
}
#endif 
