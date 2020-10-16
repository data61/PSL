#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <iostream>

#define STAT

typedef unsigned char uchar;
typedef unsigned int node;

struct edge {
	node target;
	edge *next;
	edge (node target, edge *next)
	{ 
		this->target = target;
		this->next = next;
	}
};

#ifdef STAT

struct stat {
	const char *msg;
	int val;
	bool silent;
	void set (int v) {
    val = v;
  }
	~stat () {
    if (!silent) printf("%s: %d\n",msg,val);
  }
};

class counter : public stat {
public:	counter (const char *s) {
  val = 0;
  msg = s; silent = (msg == NULL); }
	void inc () {
    val++;
  }
};

class maxcounter : public stat {
public:
  int current;

  maxcounter (const char *s) {
    val = current = 0;
    msg = s;
					silent = (msg == NULL); }
	void inc () {
    if (++current > val) val = current;
  }
	void dec () {
    current--;
  }
};

#else

struct stat {
  void set (int v) {}
};

class counter : public stat {
public: counter (const char *s) {}
  void inc () {  }
};

class maxcounter : public stat {
public:

  maxcounter (const char *s) {}
  void inc () {
  }
  void dec () {
  }
};


#endif


#define FOR_POST(s,t,c) \
  for (edge *_e = G_edges[s]; _e && (c.inc(), (t = _e->target)+1); _e = _e->next)
#define FOR_SUCCESSORS(s,t) \
  for (edge *_e = G_edges[s]; _e && (t = _e->target)+1; _e = _e->next)
#define FOR_SUCCESSORS_COUNT(s,t,c) \
  for (edge *_e = G_edges[s]; _e && (c.inc(), (t = _e->target)+1); _e = _e->next)
#define ACCEPTING(s) G_accepting[s]
#define INITIAL_STATE 0

int G_nodes;
uchar* G_accepting;
edge** G_edges;
bool printcp;


#ifdef STAT
class stack {
  edge *tos;
  maxcounter sd;
  void print_recur (edge *tmp) {
    if (!tmp) return;
    print_recur(tmp->next);
    if (ACCEPTING(tmp->target)) printf("{");
    printf("%d",tmp->target);
    if (ACCEPTING(tmp->target)) printf("}");
    printf(" ");
  }
  void clone_recur (edge *tmp, stack *ns) {
    if (!tmp) return;
    clone_recur(tmp->next,ns);
    (*ns).push(tmp->target);
  }

public: stack(char *s) : sd(s) { tos = NULL; }
  ~stack() { while (tos) { edge *tmp = tos->next; delete tos; tos = tmp;}}
  void push(node s) {
    sd.inc(); tos = new edge(s,tos);
  }
  node pop() {
    sd.dec(); node ret = tos->target; edge *tmp = tos->next;
      delete tos; tos = tmp; return ret;
  }
  node top() { return tos->target; }
  bool empty() { return tos == NULL; }
  int length() { return sd.current; }
  void print() { print_recur(tos); printf("\n"); }

  edge* topedge() { return tos; }

  stack* clone(char *s) {
    stack *ns = new stack(s);
    clone_recur(tos,ns);
    return ns;
  }
};
#else

class stack {
 
public: stack(char *s) { }
  void push(node s) {
  }
  void pop() {
  }
  void print() { }
};

#endif



struct dfs {
	dfs(char *title) { printf("%s\n",title);
		  for (int i=0; i < strlen(title); i++) printf("=");
		  printf("\n"); }
	~dfs()  { printf("\n"); }
};

struct cycle_found {
	cycle_found () { printf("Cycle found!\n"); }
	cycle_found (stack *c) { printf("Cycle found!\n");
#ifdef STAT
		printf("Length of counterexample: %d\n",c->length());
		if (printcp) c->print();
#endif
    
  }
};

struct no_cycle {
	no_cycle () { printf("No cycle found.\n"); }
};

#include "simple.c"
#include "hpy.c"
#include "hpy2.c"
#include "newdfs.c"
#include "gmz.c"
#include "tjs.c"

#ifdef STAT
#include "couvreur.c"
#include "gv.c"
#endif

void read_graph ()
{
	int m,n,tc = 0;
	edge* e;

	scanf("%d",&G_nodes);
	printf("Number of reachable nodes: %d\n",G_nodes);

	G_accepting = new uchar[G_nodes];
	G_edges = new edge*[G_nodes];

	for (;;)
	{
		scanf("%d",&m);
		if (m == -1) break;
		G_accepting[m] = 1;
	} 
	for (;;)
	{
		scanf("%d",&m);
		if (m == -1) break;
		scanf("%d",&n);
		G_edges[m] = new edge(n,G_edges[m]);
		tc++;
	}
	printf("Number of edges: %d\n\n",tc);
}

#define MEASURE(x) { \
        struct timeval stv, etv, rtv;  \
        gettimeofday(&stv, NULL); \
        x; \
        gettimeofday(&etv, NULL); \
        timersub(&etv, &stv, &rtv);\
        std::cout << "Time used: " << rtv.tv_sec << "s " << rtv.tv_usec << "us" << std::endl;\
        std::cout << "Time: " << rtv.tv_sec*1000 + rtv.tv_usec / 1000 << "ms" << std::endl;\
}

int main (int argc, char **argv)
{
	if (argc >= 2 && !strcmp(argv[1],"-c")) printcp = true;
	read_graph();
//   MEASURE (simple x);
 	MEASURE (hpy x);
//   MEASURE (hpy2 x);
// 	MEASURE (gmz x);
//  	MEASURE (newdfs x);
//   MEASURE (tjs x);
// #ifdef STAT
//   MEASURE (couvreur x);
// 	MEASURE (gv x);
// #endif
}
