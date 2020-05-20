class tjs : public dfs {

int count;
int* dfsnum;
node* lownode;
bool* onstack;
bool* visited;
stack cp;

counter tc, nc;


void tjs_dfs (node v, int acc_idx)
{
  cp.push(v);
  nc.inc();
  
  dfsnum[v]=count;
  onstack[v]=visited[v]=true;
  lownode[v]=v;

  if (ACCEPTING(v)) acc_idx=count;
  count++;

  node w;
  FOR_POST(v,w,tc) {
    if (visited[w]) {
      if (onstack[lownode[w]]) {
        if (dfsnum[lownode[w]] <= acc_idx)
          throw cycle_found();
        else if (dfsnum[lownode[w]] < dfsnum[lownode[v]])
          lownode[v] = lownode[w];

      }

    } else {
      tjs_dfs(w,acc_idx);
      if (onstack[lownode[w]] && dfsnum[lownode[w]] < dfsnum[lownode[v]])
        lownode[v] = lownode[w];
    };
  }

  onstack[v]=false;
  cp.pop();
}

public:

tjs () :
	dfs("Tarjan simplified"),
	nc("Distinct nodes visited"),
	tc("Transitions explored"),
	cp("Maximal depth of call stack")
{
	try {
		count = 0;
		dfsnum = (int*)calloc(1,G_nodes * sizeof(int));
    lownode = (node*)calloc(1,G_nodes * sizeof(node));
    onstack = (bool*)calloc(1,G_nodes * sizeof(bool));
    visited = (bool*)calloc(1,G_nodes * sizeof(bool));
    
		tjs_dfs(INITIAL_STATE,-1);
		throw no_cycle();
	}
	catch (cycle_found) { }
	catch (no_cycle) { }

	free(dfsnum);
  free(lownode);
  free(onstack);
  free(visited);
}

};
