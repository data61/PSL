class gv : public dfs {

int count;
int* dfsnum;
int* lowpt;
bool* onstack;
bool* incp;
stack current;

stack cp;
counter tc, nc;

void find_counterexample (node s, int acc)
{
	node t;
	cp.push(s);
	onstack[s] = false;
	if (incp[s] && dfsnum[s] <= acc) throw cycle_found(&cp);
	FOR_POST(s,t,tc)
		if (onstack[t] && lowpt[t] <= acc) find_counterexample(t,acc);
	cp.pop();
}

void gv_dfs (node s, int acc)
{
	node t;
	nc.inc();

	dfsnum[s] = lowpt[s] = ++count;
	current.push(s);
	cp.push(s);
	onstack[s] = true;
	incp[s] = true;
	
	FOR_POST(s,t,tc)
	{
		if (dfsnum[t] == 0) gv_dfs(t,ACCEPTING(t)? count+1 : acc);
		if (onstack[t])
		{
			if (lowpt[t] < lowpt[s]) lowpt[s] = lowpt[t];
			if (lowpt[s] <= acc) find_counterexample(t,acc);
		}
	}
	cp.pop();
	incp[s] = false;

	if (lowpt[s] == dfsnum[s])
	{
		do {
			t = current.pop();
			onstack[t] = false;
		} while (s != t);
	}
}

public:

gv () :
	dfs("Geldenhuys-Valmari algorithm [GV04]"),
	nc("Distinct nodes visited"),
	tc("Transitions explored"),
	cp("Maximal depth of call stack"),
	current("Maximal size of state stack")
{
	try {
		count = 0;
		dfsnum = (int*)calloc(1,G_nodes * sizeof(int));
		lowpt = (int*)calloc(1,G_nodes * sizeof(int));
		onstack = (bool*)calloc(1,G_nodes * sizeof(bool));
		incp = (bool*)calloc(1,G_nodes * sizeof(bool));
		gv_dfs(INITIAL_STATE,ACCEPTING(INITIAL_STATE)? 1 : 0);
		throw no_cycle();
	}
	catch (cycle_found) { }
	catch (no_cycle) { }

	free(dfsnum);
	free(lowpt);
	free(onstack);
	free(incp);
}

};
