class couvreur : public dfs {

int count;
int* dfsnum;
bool* removed;
bool* incp;
stack roots;
stack cp;

counter tc, nc;

void find_counterexample (node s, int acc)
{
	node t;
	cp.push(s);
	removed[s] = true;
	if (incp[s] && dfsnum[s] <= acc) throw cycle_found(&cp);
	FOR_POST(s,t,tc)
                if (!removed[t] && dfsnum[t] <= acc) find_counterexample(t,acc);
	cp.pop();
}

void remove (node s)
{
	node t;
	if (removed[s]) return;
	removed[s] = true;
	FOR_POST(s,t,tc) remove(t);
}

void couvreur_dfs (node s)
{
	node t;
	nc.inc();

	dfsnum[s] = ++count;
	roots.push(s);
	cp.push(s);
	incp[s] = true;
	
	FOR_POST(s,t,tc)
	{
		if (dfsnum[t] == 0) couvreur_dfs(t);
		else if (!removed[t])
		{
			node u;
			do {
				u = roots.pop();
				if (ACCEPTING(u))
					find_counterexample(t,dfsnum[u]);
			} while (dfsnum[u] > dfsnum[t]);
			roots.push(u);
		}
	}

	cp.pop();
	incp[s] = false;
	if (roots.top() == s)
	{
		roots.pop();
		remove(s);
	}
}

public:

couvreur () :
	dfs("Couvreur's algorithm [Cou99]"),
	nc("Distinct nodes visited"),
	tc("Transitions explored"),
	cp("Maximal depth of call stack"),
	roots("Maximal size of roots stack")
{
	try {
		count = 0;
		dfsnum = (int*)calloc(1,G_nodes * sizeof(int));
		removed = (bool*)calloc(1,G_nodes * sizeof(bool));
		incp = (bool*)calloc(1,G_nodes * sizeof(bool));
		couvreur_dfs(INITIAL_STATE);
		throw no_cycle();
	}
	catch (cycle_found) { }
	catch (no_cycle) { }

	free(dfsnum);
	free(removed);
	free(incp);
}

};
