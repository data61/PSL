class hpy : public dfs {

bool* blue;
bool* red;
bool* onstack;

stack cp;
counter tc, nc;

void red_dfs (node s)
{
	node t;

	red[s] = true;
	cp.push(s);
	FOR_POST(s,t,tc)
	{
		// Correction of HPY96 (order of conditions swapped)
		if (onstack[t]) { cp.push(t); throw cycle_found(&cp); }
		else if (!red[t]) red_dfs(t);
	}
	cp.pop();
}

void blue_dfs (node s)
{
	node t;
	nc.inc();

	blue[s] = true;
	onstack[s] = true;
	cp.push(s);
	FOR_POST(s,t,tc)
		if (!blue[t]) blue_dfs(t);
	cp.pop();
	if (ACCEPTING(s)) red_dfs(s);
	onstack[s] = false;
}

public:

hpy () :
	dfs("Nested-DFS improvement [HPY96]"),
	nc("Distinct nodes visited"),
	tc("Transitions explored"),
	cp("Maximal stack depth")
{
	try {
		blue = (bool*)calloc(1,G_nodes * sizeof(bool));
		red = (bool*)calloc(1,G_nodes * sizeof(bool));
		onstack = (bool*)calloc(1,G_nodes * sizeof(bool));
		blue_dfs(INITIAL_STATE);
		throw no_cycle();
	}
	catch (cycle_found) { }
	catch (no_cycle) { }

	free(blue);
	free(red);
	free(onstack);
}

};
