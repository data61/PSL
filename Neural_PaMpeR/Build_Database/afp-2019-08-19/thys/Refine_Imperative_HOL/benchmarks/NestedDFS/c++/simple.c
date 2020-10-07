class simple : public dfs {

bool* blue;
bool* red;

void red_dfs (node seed, node s)
{
	node t;

	red[s] = true;
	FOR_SUCCESSORS(s,t)
	{
		if (!red[t]) red_dfs(seed,t);
		else if (t==seed) { throw cycle_found(); };
	}
}

void blue_dfs (node s)
{
	node t;

	blue[s] = true;
	FOR_SUCCESSORS(s,t)
		if (!blue[t]) blue_dfs(t);

  if (ACCEPTING(s)) red_dfs(s,s);
}

public:

simple () :
	dfs("Nested-DFS (simple)")
{
	try {
		blue = (bool*)calloc(1,G_nodes * sizeof(bool));
		red = (bool*)calloc(1,G_nodes * sizeof(bool));
		blue_dfs(INITIAL_STATE);
		throw no_cycle();
	}
	catch (cycle_found) { }
	catch (no_cycle) { }

	free(blue);
	free(red);
}

};
