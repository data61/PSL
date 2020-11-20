class newdfs : public dfs {

enum { white, cyan, blue, red };
uchar* colour;

stack cp;
counter tc, nc;

void second_dfs (node s)
{
	node t;

	cp.push(s);
	FOR_POST(s,t,tc)
	{
		if (colour[t] == cyan) { cp.push(t); throw cycle_found(&cp); }
		else if (colour[t] == blue) { colour[t] = red; second_dfs(t); }
	}
	cp.pop();
}

void first_dfs (node s)
{
	node t;
	nc.inc();

	colour[s] = cyan;
	cp.push(s);
	FOR_POST(s,t,tc)
		if (colour[t] == cyan && (ACCEPTING(s) || ACCEPTING(t)))
			{ cp.push(t); throw cycle_found(&cp); }
		else if (colour[t] == white) first_dfs(t);
	cp.pop();
	if (ACCEPTING(s)) { second_dfs(s); colour[s] = red; }
	else colour[s] = blue;
}

public:

newdfs () :
	dfs("New DFS algorithm"),
	nc("Distinct nodes visited"),
	tc("Transitions explored"),
	cp("Maximal stack depth")
{
	try {
		colour = (uchar*)calloc(1,G_nodes * sizeof(uchar));
		first_dfs(INITIAL_STATE);
		throw no_cycle();
	}
	catch (cycle_found) { }
	catch (no_cycle) { }

	free(colour);
}

};
