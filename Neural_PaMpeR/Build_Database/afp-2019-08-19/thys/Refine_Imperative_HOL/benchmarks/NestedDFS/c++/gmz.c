class gmz : public dfs {

enum { white, blue, red, black };

uchar* colour;
bool* onstack;

stack cp;
counter tc, nc;

void black_dfs (node s)
{
	node t;

//	blk.inc();
	colour[s] = black;
	FOR_POST(s,t,tc)
		if (colour[t] != black) black_dfs(t);
}

void red_dfs (node s)
{
	node t;

	onstack[s] = true;
	colour[s] = red;
	cp.push(s);
	FOR_POST(s,t,tc)
	{
		if (onstack[t] && (ACCEPTING(t) || colour[t] == blue))
			{ cp.push(t); throw cycle_found(&cp); }
		else if (colour[t] == blue) red_dfs(t);
	}
	onstack[s] = false;
	cp.pop();
}

void blue_dfs (node s)
{
	node t;
	nc.inc();

	onstack[s] = true;
	colour[s] = blue;
	cp.push(s);
	FOR_POST(s,t,tc)
		if (onstack[t] && ACCEPTING(t))
			{ cp.push(t); throw cycle_found(&cp); }
		else if (colour[t] == white) blue_dfs(t);
	onstack[s] = false;
	cp.pop();

	bool sblk = true;
	FOR_POST(s,t,tc) if (colour[t] != black) sblk = false;
	if (sblk) { colour[s] = black; }
	else if (ACCEPTING(s))
	{
		red_dfs(s);
		black_dfs(s);
	}
}

public:

gmz () :
	dfs("Colour-DFS algorithm [GMZ04]"),
	nc("Distinct nodes visited"),
	tc("Transitions explored"),
	cp("Maximal stack depth")
{
	try {
		colour = (uchar*)calloc(1,G_nodes * sizeof(uchar));
		onstack = (bool*)calloc(1,G_nodes * sizeof(bool));
		blue_dfs(INITIAL_STATE);
		throw no_cycle();
	}
	catch (cycle_found) { }
	catch (no_cycle) { }

	free(colour);
	free(onstack);
}

};
