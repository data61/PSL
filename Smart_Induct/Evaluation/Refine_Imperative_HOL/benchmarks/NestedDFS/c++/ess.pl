#!/usr/bin/perl -w

usage() if ($#ARGV < 1);

# Find out how many lines the Promela model has.
open WC,"wc -l ".$ARGV[0]."|";
$linecount = <WC>;
$linecount =~ s/^ *(\d*).*\n/$1/;
close WC;

# Create the Büchi automaton
open SPIN,"./spin -f \'!".$ARGV[1]."\'|";
open NEVER,">never.$$";
while (<SPIN>) {
	$linecount++;
	if (/^(\w*):\n$/) {
		push @labels,(uc $1);
		print NEVER $_;
	} elsif (/skip/) {
		set_labels();
		print NEVER "	if\n	:: (1) -> goto accept_all\n	fi;\n";
		$linecount += 2;
	} elsif (/^	if/) {
		set_labels();
		print NEVER $_;
	} else {
		print NEVER $_;
	}
}
close SPIN;
close NEVER;

# Match Büchi state labels to pan's state numbers
system("./spin -a -N never.$$ ".$ARGV[0]);
system("gcc -O2 -DCHECK -Wno-all -Wno-unused-result -o pan pan.c");

open PAN,"./pan -d|";
while (<PAN>) {
	last if /proctype :never:/;
}
while (<PAN>) {
	next unless (/state *(\d*).* line (\d*) =>/);
	my ($statenum,$linenum) = ($1,$2);
	next unless $stateline{$linenum};
	$accepting{$statenum} = ($stateline{$linenum} =~ /ACCEPT/)? 1 : 0;
	$initialstate = $statenum if $linenum == $firststate_line;
}
close PAN;
system("mv never.$$ never");
# unlink "never.$$";

# Build the state graph from pan's DFS output
open PAN,"./pan 2>/dev/null |";
open TRANS,">trans.$$";
open ACC,">acc.$$";

$buechistate = $initialstate;
$dfsstate = 0;
@stack = ();
while (<PAN>) {
	last if (/	New state 0/);
}
push @stack,({state => $dfsstate, buechi => $buechistate });
print ACC "0\n" if $accepting{$initialstate};

while (<PAN>) {
	if (/^\d*: Down/) {
		push @stack,({state => $dfsstate, buechi => $buechistate });
	} elsif (/^	New state (\d+)/) {
		$numstates = $1+1;
		pop @stack;
		print TRANS "$dfsstate $1\n";
		$dfsstate = $1;
		print ACC "$dfsstate\n" if $accepting{$buechistate};
		push @stack,({state => $dfsstate, buechi => $buechistate });
	} elsif (/^	(Old|Stack) state (\d+)/) {
		print TRANS "$dfsstate $2\n";
	} elsif (/^ *\d+: proc 0 exec \d+, \d+ to (\d+)/) {
		$buechistate = $1;
	} elsif (/^\d*: Up/) {
		pop @stack;
		my $tmp = pop @stack;
		$dfsstate = $tmp->{state};
		$buechistate = $tmp->{buechi};
		push @stack,($tmp);
	}
}
close PAN;
close ACC;
close TRANS;

# Print the graph
print $numstates."\n";
system("cat acc.$$");
print "-1\n";
system("cat trans.$$");
print "-1\n";

#unlink ("trans.$$","acc.$$","pan","pan.b","pan.c","pan.h","pan.m","pan.t");
unlink ("trans.$$","acc.$$","pan.b","pan.c","pan.h","pan.m","pan.t");

exit 0;

# Subroutines

sub set_labels {
	my @sortlabels = sort @labels;
	$stateline{$linecount} = $sortlabels[0];
	@labels = ();
	$firststate_line = $linecount unless $firststate_line;
}

sub usage {
	print "Usage: ess.pl <promela model> <formula>\n";
	print "Extracts the product state space of the model and the Büchi\n";
	print "automaton of the negated formula from Spin's output.\n";
	exit 1;
}
