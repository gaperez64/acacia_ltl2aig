#! /usr/bin/perl -w

# $Id: ltl2aut.pl,v 1.44 2006/10/25 08:35:46 bjobst Exp $

# This script generates Buechi automata from LTL formulae using
# the Daniele-Giunchiglia-Vardi algorithm and various optimizations.

# Author: Fabio Somenzi <Fabio@Colorado.EDU>, with modifications
# by Roderick Bloem <roderick.bloem@colorado.edu>

use Sopen;
use LTL;
use LTL2AUT;
use Verilog;
use strict;

my $startTime = (times)[0];

# Set default values for options.
my $verb = 1;			# verbosity level
my @formulae = ();		# list of LTL formulae to be processed
my $prefix = "ltl2aut";		# prefix for output file names
my $method = "Boolean";		# method (GPVW, GPVW+, LTL2AUT, Boolean)
my $simplify = 1;		# simplify formula
my $optimize = 1;		# optimize automaton
my $complete = 0;		# complete transition relation
my $help     = 0;               # help is requested
my $automaton = "";		# automaton file
my $monitorFile = "";		# Verilog monitor file
my $verify = 0;

# Parse command line and set options accordingly.
while (defined($ARGV[0]) && substr($ARGV[0], 0, 1) eq "-") {
    if ($ARGV[0] eq "-c") {
	shift;
	$complete = shift;
    } elsif ($ARGV[0] eq "-f") {
	shift;
	push(@formulae, shift);
    } elsif ($ARGV[0] eq "-h") {
	shift;
	$help = 1;
    }  elsif ($ARGV[0] eq "-ltl") {
	shift;
	my $ltlfile = shift;
	readLTL($ltlfile,\@formulae);
    } elsif ($ARGV[0] eq "-auto") {
	shift;
	$automaton = shift;
    } elsif ($ARGV[0] eq "-m") {
	shift;
	$method = shift;
    } elsif ($ARGV[0] eq "-o") {
	shift;
	$optimize = shift;
    }  elsif ($ARGV[0] eq "-p") {
	shift;
	$prefix = shift;
    }elsif ($ARGV[0] eq "-s") {
	shift;
	$simplify = shift;
    }  elsif ($ARGV[0] eq "-v") {
	shift;
	$verb = shift;
    } elsif ($ARGV[0] eq "-ver") {
	shift;
	$verify = shift;
    } elsif ($ARGV[0] eq "-mon") {
	shift;
	$monitorFile = shift;
    } else {
	warn "unrecognized option: $ARGV[0]\n";
	shift;
    }
}

die helpMessage() if $help;

die usage() if $#ARGV !=-1 or (@formulae == 0 and $automaton eq "");

# Process each formula.
open(PARSE, ">$prefix" . "-parse.dot");
open(BUECHI, ">$prefix" . "-buechi.dot");
open(SCC, ">$prefix" . "-scc.dot");
open(MONITOR, ">$monitorFile") if $monitorFile ne "";
foreach my $formula (@formulae) {
    print '-' x 70, "\n", $formula, "\n", '-' x 70, "\n";
    my $parsetree = LTL->new($formula);
    print $parsetree->ToString, "\n" if $verb > 1;
    print $parsetree->ToDot($formula) if $verb > 3;
    my $normalized = $parsetree->Normalize;
    $normalized = $normalized->Simplify if $simplify;
    my $dot = $normalized->ToDot($parsetree->ToString);
    print PARSE $dot;
    print $normalized->ToString, "\n";
    my $result = LTL2AUT->new(formula => $normalized, method => $method);
    $result->Optimize($verb) if $optimize;
    if ($verify) {
	my $negation = $parsetree->Not->Normalize;
	my $complement = LTL2AUT->new(formula => $negation, method => $method);
	my $intersection = $result->Intersection($complement)->Prune;
	print "Intersection not empty!\n"
	  unless $intersection->NumberOfStates == 0;
	$result = $result->Union($complement);
	$result->Optimize($verb);
    }
    $result->MakeComplete if $complete;
    print $result->ToString;
    print BUECHI $result->ToDot($formula);
    if ($monitorFile ne "") {
	print MONITOR $result->ToVerilogMonitor;
    }
    my $quotient = $result->Quotient($result->SCC);
    print "SCC quotient graph:\n", $quotient->ToString if $verb > 2;
    print SCC $quotient->ToDot($formula);
    print "Stats: ", $result->Stats, "\n";
}
close PARSE;
if ($automaton ne "") {
    my $moddate = sopen($automaton,\*AUTOMATON);
    my $result = Buechi->new(file => \*AUTOMATON);
    close AUTOMATON;
    if ($optimize) {
	$result->Optimize($verb);
    }
    print $result->ToString;
    print BUECHI $result->ToDot($automaton);
    if ($monitorFile ne "") {
	print MONITOR $result->ToVerilogMonitor;
    }
    my $quotient = $result->Quotient($result->SCC);
    print "SCC quotient graph:\n", $quotient->ToString if $verb > 2;
    print SCC $quotient->ToDot($automaton);
    print "Stats: ", $result->Stats, "\n";
}
close BUECHI;
close SCC;
close MONITOR if $monitorFile ne "";
my $endTime = (times)[0];
printf "CPU time: %.2f seconds\n", $endTime - $startTime;

exit(0);


######################################################################
# Read LTL formulae from file and append them to a list.
######################################################################
sub readLTL {
    my ($file,$fref) = @_;
    my $moddate = sopen($file,\*FFILE);
    while (<FFILE>) {
	chop;				# discard newline
	s/\#.*//;			# discard comments
	s/;//;				# discard trailing semicolon
	s/\s+$//;			# discard trailing blanks
	push(@$fref,$_) unless /^\s*$/;	# skip empty lines
    }
    close(FFILE);

} # readLTL


######################################################################
# Return the usage message.
######################################################################
sub usage {
    return <<EOF;
Usage: $0 [-c {0,1}] [-f formula] [-h]  [-ltl file]
       [-m method] [-o {0,1}] [-p prefix] [-s {0,1}] [-v n]
       [-ver {0,1}] [-auto file] [-mon file]
EOF

} # usage


######################################################################
# Return the help message.
######################################################################
sub helpMessage {
    return usage() . <<EOF;

-c {0,1}  : Iff n != 0, make the transition relation of the automaton complete
            (off by default).
-f formula: The LTL formula to be translated.  Use either -ltl or -f.
-h        : gives this help.
-ltl file : file containing the LTL formulae to be ranslated.
            Use either -ltl or -f.
-m method : Sets the method used in translation.  Method ranges over
            GPVW, GPVW+, LTL2AUT, Boolean.  Default is Boolean.
-o {0,1}  : Optimize the automaton after translation, using simulation
            relations. On by default.
-p prefix : Sets the prefix of the files that are written.  Default: ltl2aut.
-s {0,1}  : Iff n != 0, simplify the formula before translating it, using
            rewriting.  On by default.
-v n      : Sets the verbosity level (0 <= n <= 4, default is 1).
-ver{0,1} : Iff n!= 0, make an attempt at verifying the automaton.
            Off by default.
-auto file: Optimizes an automaton described in file.
-mon file : wite a Verilog monitor to file.

This is Wring, by Fabio Somenzi, University of Colorado.  No warranty
is given for the correctness of this code or its suitability for any
purpose.  Given an LTL formula, creates a Buechi automaton that
accepts exactly those traces that satisfy the formula.  See [SB00] for
a description of the algorithm.  Wring incorporates the algorithms of
[GPVW95] and [DGV99], as special cases.  The program writes three
files: prefix-parse.dot, prefix-buechi.dot, and prefix-scc.dot.  These
files hold the graphs of the parse tree, the Buechi automaton, and the
SCC-quotient graphs of the automaton respectively.  They are in dot
format, which can be translated using dot.  Please learn the syntax of
LTL formulae from the examples below.

Examples:

ltl2aut.pl -f '!(p=1 U (q=1 U r=1))' -p wring
Produces the automaton for the formula using wring, the strongest algorithm.
Equivalent to:
ltl2aut.pl -f '!(p=1 U (q=1 U r=1))' -p wring -m Boolean -s 1 -o 1

ltl2aut.pl -f '(G(F(p=1))) -> (G(F(q=1)))' -p wring -s 0 -o 0 -m LTL2AUT -v 4
Produces the automaton for the formula in the manner of [DGV99].

ltl2aut.pl -f '(F(p=1)) U (G(q=1))' -p wring -s 0 -o 0 -m GPVW -v 0
Produces the automaton for the formula in the manner of [GPVW95].

NB: The algorithm uses hash tables extensively, which makes it sensitive to
memory issues.  Results may be different between a run that uses -s 1 and and
run that does not, even though -s 1 is the default, because specifying options
shifts data in memory.

EOF

} # helpMessage
