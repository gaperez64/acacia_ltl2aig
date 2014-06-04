#! /usr/bin/perl -w

# $Id: testRand.pl,v 1.2 2005/09/26 11:44:23 bjobst Exp $

# script to run various methods for automata generation on  LTL formulae
# that are either randomly generated or supplied from the outside.
#
# Author: Fabio Somenzi <Fabio@Colorado.EDU>

use LTL;
use LTL2AUT;
use Sopen;
use strict;

my $startTime = (times)[0];

# Set default values for options.
my $verb = 1;			# verbosity level
my $help = 0;			# help is requested
my @formulae = ();		# list of LTL formulae to be processed
my $samples = 0;		# number of random formulae to generate
my $length = 8;			# length of the formulae
my $atoms = 4;			# number of distinct atomic propositions
my $p = 0.5;			# probability that the top node be U or R
my $logfile = "";		# log file (STDOUT if null string)
my @method = ('GPVW', 'GPVW+', 'LTL2AUT', 'r', 'b', 'o', 'rb', 'ro',
	      'bo', 'Wring');

# Parse command line and set options accordingly.
while (defined($ARGV[0]) && substr($ARGV[0], 0, 1) eq "-") {
    if ($ARGV[0] eq "-v") {
	shift;
	$verb = shift;
    } elsif ($ARGV[0] eq "-h") {
	shift;
	$help = 1;
    } elsif ($ARGV[0] eq "-s") {
	shift;
	$samples = shift;
    } elsif ($ARGV[0] eq "-f") {
	shift;
	push(@formulae, LTL->new(shift)->Normalize);
    } elsif ($ARGV[0] eq "-ltl") {
	shift;
	my $ltlfile = shift;
	readLTL($ltlfile,\@formulae);
    } elsif ($ARGV[0] eq "-l") {
	shift;
	$length = shift;
    } elsif ($ARGV[0] eq "-p") {
	shift;
	$p = shift;
    } elsif ($ARGV[0] eq "-n") {
	shift;
	$atoms = shift;
    } elsif ($ARGV[0] eq "-m") {
	shift;
	my $methods = shift;
	@method = split ' ', $methods;
    } elsif ($ARGV[0] eq "-log") {
	shift;
	$logfile = shift;
    } else {
	warn "unrecognized option: $ARGV[0]\n";
	shift;
    }
}

if ($help == 1 or $#ARGV != -1) {
    die "Usage:	$0 [-v n] [-h] [-f formula] [-ltl file] [-s samples]\n\t[-l length] [-n atoms] [-p probability] [-log logfile] [-m methods]\n";
}

# Open log file.
my $logref = \*STDOUT;
if ($logfile ne "") {
    open(LOG, ">$logfile");
    $logref = \*LOG;
}

# Initialize statistics.
my %states = ();
my %transitions = ();
my %fairsets = ();
my %init = ();
my %weak = ();
my %terminal = ();
my %time = ();

foreach my $method (@method) {
    $states{$method} = 0;
    $transitions{$method} = 0;
    $fairsets{$method} = 0;
    $init{$method} = 0;
    $weak{$method} = 0;
    $terminal{$method} = 0;
    $time{$method} = 0.0;
}

# Run the methods on the randomly generated formulae and collect stats.
for (my $i = 0; $i < $samples; $i++) {
    push(@formulae, LTL->Random($atoms,$length,$p));
}

foreach my $formula (@formulae) {
    print $logref $formula->ToString, "\n";
    foreach my $method (@method) {
	my $itime = (times)[0];
	my $result;
	if ($method eq 'Wring') {
	    my $simplified = $formula->Simplify;
	    $result = LTL2AUT->new(formula => $simplified,
				   method => 'Boolean');
	    $result->Optimize($verb);
	} elsif ($method eq 'r') {
	    my $simplified = $formula->Simplify;
	    $result = LTL2AUT->new(formula => $simplified,
				   method => 'LTL2AUT');
	} elsif ($method eq 'b') {
	    $result = LTL2AUT->new(formula => $formula,
				   method => 'Boolean');
	} elsif ($method eq 'o') {
	    $result = LTL2AUT->new(formula => $formula,
				   method => 'LTL2AUT');
	    $result->Optimize($verb);
	} elsif ($method eq 'rb') {
	    my $simplified = $formula->Simplify;
	    $result = LTL2AUT->new(formula => $simplified,
				   method => 'Boolean');
	} elsif ($method eq 'ro' or $method eq 'New') {
	    my $simplified = $formula->Simplify;
	    $result = LTL2AUT->new(formula => $simplified,
				   method => 'LTL2AUT');
	    $result->Optimize($verb);
	} elsif ($method eq 'bo') {
	    $result = LTL2AUT->new(formula => $formula,
				   method => 'Boolean');
	    $result->Optimize($verb);
	} else {
	    $result = LTL2AUT->new(formula => $formula, method => $method);
	}
	my $time = (times)[0] - $itime;
	if ($verb > 0) {
	    printf $logref "%7s: %s %.2f s\n", $method, $result->Stats, $time;
	}
	$states{$method} += $result->NumberOfStates;
	$transitions{$method} += $result->NumberOfTransitions;
	$fairsets{$method} += $result->NumberOfFairSets;
	$init{$method} += $result->NumberOfInitialStates;
	my $strength = $result->Strength;
	$weak{$method}++ if $strength eq "weak";
	$terminal{$method}++ if $strength eq "terminal";
	$time{$method} += $time;
    }
}

close LOG if $logfile ne "";

# Print out stats.
print "Summary for $samples random formulae with $atoms atomic propositions\n";
print " $length nodes in the parse trees and $p Us and Rs\n";
print " and ", @formulae - $samples, " externally supplied formulae\n";
print "method\t states\t trans\t fair\t init\t weak\t term\t time\n";
foreach my $method (@method) {
    print $method, "\t& ",
    $states{$method}, "\t& ", $transitions{$method},
      "\t& ", $fairsets{$method}, "\t& ",
	$init{$method}, "\t& ", $weak{$method}, "\t& ",
	  $terminal{$method}, "\t& ";
    printf "%.1f \\\\\n", $time{$method};
}

my $endTime = (times)[0];
printf "CPU time: %.2f seconds\n", $endTime - $startTime;

exit 0;


######################################################################
# Read LTL formulae from file, convert them to normalized parse
# graphs, and append them to a list.
######################################################################
sub readLTL {
    my ($file,$fref) = @_;
    my $moddate = sopen($file,\*FFILE);
    while (<FFILE>) {
	chop;				# discard newline
	s/\#.*//;			# discard comments
	s/;//;				# discard trailing semicolon
	s/\s+$//;			# discard trailing blanks
	push(@$fref, LTL->new($_)->Normalize) unless /^\s*$/;
					# skip empty lines
    }
    close(FFILE);

} # readLTL
