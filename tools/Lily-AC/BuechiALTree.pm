# $Id: BuechiALTree.pm,v 1.39 2006/10/03 10:10:50 bjobst Exp $

######################################################################
# Functions to create and manipulate Buechi Tree automata with labels
#                       on the arcs
#
# A BuechiALTree automaton inherits from a BuechiAL (nondet Buechi
# automaton with labels on the edges) the following members:
# states    => Set of STATE
# init      => Set of STATE
# delta     => Hash from STATE -> Set of TRANSITIONS
# fair      => Set of Set of STATE
# names     => Hash from STATE -> String
#
# Basically STATE can be any datastructure. In our application it is
# a Pair of Sets.
# A TRANSITION is a Pair of LABEL and DESTINATIONSET.
# A LABEL is a cubes over the APs stores Set of LTL and a
# DESTINATIONSET is a conjunct of direction-state-pairs stores as Set
# of Pairs of (LABEL,STATE).
#
# Additionally BuechiALTree stores the directions and labels:
# directions => Pair of (Set of LABEL, Set of LABEL)
#
# Meaning of delta:
# delta(q,l) = B+(D x Q), e.g. delta(q1,a=1) = (1,q1) * (2,q2)
#
# delta(q) is not defined is equivalent to delta(q) = FALSE
# The same holds if delta is not defined for a particular label or
# a particular directions.
#
# Lily - LInear Logic sYnthesize
# Author: Barbara Jobstmann <bjobst@ist.tugraz.at>
#
######################################################################
package BuechiALTree;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK $nameIndex $DEBUG);
@ISA       = qw(BuechiAL);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
$DEBUG     = 0;
use strict;
use Set;
use Cover;
use Pair;
use LTL;
use Utils;
use CoBuechiTree;
use AlternatingTree;

# Inherited sub from BuechiAL that we use:
# sub new
# sub Stats
# sub NumberOfStates
# sub NumberOfFairSets
# sub NumberOfInitialStates
# sub Strength
  
######################################################################
# Construct a new automaton.
######################################################################
sub new {
    my $class  = shift;
    my %params = @_;

    # If either a file handle or a string is given, it is assumed to
    # contain the description of an automaton in the format produced
    # by ToString.  The automaton is built from this description, and
    # the remaining parameters are ignored.
    if (defined $params{file}) {
	return FromString(file => $params{file},class => 'BuechiALTree');
    } elsif (defined $params{string}) {
	return FromString(string => $params{string},class => 'BuechiALTree');
    }
    # Read parameters and supply default values as needed.
    $params{states} = Set->new unless defined($params{states});
    $params{init} = Set->new unless defined($params{init});
    $params{delta} = {} unless defined($params{delta});
    $params{fair} = Set->new unless defined($params{fair});
    $params{names} = Buechi::AddNames($params{states}) unless defined($params{names});
    $params{directions}  = Pair->new  unless defined( $params{directions} );
    # Build the automaton.
    my $self = {
		states    => $params{states},
		init      => $params{init},
		delta     => $params{delta},
		fair      => $params{fair},
		names     => $params{names},
		directions => $params{directions},
	       };
    return bless $self, $class;
}    # new


######################################################################
# Takes a Buechi word automaton for (not phi) and an I/O-paritioning  
# and builds a NBT for the realizability problem of phi.
# The last two parameter are the formula name and a debug directory.
######################################################################
sub SynthesisTree {
	my ( $self, $verb, $partition, $formula, $dir, $redirect ) = @_;
	$redirect = 0 if (not defined $redirect);
	# redirect standard output
	my $oldout;
	if ($redirect) {
	  open $oldout, ">&STDOUT" or die "Can't duplicate STDOUT: $!";
	  open STDOUT, ">$dir"."ltl2aut.out" or die "Can't redirect STDOUT: $!";
	} else {
	  open $oldout, ">&STDOUT";
	}
	
	if ( $$self{fair}->Size == 0 ) {
		# all states are accepting
		foreach my $state ($$self{states}) {
			$$self{fair}->Push($state);
		}
	} 
	if ( $$self{fair}->Size != 1 ) {
		open( FP, ">>$dir"."outours" );
		print FP "fair set size not equal to 1\n";
		close(FP);
		open( FP, ">>$dir"."outcomp" );
		print FP '-' x 70, "\nfair set size not equal to 1\n", '-' x 70, "\n";
		close(FP);
		print "Abort ComplementTree\n";
		# restore the original standard output
		if ($redirect) {
		  close STDOUT;
		  open STDOUT, ">&", $oldout or die "Can't restore old STDOUT: $!";
		}
		return;
	}

	if ($verb > 1) {
	    open( NBW, ">$dir"."nbw.dot" );
	    open( UCT, ">$dir"."uct.dot" );
	    open( AWT, ">$dir"."awt.dot" );
	    open( AWTB, ">$dir"."awt-before.dot" );
	    open( NBT, ">$dir"."nbt.dot" );
	}
#	alarm 60;
#	$SIG{'ALRM'} = \&timeouthandler;

	####################################################################
	# NBW (state) -> NBW (transition)
	print $oldout "NBW(state-labeled) -> NBW(transition labeled)...\n";
	my $bl =  BuechiAL->fromBuechi($self);  # 1 NBW(state-labeled) -> NBW(transition-labeled)
	$bl->DirectSimulationMinimization;
	$bl->FairSimulationMinimization;
	print "BuechiAL\n".$bl->ToString, "\n" if $verb > 2;
	$formula = "";
	print NBW $bl->ToDot("! ".$formula) if $verb > 1;
	print $oldout "NBW (state) -> NBW (trans) done\n";
	
	#print states - name -table
	if ($verb > 1) {
	    my $states = $$bl{states};
	    my $names = $$bl{names};
	    foreach my $state (values %$states) {
		print $$names{$state}." -> ".$state->ToString."\n";
	    }
	}
	if ($self->IsWeak) {
	    #TODO seams like $self has already changed here?
	    print "NBW(transition labeled) is weak.\n";
	} else {
	    print "NBW(transition labeled) is not weak.\n";
	}
	
	####################################################################
	# NBW -> UCT
	print $oldout "NBW -> UCT...\n";
	my $cb = CoBuechiTree->fromBuechi( $bl, $partition, $verb ); # 2 NBW -> UCT
	print "CoBuechiTree\n".$cb->ToString, "\n" if $verb > 2;
	print UCT $cb->ToDot($formula) if $verb > 1;
	print $oldout "NBW -> UCT done\n";
	print "Stats UCT: ", $cb->Stats, "\n";
	
	####################################################################
	# UCT -> AWT
	my $stti = time();
	print $oldout "UCT -> AWT...\n";
	my $al = AlternatingTree->fromBuechi( $cb, $bl->IsWeak, $verb );       # 3 UCT -> AWT
	print AWTB $al->ToDot($formula) if ($verb > 1);
	print $oldout "UCT -> AWT done\n";
	print "Stats AWT: ", $al->Stats, "\n";

	print $oldout "AWT Minimization...\n";
	$al->Minimization($verb);
	print "Stats AWT: ", $al->Stats, "\n";
	$al->DirectSimulationMinimization;
	print AWT $al->ToDot($formula) if $verb > 1;
	print $oldout "AWT Minimization done\n";
	print "Stats AWT: ", $al->Stats, "\n";
	
	####################################################################
	# AWT -> NBT
	print $oldout "AWT -> NBT...\n";
	my $co = $al->ToBuechi($verb); # returns BuechiALTree
	print NBT $co->ToDot($formula) if $verb > 1;
	print $oldout "AWT -> NBT done\n";
	
	if ($verb > 1) {
	    Utils::dot2ps($dir."uct.dot");
	    Utils::dot2ps($dir."nbw.dot");
	    Utils::dot2ps($dir."awt-before.dot");
	    Utils::dot2ps($dir."awt.dot");
	    Utils::dot2ps($dir."nbt.dot");
	    close (NBW);
	    close (UCT);
	    close (AWT);
	    close (AWTB);
	    close (NBT);
	}
	
	# restore the original standard output
	if ($redirect) {
	  close STDOUT;
	  open STDOUT, ">&", $oldout or die "Can't restore old STDOUT: $!";
	}
	
	return $co;
}

######################################################################
# Is the language of the automaton empty
######################################################################
sub IsEmpty {
	my $self = shift;
	return 1 if ($$self{init}->Size == 0);
	return "";
}

######################################################################
# Converts an automaton to dot format.
######################################################################
sub ToDot {
    my ( $self, $graphname ) = @_;
    my $nodes    = $$self{states};
    my $fair     = $$self{fair};
    my $names    = $$self{names};
    my $labels   = $$self{labels};
    my $delta    = $$self{delta};
    my $init     = $$self{init};
    my %fairness = ();
    my $falsenode = 0;

    my $type    = ref($self);
    my $edge    = ($type eq "BuechiALTree")?"circle":"box";

    foreach ( values %{$nodes} ) {
	$fairness{$_} = "(";
    }
    my $i = 1;
    foreach my $fairset ( values %{$fair} ) {
	foreach my $node ( values %{$fairset} ) {
	    $fairness{$node} .= "," unless $fairness{$node} eq "(";
	    $fairness{$node} .= $i;
	}
	$i++;
    }
    foreach ( values %{$nodes} ) {
	$fairness{$_} .= ")";
    }
    my $string = qq!digraph "$graphname" {\nnode [shape=ellipse];\n!;
    $string .= qq!size = \"11,7.5\";\ncenter = true;\nrotate = 90;\n!;
    $string .= qq!"title" [label=\"$type - $graphname\",shape=plaintext];\n!;
    foreach my $node ( values %{$nodes} ) {
	if ( $init->IsMember($node) ) {
	    my $pred = "init-" . $$names{$node};
	    $string .= qq!"$pred" [style=invis]\n!;
	    $string .= qq!"$pred" -> "$$names{$node}";\n!;
	}
	my $label = "";
	$string .= qq!"$$names{$node}" [label=\"$$names{$node}\\n$label$fairness{$node}\"];\n!;
	my $next = $$delta{$node};
	next unless defined $next; #tr leaves the automaton
	if ( defined $$names{$next} ) {
	    $string .= qq!"$$names{$node}" -> "$$names{$next}"[label=""];\n!;
	    die; #I don't except this to be used
	}
	if ($next->Size == 0) {
	    $falsenode = 1;
	    $string .= qq!"$$names{$node}" -> "falsenode"[label=""];\n!;
	    next;
	}
	my $i = 0;		#paircounter
      LP: foreach my $labeledPair ( values %{$next} ) {
	    my $slabel = $labeledPair->First->ToString;
	    my $nlabel = $slabel;
	    $nlabel =~ s/{//;
	    $nlabel =~ s/}//;
	    $nlabel =~ s/=//;
	    my $destSet = $labeledPair->Second;
	    if ( defined $$names{$destSet} ) {
		$string .= qq!"$$names{$node}" -> "$$names{$destSet}"[label="$slabel"];\n!;
		next LP;
	    }
	    if ($destSet->Size == 0) {
		$string .= qq!"$$names{$node}" -> "falsenode"[label="$slabel"];\n!;
		$falsenode = 1;
		next LP;
	    }
	    if ( $destSet->Size == 1 ) {
		my $destnode = $destSet->Pick;
		my $direction = $destnode->First->ToString;
		$string .= qq!"$$names{$node}" -> "$$names{$destnode->Second}"[label="D$direction$slabel"];\n!;
		next;
	    }
	    $string .= qq!"$$names{$node}" -> "tri$nlabel$$names{$node}$i"[label="$slabel"];\n!;
	    $string .= qq!"tri$nlabel$$names{$node}$i" [label="",shape=$edge,height=0.5,width=0.5];\n!;
	    foreach my $succnode ( values %{$destSet} ) {
		my $direction = $succnode->First->ToString;
		my $destnode = $succnode->Second;
		if (defined $$names{$destnode}) {
		    $string .= qq!"tri$nlabel$$names{$node}$i" -> "$$names{$destnode}"[label="D$direction"];\n!;
		} else {
		    #this is a conjunct of successor and one of the successor leads to
		    #FALSE, so the whole conjunct should lead to false ->simplify
		    print "state: ".$$names{$node}."\n";
		    print "conjunct: ".$destSet->ToString($names)."\n";
		    print "name missing:". $destnode->ToString ."\n";
		    die "die Conjunct with FALSE should be simplified\n";
		}
	    }
	    $i++;
	}
    }
    $string .= qq!}\n!;
    return $string;
} # ToDot

######################################################################
# Takes an NBT and calculates language emptiness. If the language 
# isn't empty, returns a witness (a determinstic BuechiALTree).
#
# To determine if the language if empty, we compute a corresponding 
# Buechi game, where the protagonist selects the transitions of the 
# tree automaton and the antagonist chooses the directions.
# The winning condition for the protagonist is to reach infinitely 
# often one of the fair states.
# If the game is won, we compute the attractor strategy, which tells 
# to move to a fair state as fast as possible. Finally we build a
# deterministc (BuechiALTree) automaton (witness) according to the 
# strategy.
# Returns a BuechiALTree if the language isn't empty; otherwise "";
######################################################################
sub LanguageEmptiness {
	my $self = shift;
	my %params = @_;
	my $states = $$self{states};
	my $delta  = $$self{delta};
	my $directions= $$self{directions};
	my $init   = $$self{init};
	my $names  = $$self{names};
	my $win;

	if ($init->Size == 0) {
	    print "No initial states\n";
	    return;
	}
	if (defined $params{win}) {
	    $win = $params{win};
	} else {
	    print "Calculate winning region...\n";
	    $win = $self->Winning(%params);
	}
	if ($init->IsIncluded($win) eq "") {
	    print "Initial state is not winning.\n";
	    #print "Winning region:\n" . $win->ToString($names) . "\n" if $verb > 2;
	    return;
	}

	print "done\n";
	print "Calculate winning strategy...";
	my $strategy = $self->Strategy($win);
	# The strategy is a map
	# state -> (label, dir-state-pair-set)
	# e.g. n1 -> (a=1, {(r=1,n2),(r=0,n1)})
	print "done\n";
	
	print "Build witness...";
	my $wstates = Set->new;     #set of states of the witness
	my $winit   = $init->Clone; #initial state
	my $wdelta  = {};           #transition relation of the witness
	my $wnames = {};            #names of the (witness-)states

	#Note: these automata have only a single initial state
	my $unexpanded = Set->new($winit->Pick); 
	while ($unexpanded->Size > 0) {
		my $state = $unexpanded->Pop;
		$wstates->Push($state);
		$$wnames{$state} = $$names{$state};
		print "Add state ".$state->ToString($wnames)."\n";
		die if (not defined $$strategy{$state});
		#print "Strategy ".$$strategy{$state}->ToString($names)."\n";
		$$wdelta{$state} = Set->new;
		$$wdelta{$state}->Push($$strategy{$state}); 
		my $destSet = $$strategy{$state}->Second;
		foreach my $dirPair (values %$destSet) {
			if ( not $wstates->IsMember($dirPair->Second)) {
				$unexpanded->Push($dirPair->Second);
			}
		}
	}
	print "done\n";
	
	my $witness = BuechiALTree->new( states => $wstates,
					 init   => $winit,
					 delta  => $wdelta,
					 directions => $directions,
					 fair   => Set->new,
					 names  => $wnames);
	return $witness;
}

######################################################################
# Creates a Hashtable which maps from each winning state to a single 
# label according to the attractor-strategy (M win U win*fair) of the 
# fair states.
# Returns a (possible empty) hash: state -> label.
######################################################################
sub Strategy {
	my ($self,$win) = @_;
	my $states = $$self{states};
	my $fair   = $$self{fair}->Pick;
	my $names  = $$self{names};
	my %strategy = ();

	my $i = 0;
	my %Y =();
	my $nY = $fair->Intersection($win); #Onionring 0 = fair*win
	my $Y = Set->new;
	# According to the onionring of M win U win*fair
	# mu Y. win * (fair + MX Y))
	my %nextLabel = ();
	#to add the strategy for states in onionring 0 (fair states)
	$self->MX($win, \%nextLabel);
	my $tmpSet;
	do {
		$Y{$i} = $nY->Clone;
		$Y{$i}->Subtract($Y);
		$tmpSet = $Y{$i};
		foreach my $state (values %$tmpSet) {
			next if ((defined $strategy{$state}) or (not defined $nextLabel{$state}));
			#$strategy{$state} = $nextLabel{$state}->First;
			$strategy{$state} = $nextLabel{$state};
			#print $state->ToString($names)."->";
			#print $strategy{$state}->First->ToString($names)."->";
			#print $strategy{$state}->Second->ToString($names)."\n";
		}
		$i++;
		$Y = $nY;
		#nextLabel holds strategy from onionring i to i-1, we have to reset it
		#for the next onionring
		%nextLabel = ();
		my $union = $fair->Union($self->MX($Y,\%nextLabel));
		$nY = $union->Intersection($win);
	} while (not $Y->IsEqual($nY));

	return \%strategy;
}

######################################################################
# Computes the winning region for the following Buechi game:
# From each states the protagonist can choose a transition/labeling, 
# while the antagonist chooses the direction.
# The winning condition for the protagonist is to reach infinitely 
# often one of the fair states.
# We compute MG true under fairness using the fix-point formula
# nu Z. MX(mu Y. Z * (fair + MX Y)).
# Finally we check if the initial state is in the winning region.
# Returns the set of winning states.
######################################################################
sub Winning {
        my $self = shift;
	my %params = @_;
	my $states = $$self{states};
	my $init   = $$self{init};
	my $fair   = $$self{fair}->Pick;
	my $names  = $$self{names};
	my $verb = 1;
	my $oldWin = Set->new;
	
	$verb = $params{verb} if (defined $params{verb});
	$oldWin = $params{oldwin}  if (defined $params{oldwin});
	
	# MG true under fairness = nu Z. MX (M Z U (Z * fair))
	# nu Z. MX (M Z U Z * fair) = nu Z. MX(mu Y. Z * fair + (Z * MX Y)) = 
	# nu Z. MX (mu Y. Z * (fair + MX Y)) with 
	# Z0 = alle states, Y0 = fair states (wrong) Y0 = empty set
	# if we already know some winning states, we can start Y0 with those
	my $nZ = $states->Clone;
	my $Z = Set->new;
	my $Y = Set->new;
	my $nY = $oldWin->Clone;
	my $zfair;
	while (not $Z->IsEqual($nZ)) {
		$Z = $nZ;
		$zfair = $fair->Intersection($Z);
		$nY = $oldWin->Clone;
		do {
			$Y = $nY;
			$nY = $self->MX($Y);
			$nY = $nY->Intersection($Z);
			$nY = $zfair->Union($nY);
			print "---- nY:".$nY->ToString($names)."\n" if $verb > 2;
		} while (not $Y->IsEqual($nY));
		$nZ = $self->MX($nY);
		print "-- nZ:".$nZ->ToString($names)."\n" if $verb > 2;
	}

	print "Winning:".$nZ->ToString($names)."\n" if $verb > 2;
	return $nZ;
}

######################################################################
# Computes MX(target), which are all states that can be forced by the
# protagonist to reach in the next step one of the target states.
# Note: The protagonist chooses the transition and the antagonist 
# chooses the direction.
# If the function is called with a reference to a hash ($mxLabel)
# then we store for each state in MX(target) the transition (label and
# destination set) leading to one of the target states in this hash.
# Returns a (possible empty) set of states.
######################################################################
sub MX {
	my ($self, $targetStates, $mxLabel, $verb) = @_;
	my $states = $$self{states};
	my $init   = $$self{init};
	my $delta  = $$self{delta};
	my $directions = $$self{directions};
	my $inputs = $directions->First;
	my $fair   = $$self{fair};
	my $names  = $$self{names};
	
	$verb = 1 if (not defined $verb); #set level of debug output
	print "------------------Call MX-----------------------\n" if $verb > 1;
	print "  Targets: ".$targetStates->ToString($names)."\n"  if $verb > 1;
	print "  Results: ".Set->new->ToString."\n" if ($targetStates->Size == 0) && ($verb > 1);
	return Set->new	if ($targetStates->Size == 0);	
	
	my $mxStates = Set->new;
  STATE:foreach my $state (values %$states) {
		print "Test state:".$state->ToString($names)."\n" if $verb > 2;
		my $next = $$delta{$state};
	 LL:foreach my $labelPair (values %$next) {
			my $dirPairSet = $labelPair->Second;
			my $coveredInputs = Cover->new; # Set of Sets = {{}}
			foreach my $dirPair (values %$dirPairSet) {
				next LL unless $targetStates->IsMember($dirPair->Second);
				if ($dirPair->First->Size == 0) {
				    #this transition covers all inputs
				    $mxStates->Push($state);
				    $$mxLabel{$state} = $labelPair if (defined $mxLabel);
				    print "Is covered independly with ".
				      $labelPair->First->ToString($names)."\n" if $verb > 2;
				    next STATE;
				}
				$coveredInputs->Push($dirPair->First);
			}
			my $covered = $coveredInputs->PrimeAndIrredundant;
			if ($covered->Size == 1 && $covered->Pick->Size == 0) {
			    $mxStates->Push($state);
			    if ($verb > 2) {
				print "Is covered by ".$labelPair->First->ToString($names)."\n";
				print "   Inputs:".$inputs->ToString($names)."\n";
				print "CovInputs:".$covered->ToString($names)."\n";
			    }
 			    if (defined $mxLabel) {
				if (not defined $$mxLabel{$state}) {
				    $$mxLabel{$state} = $labelPair;
				    print "Add new strategy\n" if $verb > 2;
				} else {
				    if (IsBetterStrategy($labelPair, $$mxLabel{$state})) {
					$$mxLabel{$state} = $labelPair;
					print "Replace strategy\n" if $verb > 2;
				    }
 				}
 			    }
			} else {
			    print "Not all inputs are covered\n" if $verb > 2;
			    print "CovInputs:".$covered->ToString($names)."\n" if $verb > 2;
			}
		} #foreach $labelPair
	} #foreach $state
	print "  Results:".$mxStates->ToString($names)."\n" if $verb > 1;
	return $mxStates;
}

######################################################################
# Check if transition $pairL is better then transition $pairR as
# strategy.  "Better" is defined according to the priorities used in
# sub ValueOfStrategy (see below).
# Note that a transition consists of a label and a set of
# dir-state-pairs.
######################################################################
sub IsBetterStrategy {
    my ($pairL, $pairR) = @_;
    die if ((ref($pairL) ne "Pair") or (ref($pairR) ne "Pair"));
    
    my $countL = StrategyValueOfTransition($pairL);
    my $countR = StrategyValueOfTransition($pairR);

    if ($countL > $countR) {
	return "";
    } else {
	return 1;
    }
}

######################################################################
# Computes the value of a transition as part of a strategy.  The value
# depends on the states this transition leads to.  A LOWER value
# indicates a BETTER strategy.
# The automata (NBT) we are dealing with are constructed from other
# automata (AWT).  A state of the NBT consists of two subsets (S,O) of
# AWT-states.  Intuitively, the language accepted in an NBT-state can
# be seen as the conjunct of the languages accepted in the states in S.
# States in the Subset 0 represent paths of an NBT-run which owe a
# visit to an accepting state.  Therefore we compute the value of a
# transition as follow: value = (states in S) + 3 * (states in O)
######################################################################
sub StrategyValueOfTransition {
    my $transition = shift;
    die if (ref($transition) ne "Pair");

    my $strategySet = $transition->Second;
    die if (ref($strategySet) ne "Set");
    my $count = 0;
    foreach (values %$strategySet) {
	die if (ref($_) ne "Pair");
	my $state = $_->Second;
	die if (ref($state) ne "Pair");
	my $S = $state->First;
	my $O = $state->Second;
	die if ((ref($S) ne "Set") or (ref($O) ne "Set"));
	#Priority
	#1 smaller obligations
	#2 smaller states
	#3 lesser sets
	$count = $count + $S->Size + (3 * $O->Size);
    }

    return $count;
}

######################################################################
# Converts an automaton to a Verilog model. The direction are the
# input of the model and the labeling represents the outputs. The
# model is a Moore machine, therefore the outputs only depend on the
# current state.
# If the automaton is nondeterministic, the translation picks an 
# arbitray transition of the possible ones.
######################################################################
sub ToVerilog {
	my ( $self, $graphname ) = @_;
	my $nodes    = $$self{states};
	my $names    = $$self{names};
	my $labels   = $$self{labels};
	my $delta    = $$self{delta};
	my $directions = $$self{directions};
	my $init     = $$self{init};

	#state-mapping
	my %stateName = ();
	my $i = 0;
	foreach ( values %{$nodes} ) {
		$stateName{$_} = $i;
		$i = $i + 1;
	}
	my $bitNum = Utils::calcBitNum($i);

	#input/output declarations
	my $inputs = ExtractIOStrings($directions->First->Pick);
	my $outputs = ExtractIOStrings($directions->Second->Pick);
	my $string .= qq!module synthesis\(!;
	$string .= qq!$outputs,! unless $outputs eq "";
	$string .= qq!clk!;
	$string .= qq!,$inputs! unless $inputs eq "";
	$string .= ");\n";
	$string .= qq!  input  clk!;
	$string .= qq!,$inputs! unless $inputs eq "";
	$string .= qq!;\n!;
	$string .= qq!  output $outputs;\n! unless $outputs eq "";
	
	#datatype declarations
	$string .= qq!  wire clk!;
	$string .= qq!,$outputs! unless $outputs eq "";
	$string .= qq!,$inputs! unless $inputs eq "";
	$string .= qq!;\n!;
	$string .= qq!  reg \[$bitNum\:0\] state;\n\n!;
	
	#replacement-string for the assign statements
	$string .= qq!ASSIGNMENTS\n!;
	my %assignments = ();
	
	#initial block
	$string .= qq!  initial begin\n!;
	if ($init->Size != 1) { print $string; die;} #something went wrong TODO
	my $initial = $init->Pick;
	$string .= "    state = ".$stateName{$initial}."; //".$$names{$initial}."\n";
	$string .= qq!  end\n!;

	#always block	
	$string .= qq!  always @(posedge clk) begin\n!;
	$string .= qq!    case(state)\n!;
	foreach my $node ( values %{$nodes} ) {
		$string .= qq!    $stateName{$node}: begin \/\/$$names{$node}\n!;
		my $next = $$delta{$node};
		if ($next->Size > 1) {
			#TODO
			print "Model still has ND in state ".$stateName{$node}.".\n";
		};
		my $labeledPair = $next->Pick;
		my $label = $labeledPair->First;
		AddAssignString( \%assignments, $node, $label);
		my $destSet = $labeledPair->Second;
		next if (not defined $destSet);
		die if (ref $destSet eq "Pair"); #TODO
		foreach my $dirPair ( values %{$destSet} ) {
			if ($dirPair->First->Size == 0) {
				$string .= qq!      !;
			} else {
				my $inputAssignString = $dirPair->First->ToString;
				$inputAssignString =~ s/{(.*)}/$1/;
				$inputAssignString =~ s/,/ && /g;
				$inputAssignString =~ s/=/==/g;
				$string .= qq!      if ($inputAssignString) !;
			}
			$string .= qq!state = $stateName{$dirPair->Second};\n!;
		}
		$string .= qq!    end\n!;
	}

	#generate assign-string for the output values
	my $assignString = "";
	foreach (keys %assignments) {
		$assignString .= qq!   assign $_ = !;
		my $stateSet = $assignments{$_};
		if ($stateSet->Size == 0) {
			$assignString .= qq!0;!;
		}
		foreach my $state (values %$stateSet) {
			$assignString .= qq!\(state == $stateName{$state}\)||!;
		}
		$assignString =~ s/\|\|$/;\n/;
		
	}
	#insert assign-string
	$string =~ s/ASSIGNMENTS/$assignString/;

	#end of case-, always- and module-block
	$string .= qq!    endcase\n!;
	$string .= qq!  end\n!;
	$string .= qq!endmodule \/\/synthesis\n!;
	return $string;
};

######################################################################
#
######################################################################
sub ExtractIOStrings {
	my ($dirSets,$delim) = @_;
	$delim = "," if (not defined $delim);
	
	my $str = "";
	foreach my $dir (values %$dirSets) {
		$_ = $dir->Value;
		#$_ = $dir;
	    if (/(.*)=(.*)/) {
    		$str .= $1.$delim;
	    } else {
	    	print $_." not covered\n";
		}
	}
	$str =~ s/$delim$//;
	return $str;
}

######################################################################
#
######################################################################
sub AddAssignString {
	my ($assignments, $node, $label) = @_;
	foreach my $val (values %$label) {
		$_ = $val->Value;
		if (/(.*)=1/) {
			if (defined $$assignments{$1}) {
				$$assignments{$1}->Push($node);
			} else {				
				$$assignments{$1} = Set->new($node);
			}
		} elsif (/(.*)=0/) {
			if (not defined $$assignments{$1}) {
				$$assignments{$1} = Set->new;
			}
		}
	}
}


######################################################################
# Optimize a NBT by converting it to a (transition-labeled) NBW and
# calculate direct and fair simulation minimization on it.
######################################################################
sub Optimize {
    print "Optimize strategy tree...";
    my $self = shift;
    my $buechiAL = $self->ToBuechiAL;
    $buechiAL->DirectSimulationMinimization;
    $buechiAL->FairSimulationMinimization;

    my $buechiALTree = fromBuechiAL($buechiAL, $$self{directions});
    print "done\n";
    return $buechiALTree;
}

######################################################################
# Given an NBW and an IO-Partition of the labels returns an NBT with
# the inputs-label as directions.
######################################################################
sub fromBuechiAL {
    my ($self,$partition) = @_;
    my $states= $$self{states};
    my $init  = $$self{init};
    my $delta = $$self{delta};
    my $fair  = $$self{fair};
    my $names = $$self{names};
    my $inputs = $partition->First;
    my $outputs = $partition->Second;
    my $outputSet = $outputs->DisjoinElements;
    
    my $tstates = $states->Clone;
    my $tinit   = $init->Clone;
    my $tdelta = {};
    my $tdirections = $partition;
    my $tfair = $fair->Clone;
    my $tnames = $names;

    my $outputHash = {};    
    foreach my $output (values %$outputs) {
	$$outputHash{$output} = Set->new;
    }
    foreach my $state (values %$tstates) {
	my $image = $$delta{$state};
	my $timage = Set->new;
	#print "IMAGE:".$image->ToString($names)."\n";

	foreach my $labeledPair (values %$image) {
	    my $label = $labeledPair->First;
	    my $destSet = $labeledPair->Second;
	    my $output = Set->new;
	    foreach (values %$outputs) {
		#the outputs are disjoint and only true-edges can
		#cover more then one output
		if ($_->IsIncluded($label)) {
		    $output = $_;
		}
	    }
	    $label->Subtract($outputSet);
	    if (not defined $$outputHash{$output}) {
		print "Found a TRUE-Edge\n";
		foreach (values %$outputs) {
		    $$outputHash{$_}->Push(Pair->new($label,$destSet));
		}
	    } else {
		$$outputHash{$output}->Push(Pair->new($label,$destSet));
	    }
	}

	#build new image and reset outputHash
	foreach (values %$outputs) {
	    if ($$outputHash{$_}->Size ne 0) {
		$timage->Push(Pair->new($_, $$outputHash{$_}));
		$$outputHash{$_} = Set->new;
	    }
	}

	#add image to delta
	if ($timage->Size ne 0) {
	    $$tdelta{$state} = $timage;
	    #print "NEWIMAGE:".$timage->ToString($names)."\n";
	    $timage = Set->new;
	}
    }
    my $tself = BuechiALTree->new( states => $tstates,
				   init   => $tinit,
				   delta  => $tdelta,
				   directions => $tdirections,
				   fair   => $tfair,
				   names  => $tnames);
    return $tself;

}

######################################################################
# Converts an NBT to an NBW with labels on the arcs.
######################################################################
sub ToBuechiAL {
    my $self = shift;
    my $states = $$self{states};
    my $init   = $$self{init};
    my $delta  = $$self{delta};
    my $directions = $$self{directions};
    my $inputs = $directions->First;
    my $fair   = $$self{fair};
    my $names  = $$self{names};

    my $newStates = $states->Clone;
    my $newInit = $init->Clone;
    my $newDelta  = {};
#    my $newFair = $fair->Clone;
#  We deal with FSMs only, so all states are fair
   my $newFair = Set->new;
#    my $newFair = $states->Clone;
    my $newNames = $names;
    
    foreach my $state (values %$states) {
	#print $state->ToString($names);
	my $image = $$delta{$state};
	my $newImage = Set->new;
	foreach my $labeledPair (values %$image) {
	    my $label = $labeledPair->First;
	    my $dirStateSet = $labeledPair->Second;
	    foreach my $dirStatePair (values %$dirStateSet) {
		my $dir = $dirStatePair->First;
		my $dest = $dirStatePair->Second;
		my $newLabel;
		if (ref($dir) eq "UniqSet") {
		    $dir = $dir->Set;
		}
		$newLabel = $dir->Clone;
		$newLabel = $newLabel->Union($label);
		$newImage->Push(Pair->new($newLabel, $dest));
		#print "LABEL: ".$newLabel->ToString."\n";
	    }
	}
	$$newDelta{$state} = $newImage;
    }

    my $buechiAL = BuechiAL->new( states    => $newStates,
				  init      => $newInit,
				  delta     => $newDelta,
				  fair      => $newFair,
				  names     => $newNames);
    return $buechiAL;

}


######################################################################
# Returns the number of transitions of an automaton.
######################################################################
sub NumberOfTransitions {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $transitions = 0;
    foreach my $state (values %{$states}) {
	my $image = $$delta{$state};
	foreach my $lpair (values %$image) {
	    $transitions += $lpair->Second->Size;
	}
    }
    return $transitions;

} # NumberOfTransitions

######################################################################
# Should return: (not implemented yet)
#   "terminal" if the automaton is terminal;
#   "weak"   if an automaton is weak;
#   "strong" otherwise.
######################################################################
sub Strength {
    return "unknown";
}



######################################################################
# Converts a string into an automaton.
# The string must use the format produced by ToString.
######################################################################
sub FromString {
    my %params = @_;
    my $string;
    my $vars = Set->new;
    my %partition = ();
    # The input can be either a string or a file handle.  In the former
    # case, the string is the entire automaton.  In the latter case,
    # the automaton is read as a single string from the file.
    if (defined $params{file}) {
	# Read the entire file into a single string.
	my $handle = $params{file};
	my $oldfh = select $handle;
	undef $/;
	select $oldfh;
	$string = <$handle>;
    } elsif (defined $params{string}) {
	$string = $params{string}
    } else {
	die "Specify either a file handle or a string";
    }
    # Initialize automaton components.
    my $states = Set->new;
    my $init = Set->new;
    my %delta = ();
    my %names = ();
    my %statemap = ();
    my $fair = Set->new;
    # my $count = 0;

    # The parser is an automaton with states "start," "states,"
    # "arcs," fair," and "end."
    my $state = "start";
    while (defined $string) {
	# Peel a line off the string and remove the trailing newline.
	my $line;
	($line,$string) = split(/^/m, $string, 2);
	chop $line;
	# Remove comments and trailing spaces, and skip empty lines.
	$line =~ s/\s*\#.*//;
	$line =~ s/\s+$//;
	next if $line eq "";
	#print "Line: $line \n";
	# Branch on the current state.
	if ($state eq "start") {
	    if ($line eq "States") {
		$state = "states";
	    } else {
		die "description must start with \"States\"";
	    }
	} elsif ($state eq "states") {
	    if ($line eq "Arcs") {
		$state = "arcs";
	    } else {
		unless ($line =~ s/^([\w<>\[\]\,]+):\s*//) {
		    die "missing state name";
		}
		my $name = $1;
		my $state = Buechi::BuildState($line);
		$statemap{$name} = $state;
		$names{$state} = $name;
		$states->Push($state);
		#print "State: ", $name, ": ", $state->ToString, "\n";
	    }
	} elsif ($state eq "arcs") {
	    if ($line eq "Fair Sets") {
		$state = "fair";
	    } else {
		my $initflag = 0;
		if ($line =~ s/^->//) {
		    $initflag = 1;
		}
		unless ($line =~ s/^\s*([\w<>\[\]\,]+)\s*->\s*//) {
		    die "missing state name";
		}
		my $name = $1;
		unless ($line =~ s/^{//) {
		    die "missing left brace";
		}
		unless ($line =~ s/}$//) {
		    die "missing right brace";
		}
		my @successors = SplitTransitionList($line);
		my $img = Set->new;
		foreach my $succ (@successors) {
		    unless ($succ =~ s/^\[//) {
			die "missing left bracket";
		    }
		    unless ($succ =~ s/\]$//) {
			die "missing right bracket";
		    }
		    unless ($succ =~ s/({.*}),({.*})/$2/) {
			print $succ,"\n";
			die "wrong format\n";
		    }
		    my $label = Buechi::BuildState($1);
		    #make label uniq
		    $label = UniqSet->newFromSet($label);
		    AddIO($label,2,\%partition, $vars);
		    unless ($succ =~ s/^{//) {
			die "missing left brace";
		    }
		    unless ($succ =~ s/}$//) {
			die "missing right brace";
		    }
		    my @directions = SplitTransitionList($succ);
		    my $image = Set->new;
		    foreach (@directions) {
			unless (s/^\[//) {
			    die "missing left bracket";
			}
			unless (s/\]$//) {
			    die "missing right bracket";
			}
			unless (s/,([\w<>\[\]]+)$//) {
			    die "missing succesor name";
			}
			my $succname = $1;
			my $dir = Buechi::BuildState($_);
			#make label uniq
			$dir = UniqSet->newFromSet($dir);
			AddIO($dir,1,\%partition, $vars);
			my $sstate = $statemap{$succname};
			#print "D:".$dir->ToString." ";
			#print "S:".$sstate->ToString(\%names)."\n";
			$image->Push(Pair->new($dir,$sstate));
		    }
		    $img->Push(Pair->new($label,$image));
		    #Note that if $image->Size == 0, we found the empty set,
		    #which corresponds to a transition to false/true
		}
		my $state = $statemap{$name};
		$delta{$state} = $img;
		$init->Push($state) if $initflag;
	    }
	} elsif ($state eq "fair") {
	    if ($line eq "End") {
		$state = "end";
	    } else {
		unless ($line =~ s/^{//) {
		    die "missing left brace";
		}
		unless ($line =~ s/}$//) {
		    die "missing right brace";
		}
		my @fairstates = Buechi::SplitStateList($line);
		my $fairset = Set->new;
		foreach my $fairs (@fairstates) {
		    my $fstate = $statemap{$fairs};
		    $fairset->Push($fstate);
		}
		$fair->Push($fairset);
	    }
	} else {
	    die "spurious trailing characters";
	}
    }
    my ($lettersI, $lettersO) = CoBuechiTree::MakeIOLetters($vars, \%partition);
    my $self = BuechiALTree->new(states => $states,
				 init   => $init,
				 delta  => \%delta,
				 names  => \%names,
				 fair   => $fair,
				 directions => Pair->new($lettersI, $lettersO));
    return $self;
} # FromString


sub AddIO {
    my ($keys, $value, $hash, $vars) = @_;
    foreach (values %$keys) {
	my $key = $_->Value;
	$key =~ s/=1//;
	$key =~ s/=0//;
	#print "$key -> $value\n";
	$$hash{$key} = $value;
	$vars->Push($key);
    }
}

######################################################################
# Split a comma-separated list of transtions into a list.  The state
# names may also contain commas as in [a,[b,c]].  Hence we count the
# left brackets and the commas to know when a name finishes.
######################################################################
sub SplitTransitionList {
    my $string = shift;
    my @list = ();
    while ($string ne "") {
	my $leftbrackets = 0;
	my $commas = 0;
	my $openbraces = 0;
	my $i;
	for ($i = 0; $i < length($string); $i++) {
	    my $first = substr($string,$i,1);
	    if ($openbraces == 0 and $first eq "[") {
		$leftbrackets++;
	    } elsif ($first eq "{") {
		$openbraces++;
	    } elsif ($first eq "}") {
		$openbraces--;
	    } elsif ($openbraces == 0 and $first eq ",") {
		$commas++;
		last if $commas > $leftbrackets;
	    }
	}
	push(@list,substr($string,0,$i));
	if ($i < length($string)) {
	    $string = substr($string,$i+1);
	} else {
	    $string = "";
	}
    }
    return @list;

} # SplitTransitionList



######################################################################
# DFS for the computation of the strongly connected components.
######################################################################
sub searchSCC {
    my ($self,$v,$scc,$stack,$onstack,$dfnumber,$lowlink,$countr) = @_;
    $$lowlink{$v} = $$dfnumber{$v} = $$countr;
    ${$countr}++;
    push(@{$stack},$v);
    $$onstack{$v} = 1;
    my $delta = $$self{delta};
    my $image = $$delta{$v};
    foreach my $lpair (values %{$image}) {
	my $transition = $lpair->Second;
	foreach my $dspair (values %$transition) {
	    my $w = $dspair->Second;
	    unless (exists $$dfnumber{$w}) {
		$self->searchSCC($w,$scc,$stack,$onstack,
			  $dfnumber,$lowlink,$countr);
		$$lowlink{$v} = $$lowlink{$w} if $$lowlink{$w} < $$lowlink{$v};
	    } elsif ($$dfnumber{$w} < $$dfnumber{$v} and exists $$onstack{$w}) {
		$$lowlink{$v} = $$dfnumber{$w} if $$dfnumber{$w} < $$lowlink{$v};
	    }
	}
    }
    if ($$dfnumber{$v} == $$lowlink{$v}) {
	my $x;
	my $component = Set->new;
	do {
	    $x = pop(@{$stack});
	    delete $$onstack{$x};
	    $component->Push($x);
	} while ($x ne $v);
	unshift(@$scc,$component);
    }

} # searchSCC

1;
