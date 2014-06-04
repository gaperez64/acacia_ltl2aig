#$Id: CoBuechiTree.pm,v 1.28 2007/05/31 16:53:18 bjobst Exp $

################################################################
# Functions to create and manipulate Co-Buechi-Tree automata.
#
# A CoBuechiTree automaton has the same members as a BuechiALTree
# states    => Set of STATE
# init      => Set of STATE
# delta     => Hash from STATE -> Set of TRANSITIONS
# fair      => Set of Set of STATE
# names     => Hash from STATE -> String
# directions => Pair of (Set of LABEL, Set of LABEL)
#
# Basically STATE can be any datastructure. In our application it is
# a Pair of Sets.
# A TRANSITION is a Pair of LABEL and DESTINATIONSET.
# A LABEL is a cubes over the APs stores Set of LTL and a
# DESTINATIONSET is a conjunct of direction-state-pairs stores as Set
# of Pairs of (LABEL,STATE).
#
# Meaning of delta:
# delta(q,l) = B+(D x Q), e.g. delta(q1,a=1) = (1,q1) * (2,q2)
#
# delta(q) = {}        ...FALSE
# delta(q,l) = {}      ...FALSE
# delta(q) not defined  ..TRUE
# delta(q,l) not defined..TRUE
# If delta for (q,l) and a particular direction is not defined,
# this direction leads to TRUE. It is not allowed that delta(q,l)
# for a particular direction leads to FALSE {}, because conjuncts
# with FALSE are always FALSE. So if one direction would lead to
# FALSE the whole transition delta(q,l) is redirected to FALSE.
#
# Lily - LInear Logic sYnthesize
# Author: Barbara Jobstmann <bjobst@ist.tugraz.at>
#
################################################################

package CoBuechiTree;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK $nameIndex $DEBUG);
@ISA       = qw(BuechiALTree);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
$DEBUG     = 0;
use strict;
use Set;
use Cover;
use Pair;
use UniqSet;

#$DEBUG ="UCT";

################################################################
# Make a basic CoBuechiTree structure by inheriting all members
# from BuechiALTree.
################################################################
sub new {
    my $class = shift;
    my $self = BuechiALTree->new(@_);
    bless $self, $class;
    return $self;
}

################################################################
# Convert the input Buechi automata with labels on arcs to
#              Co-Buechi universal automata.
# 
# delta(q,s) = B+(D x Q)
# delta(q1,a) = (1,q1) * (2,q2)
# 
# delta(s) = {}     ... FALSE (empty disjunction)
# delta(s,a) = {}   ... FALSE (empty disjunction)
# delta(s,a) not defined ..TRUE
# All runs leaving the automaton are accepting!
################################################################
sub fromBuechi {
	my ( $class, $buechiAL, $partition, $verb, $merge_edges ) = @_;
	my $bstates = $$buechiAL{states};
	my $binit   = $$buechiAL{init};
	my $bdelta  = $$buechiAL{delta};
	my $blabels = $$buechiAL{labels};
	my $bfair   = $$buechiAL{fair};
	my $states  = $bstates->Clone;
	my $fair    = Set->new;
	my $init    = $binit->Clone;
	my $names   = $$buechiAL{names};
	my %delta   = ();

	#we assume a single fairness conditions
	die if ($bfair->Size != 1);
	$fair->Push($bfair->Pick->Clone);
	
	my $vars = $buechiAL->ExtractInputs($bstates);
	my ($lettersI, $lettersO, $literalsI, $literalsO) = MakeIOLetters($vars, $partition);
	my $isCovered = 0;
    #Note: True and False are no states
	#my $cover = Set->new(LTL->new("TRUE"));
	#$$names{$cover} = "T";     # {{}} = TRUE
	#delta(s) = {}  #TRUE
	#delta(s,a) = {} #TRUE

	my %num = ();
	my $count = 1;
	foreach (values %$states) {
	    $num{$_} = $count;
	    $count++;
	}
	print "-- from BuechiAL to CoBuechiTree --\n" if $verb > 1;
	my $subtract = Set->new;
	foreach my $cbstate ( values %$states ) {
	    print "State:",$cbstate->ToString($names),"\n"  if ($DEBUG eq "UCT");
	    if (($cbstate->Size eq 0) && 
		($fair->Pick->IsMember($cbstate))) { #found TRUE state
		#TRUE states in the NBW will be false states in the UCT
		#we encode transitions to false with transition to the
		#empty set, so we remove the true states and redirect
		#all transitions to the empty-set
		print "Recognized ".$cbstate->ToString($names).
		  " as a true state because it is represented by the empty set.\n";
		$subtract->Push($cbstate);
		my $true = UniqSet->new;
		$delta{$cbstate} = Set->new(Pair->new($true,Set->new));
		print $delta{$cbstate}->ToString($names),"\n"  if ($DEBUG eq "UCT");
		next;
	    }
	    #print "state: " . $$names{$cbstate}, "\n";
	    my $bimage  = $$bdelta{$cbstate};
	    my $cbimage = Set->new;
	    if ($bimage->Size eq 0) {
		print "NBW has a TR to FALSE\n";
		#tr to FALSE should be turned into tr to TRUE
		#all path leaving the UCT are accepting therefore
		#we delete this tr to get a tr to TRUE
		next;
	    }
	    #Notes about the transition relation: Since Pairs are unique,
	    #forall C in delta(q,sigma) none of the elements in C are equal
	    #(if we don't merge directions)
	    #and since we build only one conjucnt for edge (output-label) none
	    #of the (label, conjunct) pairs in image are equal.
	    if ($merge_edges) {
		my $coveredLabels = Cover->new;
		foreach my $labelO ( values %$lettersO ) {
		    print "L:",$labelO->ToString($names),"\n" if ($DEBUG eq "UCT");
		    next if $coveredLabels->IsImplied($labelO);
		    my $destset = Set->new;
		    my $oLabels = Set->new;
		    my $neg = Set->new;
		    foreach (values %$labelO) {
			$neg->Push($_->Negate);
		    }
		    foreach my $blpair ( values %$bimage ) {
			print "P:",$blpair->ToString($names),"\n" if ($DEBUG eq "UCT");
			my $o =  $blpair->First->Intersection($literalsO);
			my $i =  $blpair->First->Intersection($literalsI);
			print "o:",$o->ToString," i:",$i->ToString,"\n" if ($DEBUG eq "UCT");
			my $no = $o->Intersection($neg);
			if ($no->Size == 0) {
			    #we have to check if the negation of $o is not included,
			    #e.g. if o={a=1,b=0} then we add all tr with a=0 not in tr.label
			    # and b=1 not in tr.label
			    $i = UniqSet->newFromSet($i); #make direction labels uniq
			    $destset->Push(Pair->new($i,$blpair->Second));
			    $oLabels->Add($o);
			} else {
			    foreach (values %$no) {
				$oLabels->Push($_->Negate);
			    }
			}
		    }
		    if ($destset->Size > 0) {
			$coveredLabels->Push($oLabels);
			$oLabels = UniqSet->newFromSet($oLabels);
			$cbimage->Push( Pair->new( $oLabels, $destset ) );
		    }
		}
		print "C:",$coveredLabels->ToString($names),"\n" if ($DEBUG eq "UCT");
		print $cbimage->ToString($names),"\n" if ($DEBUG eq "UCT");
		$delta{$cbstate} = $cbimage;
	    } else {
		#Note that if we don't merge labels, they are unique anyway.
		foreach my $labelO ( values %$lettersO ) {
		    $labelO = UniqSet->newFromSet($labelO);
		    #print "-- labelO: " . $labelO->ToString, "\n";
		    my $destset = Set->new;
		    foreach my $labelI ( values %$lettersI ) {
			$labelI = UniqSet->newFromSet($labelI);
			$isCovered = 0;
			#print "---- labelI: " . $labelI->ToString, "\n";
			my $label = $labelO->Union($labelI);
			foreach my $blpair ( values %$bimage ) {
			    #print "------ pair: (" . $blpair->First->ToString, ",";
			    #print $$names{ $blpair->Second }, ")\n";
			    if ($blpair->First->IsIncluded($labelO)) {
				#we are independed from the input value - TODO: optimize
			    } 
			    if ( $blpair->First->IsIncluded($label) ) {
				my $pair = Pair->new( $labelI, $blpair->Second );
				$destset->Push($pair);
				$isCovered = 1;
				#print "------ PUSH: (" . $labelI->ToString . "," . $$names{ $blpair->Second } . ")\n";
			    }
			}
			if ($isCovered == 0) {
			    print "TR of (".$$names{$cbstate}.", ".$labelO->ToString .
			      ", ".$labelI->ToString.") is TRUE\n" if $verb > 2;
			    
			    #$destset->Push(Pair->new( $labelI, $cover));
			    #$states->Push($cover); #all elements in Set are unique
			}
		    }
		    #print "D:".$destset->ToString($names)."\n";
		    $cbimage->Push( Pair->new( $labelO, $destset ) ) if $destset->Size > 0;
		    #print "PUSH TR: (" . $labelO->ToString . "," . $destset->ToString . ")\n";
		}
		$delta{$cbstate} = $cbimage;
	    } #endif  ($merge_edges)

	    #make labels unique
	}

	my $self = CoBuechiTree->new(states => $states,
				     init   => $init,
				     delta  => \%delta,
				     names  => $names,
				     fair   => $fair,
				     directions => Pair->new($lettersI,$lettersO));

# 	print "False states: ".$subtract->ToString($names)."\n";
# 	if ($init->IsIncluded($subtract)) {
# 	    print "UCT has no initial states\n";
# 	    return "";
# 	}
# 	if ($subtract->Size > 0) {
# 	    print "Remove FALSE states and replace them by FALSE transitions.\n";
# 	    $self->Subtract($subtract);
# 	}

	return  $self;
}    # new



######################################################################
# Return two sets of letters (input and output according to the given
# partition.  The letters are built from the given variables
# (with the same method as in the fct BuechiAL::Letters).
######################################################################
sub MakeIOLetters{
    my ($vars, $partition) = @_;
    my $varsI = Set->new;
    my $varsO = Set->new;
    foreach my $var (values %$vars) {
    	if (defined $$partition{$var}) {
	    	if ($$partition{$var} eq 1) {
	    		$varsI->Push($var);
			print $var." is recognized as input.\n";
	    	} elsif ($$partition{$var} eq 2) {
	    		$varsO->Push($var);
			print $var." is recognized as output.\n";
	    	} else {
	    		print "Warning: ".$var." was unknown type. Set default.\n";
			$varsO->Push($var);
			print $var." is recognized as output.\n";

	    	}
    	} else {
   			print "Warning: ".$var." was no type. Set default.\n";
			$varsO->Push($var);
			print $var." is recognized as output.\n";
    	}
    }
    my $lettersI = Set->new;
    my $literalsI = Set->new;
    my @variables  = values %$varsI;
    my @values = map 0, @variables;
    for (my $i=0; $i < 2 ** @values; $i++) {
		my $flip = 1;
		my $string = "{";
		my $separator = "";
		for (my $j=0; $j < @values; $j++) {
	    	$string .= $separator . $variables[$j] . "=" . $values[$j];
		    if ($flip) {
			$values[$j] = 1 - $values[$j];
			$flip = 0 if $values[$j];
		}
	    $separator = ",";
	}
	$string .= "}";
	my $l = Buechi::BuildState($string);
	$lettersI->Push($l);
	$literalsI = $literalsI->Union($l);
    }
    
    my $lettersO = Set->new;
    my $literalsO = Set->new;
    @variables  = values %$varsO;
    @values = map 0, @variables;
    for (my $i=0; $i < 2 ** @values; $i++) {
		my $flip = 1;
		my $string = "{";
		my $separator = "";
		for (my $j=0; $j < @values; $j++) {
	    	$string .= $separator . $variables[$j] . "=" . $values[$j];
		    if ($flip) {
			$values[$j] = 1 - $values[$j];
			$flip = 0 if $values[$j];
		}
	    $separator = ",";
	}
	$string .= "}";
	my $l = Buechi::BuildState($string);
	$lettersO->Push($l);
	$literalsO = $literalsO->Union($l);
    }
    
    return ($lettersI,$lettersO,$literalsI,$literalsO);
}


#####################################################################
# Minimizes the automaton by removing states from which the
# environment can force a path that visits alpha-states infinitely
# often. Those states fulfill  MG(true) under fairness(alpha) =
# nu Z. MX (M Z U (Z * alpha))
#####################################################################
sub LostStatesMinimization {
    my ($self,$verb) = @_;
    $verb = 1 if (not defined $verb);
    my $names = $$self{names};
    my $init  = $$self{init};
    print "-- Minimize Universal Tree Automaton --\n" if $verb > 1;

    my $win = $self->Winning;
    if ($init->IsIncluded($win)) {
	print "Lost states in the UCT..\n";
	print $win->ToString($names)."\n";
	print "Language of the UCT is empty\n";
	return "";
    }

    print "Remove lost states in the UCT..\n";
    print $win->ToString($names)."\n";
    $self->Subtract($win);
    print "Stats UCT: ", $self->Stats, "\n";
    print "Remove lost states done\n";
    
    return 1;
} #Minimization


######################################################################
# Calculate a game between the environment and the system. The env
# controlls the universality. The system controlls the transition labeling.
# The aim of the env is too force circle visiting alpha-states infinitely 
# often. Essentially this is the same as playing a game on the NBW for 
# not phi, where the env controlls the inputs and the nondeterminism. The
# system controlls the outputs (chooses the labeling).
# If the env wins the game the formula is unsatisfiable, otherwise we
# don't know. However all states in the winning region of env can be
# removed from the automaton, since the env can force plays going through 
# those states to satisfy not phi.
######################################################################
sub Winning {
    my $self = shift;

    # MG true under fairness = nu Z. MX (M Z U (Z * alpha)) with the
    # MX fct defined below.
    my $win = BuechiALTree::Winning($self);
    return $win;
}

######################################################################
# Computes MX(target), which are all states that can be forced by the
# protagonist (environment) to reach in the next step one of the
# target states or a false transition {}.
# Note: The antagonist chooses the transition and the protagonist
# chooses the direction. The universality belongs to the protagonist.
#
# All unmentioned labels leave the automaton, so states with
# unmentioned labels cannot be force to visit the target states.
######################################################################
sub MX {
    my ($self, $targetStates) = @_;
    my $states = $$self{states};
    my $init   = $$self{init};
    my $delta  = $$self{delta};
    my $directions = $$self{directions};
    my $inputs = $directions->First;
    my $names  = $$self{names};

    my $mxStates = Set->new;
  ST: foreach my $state (values %$states) {
	my $image = $$delta{$state};
	my $covered = Cover->new;
	next unless defined $image; #TRUE tr
	if ($image->Size == 0) { #FALSE tr
	    $mxStates->Push($state);
	    next;
	}
      LP: foreach my $labeledPair (values %$image) {
	    $covered->Push($labeledPair->First);
	    my $dirdestSet = $labeledPair->Second;
	    next if ($dirdestSet->Size == 0); #FALSE tr
	    foreach my $pair (values %$dirdestSet) {
		next LP if ($targetStates->IsMember($pair->Second));
	    }
	    #the transition(labeledPair) cannot be force to the target
	    next ST;
	}
	#state can be forced to $targetStates forall mentioned labels
	$covered = $covered->PrimeAndIrredundant;
	if (($covered->Size > 0) &&
	    ($covered->Pick->Size == 0)) { #all labels are covered
	    $mxStates->Push($state);
	}
    }
    return $mxStates;
}

######################################################################
# Subtract states
######################################################################
sub Subtract {
    my ($self,$subtract) = @_;
    my $states = $$self{states};
    my $delta  = $$self{delta};
    my $names  = $$self{names};
    my $init   = $$self{init};
    my $fair   = $$self{fair};
    
    $states->Subtract($subtract);
    $init->Subtract($subtract);
    foreach my $state (values %$subtract) {
	delete $$delta{$state};
	delete $$names{$state};
    }
    foreach (values %$fair) {
	$_->Subtract($subtract);
    }
    foreach my $state (values %{$states}) {
	#print "S:".$state->ToString($names)."\n";
	my $image = $$delta{$state};
	next unless defined $image; #image = true
	next if $image->Size eq 0; #image = false
	foreach my $lpair (values %{$image}) {
	    my $label = $lpair->First;
	    my $dirdestset = $lpair->Second;
	    my $dir2false = Cover->new;
	    foreach my $dirdest (values %$dirdestset) {
		if ($subtract->IsMember($dirdest->Second)) {
		    $dirdestset->Delete($dirdest);
		    $dir2false->Push($dirdest->First);
		}
	    }

	    my $false = Set->new;
	    #since we have a conjunct of dir-state-pairs, the transition
	    #leads to FALSE as soon as one direction leads to FALSE
	    if ($dir2false->Size > 0) {
		$image->Delete($lpair);
		$image->Push(Pair->new($label,$false));
	    }
	}
    }
    return $self;
}

sub CheckTypes {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $dirs = $$self{directions}->First;
    my $labels = $$self{directions}->Second;
    my $fair = $$self{fair};

    print "UCT CheckTypes ";
    die "UCT wrong state set" if ((ref($states) ne "Cover") &&
				  (ref($states) ne "Set"));
    die "UCT wrong delta" if (ref($delta) ne "HASH");
    die "UCT wrong init" if (ref($init) ne "Set");
    die "UCT wrong dirs" if (ref($dirs) ne "Set");
    die "UCT wrong labes" if (ref($labels) ne "Set");
    die "UCT wrong fair" if (ref($fair) ne "Set");

    foreach my $state (values %$states) {
	my $image = $$delta{$state};
	next unless defined $image;
	die "UCT wrong image" if (ref($image) ne "Set");
	foreach my $tr (values %$image) {
	    die "UCT wrong tr" if (ref($tr) ne "Pair");
	    my $label = $tr->First;
	    my $conjunct = $tr->Second;
	    die "UCT wrong label" if (ref($label) ne "UniqSet");
	    die "UCT wrong conjuct" if (ref($conjunct) ne "Set");
	    foreach my $ddpair (values %$conjunct) {
		die "UCT wrong ddpair" if (ref($ddpair) ne "Pair");
		my $dir = $ddpair->First;
		my $dest = $ddpair->Second;
		die "UCT wrong dir" if (ref($dir) ne "UniqSet");
		die "UCT wrong dest" if ((ref($dest) ne "Set") ||
					 not $states->IsMember($dest));
	    }
	}
    }
    print "done\n";
    return 1;
}
1;
