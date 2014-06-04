# $Id: BuechiAL.pm 2389 2008-06-19 09:09:53Z jobstman $

######################################################################
# Functions to create and manipulate Buechi automata with labels.
#                       on the arcs
# Author: Fabio Somenzi <Fabio@Colorado.EDU>
#         Sankar Gurumurthy <gurumurt@Colorado.EDU>
#
######################################################################
package BuechiAL;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK $nameIndex $DEBUG);
#@ISA       = qw(Exporter Buechi);
@ISA       = qw(Buechi); #Buechi already inherits from Exporter
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
$DEBUG = 0;
use strict;
use Set;
use Cover;
use Pair;
use LTL;


######################################################################
# Construct a new automaton.
######################################################################
sub new {
    my $class = shift;
    my %params = @_;
    # If either a file handle or a string is given, it is assumed to
    # contain the description of an automaton in the format produced
    # by ToString.  The automaton is built from this description, and
    # the remaining parameters are ignored.
    if (defined $params{file}) {
	return FromString(file => $params{file});
    } elsif (defined $params{string}) {
	return FromString(string => $params{string});
    }
    # Read parameters and supply default values as needed.
    $params{states} = Set->new unless defined($params{states});
    $params{init} = Set->new unless defined($params{init});
    $params{delta} = {} unless defined($params{delta});
    $params{fair} = Set->new unless defined($params{fair});
    $params{names} = AddNames($params{states}) unless defined($params{names});
    # Build the automaton.
    my $self = {
		states    => $params{states},
		init      => $params{init},
		delta     => $params{delta},
		fair      => $params{fair},
		names     => $params{names},
	       };
    return bless $self, $class;

} # new

#######################################################################
# Convert the input Buechi with labels on states to output buechi
# with labels on arcs
#######################################################################
sub fromBuechi{
    my ($class,$buechi) = @_;
    my $bstates = $$buechi{states};
    my $binit = $$buechi{init};
    my $bdelta = $$buechi{delta};
    my $blabels = $$buechi{labels};
    my $bfair = $$buechi{fair};
    my $states = $bstates->Clone;
#    my $fair = $bfair->Clone; #bug, we need a deep copy here
    my $init = Set->new;
    my $names = $$buechi{names};
    my %delta = ();

    my $fair = Set->new;
    foreach (values %$bfair) {
	$fair->Push($_->Clone);
    }
    # The image of a state is a set of pairs [label,successor].
    foreach my $state (values %{$states}) {
	my $bimage = $$bdelta{$state};
	my $image = Set->new;
	foreach my $succ (values %{$bimage}) {
	    my $slabel = $$blabels{$succ};
	    my $imagepair= Pair->new($slabel,$succ);
	    $image->Push($imagepair);
	}
	$delta{$state}=$image;
    }
    # If an initial state of the input automaton has the set of initial
    # states as successors, then it can be made the initial state of the
    # output automaton...
    foreach my $state (values %{$binit}) {
	my $succ = $$bdelta{$state};
	if ($succ->IsEqual($binit)) {
	    $init->Push($state);
	    last;
	}
    }
    # Otherwise, we add a new intial state with all initial states of the
    # input automaton as successors.
    if ($init->Size == 0) {
	my $initialstate = Set->new;
	my $initialimage = Set->new;
	foreach my $state (values %{$binit}) {
	   my $arc = Pair->new($$blabels{$state},$state);
	   $initialimage->Push($arc);
	}
        $states->Push($initialstate);
	$init->Push($initialstate);
	$delta{$initialstate} = $initialimage;
	$$names{$initialstate} = "init";
    }
    my $self = {
		states => $states,
		init   => $init,
		delta  => \%delta,
		names  => $names,
		fair   => $fair,
	       };
    return bless $self, $class;

} # fromBuechi


######################################################################
# Canonicalize labels of BuechiAL.
######################################################################
sub CanonicalLabelBuechi {
    my $self = shift;
    my $states = $$self{states};
    my $init = $$self{init};
    my $delta = $$self{delta};
    my $fair = $$self{fair};
    my $names = $$self{names};

    my $labels = Set->new;
    foreach my $state (values %$states) {
	my $image = $$delta{$state};
	my $newimage = Set->new;
	foreach my $lpair (values %$image) {
	    my $label = $lpair->First;
	    my $clabel = CanonicalSet($label,$labels);
	    $newimage->Push(Pair->new($clabel,$lpair->Second));
	}
	$$delta{$state} = $newimage;
    }

} # CanonicalLabelBuechi


######################################################################
# Convert to Buechi automaton with labels on states.
######################################################################
sub ToBuechi {
    my $self = shift;
    my $states = $$self{states};
    my $init = $$self{init};
    my $delta = $$self{delta};
    my $fair = $$self{fair};
    my $names = $$self{names};
    my $bstates = Set->new;
    my $binit = Set->new;
    my %bnames = ();
    my %blabels = ();
    my %bdelta = ();
    my $inverse = InvertDelta($states,$delta);
    my $fairset = $fair->Size == 1 ? $fair->Pick : undef;
    my $bfairset = Set->new;
    my $allLabels = Set->new;
    print $self->ToString,"\n";
    # Create states by splitting according to the incoming labels.
    # Also create fair set.
    foreach my $state (values %{$states}) {
	my $preimage = $$inverse{$state};
	my $labels = Set->new;
	foreach my $pair (values %$preimage) {
	    my $label = $pair->First;
	    my $clabel = CanonicalSet($label,$allLabels);
	    unless ($labels->IsMember($clabel)) {
		my $newstate = Pair->new($state,$clabel);
		$bstates->Push($newstate);
		$bfairset->Push($newstate)
		  if defined $fairset and $fairset->IsMember($state);
		$blabels{$newstate} = $clabel;
		$bnames{$newstate} = $$names{$state} . ',' . $clabel->ToString;
		$labels->Push($clabel);
	    }
	}
    }
    my $bfair = defined $fairset ? Set->new($bfairset) : Set->new;
    # Create transitions.
    foreach my $bstate (values %{$bstates}) {
	my $state = $bstate->First;
	my $image = $$delta{$state};
	my $bimage = Set->new;
	foreach my $succpair (values %{$image}) {
	    my $slabel = $succpair->First;
	    my $sstate = $succpair->Second;
	    my $clabel = CanonicalSet($slabel,$allLabels);
	    $bimage->Push(Pair->new($sstate,$clabel));
	}
	$bdelta{$bstate}=$bimage;
    }
    # Fix initial states.
    foreach my $state (values %{$init}) {
	my $image = $$delta{$state};
	foreach my $succpair (values %{$image}) {
	    my $slabel = $succpair->First;
	    my $sstate = $succpair->Second;
	    my $clabel = CanonicalSet($slabel,$allLabels);
	    $binit->Push(Pair->new($sstate,$clabel));
	}
    }
    my $buechi = Buechi->new(
			     states    => $bstates,
			     init      => $binit,
			     delta     => \%bdelta,
			     names     => \%bnames,
			     labels    => \%blabels,
			     fair      => $bfair,
		 );
    return $buechi;

} #ToBuechi


######################################################################
# Return a canonical representative of a set.
######################################################################
sub CanonicalSet {
    my ($set,$setofsets) = @_;
    foreach my $otherset (values %$setofsets) {
	if ($otherset->IsEqual($set)) {
	    return $otherset;
	}
    }
    $setofsets->Push($set);
    return $set;

} # CanonicalSet


######################################################################
# Add names to states of an automaton.
######################################################################
sub AddNames {
    my ($states,$prefix) = @_;
    $prefix = "n" unless defined($prefix);
    my %names = ();
    $nameIndex = 0;
    foreach my $state (values %{$states}) {
	$names{$state} = newName($prefix);
    }
    return  \%names;

} # AddNames


######################################################################
# Generates a new state name.  Starts from n1.
######################################################################
sub newName {
    my $prefix = shift;
    $nameIndex++;
    return "$prefix$nameIndex";

} # newName


######################################################################
# Converts a string into an automaton.
# The string must use the format produced by ToString.
######################################################################
sub FromString {
    my %params = @_;
    my $string;
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
	# print $count++, ": ", $line;
	chop $line;
	# Remove comments and trailing spaces, and skip empty lines.
	$line =~ s/\s*\#.*//;
	$line =~ s/\s+$//;
	next if $line eq "";
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
		    unless ($succ =~ s/,([\w<>\[\]]+)$//) {
			die "missing succesor name";
		    }
		    my $succname = $1;
		    my $label = Buechi::BuildState($succ);
		    my $sstate = $statemap{$succname};
		    $img->Push(Pair->new($label,$sstate));
		}
		my $state = $statemap{$name};
		die "transition empty\n" if ($img->Size == 0);
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
    my $self = BuechiAL->new(
			   states => $states,
			   init   => $init,
			   delta  => \%delta,
			   names  => \%names,
			   fair   => $fair);
    # print $self->ToString;
    return $self;

} # FromString


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
	    if ($first eq "[") {
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
# Apply direct simulation minimization to an automaton.
######################################################################
sub DirectSimulationMinimization {
    my $self = shift;
    my $states = $$self{states};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $names = $$self{names};
    my $dontcares = $$self{dontcares};

    my $inverse = InvertDelta($states,$delta);
    my $simul = $self->ComputeDirectSimulationRelation(inverse => $inverse);

    # Simplify the automaton.
    # Find direct-simulation equivalent states.
    foreach my $pair (values %{$simul}) {
	next unless $simul->IsMember($pair);
	my $p = $pair->First;
	my $q = $pair->Second;
	# Make sure neither state has been removed yet.
	next unless $states->IsMember($p) and $states->IsMember($q);
	my $swapped = Pair->new($q,$p);
	next unless $simul->IsMember($swapped);
	# Theorem applies.
	# $simul->Delete($pair,$swapped);
	# Throw away p and connect its predecessors to q.
	#print "$$names{$p} is direct-simulation equivalent to $$names{$q}\n";
	# Update inverse image of successors.
	foreach my $s (values %{$$delta{$p}}) {
	    my $slabel = $s->First;
	    my $sstate = $s->Second;
	    next if $sstate eq $p;
	    $$inverse{$sstate}->Delete(Pair->new($slabel,$p));
	}
	# Update image of predecessors.
      S: foreach my $s (values %{$$inverse{$p}}) {
	    my $slabel = $s->First;
	    my $sstate = $s->Second;
	    next if $sstate eq $p;
	    $$delta{$sstate}->Delete(Pair->new($slabel,$p));
	    $$delta{$sstate}->Push(Pair->new($slabel,$q));
	    $$inverse{$q}->Push($s);
	}
	# Update the fair sets.
	foreach my $fairset (values %{$fair}) {
	    $fairset->Delete($p);
	}
	# Remove state p from automaton.
	if ($init->IsMember($p)) {
	    $init->Delete($p);
	    $init->Push($q);
	}
	delete $$delta{$p};
	# delete $$names{$p};
	delete $$dontcares{$p};
	$states->Delete($p);
    }
    # print $self->ToString;
    # Remove arcs to direct-simulated states.
    foreach my $pair (values %{$simul}) {
	my $p = $pair->First;
	my $q = $pair->Second;
	# Make sure neither state has been removed because of
	# simulation equivalence.
	next unless $states->IsMember($p) and $states->IsMember($q);
	# Theorem applies.  Drop arcs to p from parents of both p and q.
	#print "Dropping arcs of common parents ";
	#print "of $$names{$p} and $$names{$q}\n";
	# Update image of predecessors.
	foreach my $s (values %{$$inverse{$p}}) {
	    my $slabel = $s->First;
	    my $sstate = $s->Second;
	    my $found = 0;
	    foreach my $t (values %{$$delta{$sstate}}) {
		my $tlabel = $t->First;
		my $tstate = $t->Second;
		if ($tstate eq $q and $tlabel->IsIncluded($slabel)) {
		    $found = 1;
		    last;
		}
	    }
	    next unless $found;
	    #print "Dropping arc from $$names{$sstate} to $$names{$p}";
	    #print " with label ", $slabel->ToString, "\n";
	    $$delta{$sstate}->Delete(Pair->new($slabel,$p));
	    $$inverse{$p}->Delete($s);
	}
	# Remove state p from initial states if q is initial.
	if ($init->IsMember($q) and $init->IsMember($p)) {
	    $init->Delete($p);
	   # print "Removing $$names{$p} from the initial states\n"; #diag
	}
    }
    $self->MergeTransitions;

    # print $self->ToString;

} # DirectSimulationMinimization

######################################################################
# Apply fair simulation minimization to an automaton.
######################################################################
sub FairSimulationMinimization {
    my $self = shift;
  #  open(RR,"ratios");
  #  my $l=<RR>;
  #  chomp($l);
  #  my @a=split(/ /,$l);
  #  my $totalmerge = 0;
  #  my $mergeaccept = 0;
  #  my $totalarc = 0;
  #  my $arcaccept = 0;
     my $fair = $$self{fair};
    # Currently we can only deal with one fairness condition.  If there are
    # no fair sets, fair simulation minimization will do nothing.
    return unless $fair->Size == 1;
    $self->CanonicalLabelBuechi;
    my $safety = $self->SafetySimulationRelation;
    print "Safety simulation sans identity: {[simulated,simulating],...}\n",
      $self->StateRelationToNameString($safety), "\n" if $DEBUG >0;
    # There is nothing to be gained by attempting fair simulation
    # minimization unless the safety simulation relation is a proper
    # superset of the identity.
    return if $safety->Size == 0;
    my $game = Game->newAL($self, $safety);
   #  open(FP,">Game.dot");
#     print FP $game->ToDot("game");
#     close(FP);
    my $time = 0;
    my $gstates = $$game{states};
    if ($DEBUG > 0) {
	print "Game graph\n", $game->ToString, "End game graph\n";
	my $Wa = $$game{astates};
	print "Wa: ", $game->StateRelationToNameString($Wa), "\n";
	if ($DEBUG > 2) {
	    print $game->ToDot("game graph");
	    my $Wp = $gstates->Difference($Wa);
	    print "Wp: ", $game->StateRelationToNameString($Wp), "\n";
	}
    }
    my $gdelta = $$game{delta};
    my $priority = $$game{priority};
    my $seeds = Set->new;
    foreach my $gstate (values %{$gstates}) {
	if ($$priority{$gstate} == 1) {
	    $seeds->Push($gstate);
	}
    }
    my $winningstates = $game->lift($seeds->Clone);
    print $game->ToDot("parity game") if $DEBUG > 0;
    print "Winning states: ", $game->StateRelationToNameString($winningstates),
      "\n" if $DEBUG > 1;
    my $fairsim = Set->new;
    foreach my $winnings (values %{$winningstates}) {
	my $pair = $winnings->Second;
	$fairsim->Push($pair) unless $pair->First eq $pair->Second;
    }
    print "Fair simulation sans identity: {[simulated,simulating],...}\n",
      $self->StateRelationToNameString($fairsim), "\n" if $DEBUG > 0;
    # Minimize the automaton.
    my $states = $$self{states};
    my $init = $$self{init};
    my $delta = $$self{delta};
    my $names = $$self{names};
    my $inverse = InvertDelta($states,$delta);
    # Find fair-simulation equivalent states.
    my $checked = Set->new;
    foreach my $pair (values %{$fairsim}) {
#	next unless $fairsim->IsMember($pair);
	next if  $checked->IsMember($pair);
	my ($anti,$proto) = ($pair->First,$pair->Second);
	print "Checking fair-simulation equivalent states ", $anti->ToString,
	  ", ", $proto->ToString, "\n" if $DEBUG > 1;
	# Make sure neither state has been removed yet.
	next unless $states->IsMember($anti) and $states->IsMember($proto);
	my $swapped = Pair->new($proto,$anti);
	next unless $fairsim->IsMember($swapped);
	$checked->Push($swapped);
    }
    print "The fair simulation equivalent states are : ", $checked->ToString,
          "\n" if $DEBUG > 0;
    my $removals = Set->new;
    my $mergedStates = 0;
    my $step = 0;
    foreach my $pair (values %{$checked}) {
	my ($anti,$proto) = ($pair->First,$pair->Second);
	my $additions = Set->new;
	# Make sure neither state has been removed yet.
	next unless $states->IsMember($anti) and $states->IsMember($proto);
	if ($DEBUG >0) {
	    print "Checking the collapsing of fair equivalent states ",
	      "$$names{$anti} and $$names{$proto}\n";
	}
	ALOOP:foreach my $predpair (values %{$$inverse{$anti}}) {
	    my $pred  = $predpair->Second;
	    next unless $states->IsMember($pred);
	    foreach my $lpair (values %{$$delta{$pred}}) {
		next unless $lpair->First->IsIncluded($predpair->First);
		next ALOOP if $proto eq $lpair->Second;
	    }
	    my $arc = Pair->new($pred,$proto);
	    $additions->Push(Pair->new($predpair->First,$arc));
	}
	BLOOP: foreach my $predpair (values %{$$inverse{$proto}}) {
	    my $pred  = $predpair->Second;
	    next unless $states->IsMember($pred);
	    foreach my $lpair (values %{$$delta{$pred}}) {
		next unless $predpair->First->IsIncluded($lpair->First);
		next BLOOP if $anti eq $lpair->Second;
	    }
	    my $arc = Pair->new($pred,$anti);
	    $additions->Push(Pair->new($predpair->First,$arc));
	}
	CLOOP: foreach my $succpair (values %{$$delta{$proto}}) {
	    my $succ  = $succpair->Second;
	    next unless $states->IsMember($succ);
	    foreach my $lpair (values %{$$inverse{$succ}}) {
		next unless $succpair->First->IsIncluded($lpair->First);
		next CLOOP if $anti eq $lpair->Second;
	    }
	    my $arc = Pair->new($anti,$succ);
	    $additions->Push(Pair->new($succpair->First,$arc));
	}
	DLOOP: foreach my $succpair (values %{$$delta{$anti}}) {
	    my $succ  = $succpair->Second;
	    next unless $states->IsMember($succ);
	    foreach my $lpair (values %{$$inverse{$succ}}) {
		next unless $lpair->First->IsIncluded($succpair->First);
		next DLOOP if $proto eq $lpair->Second;
	    }
	    my $arc = Pair->new($proto,$succ);
	    $additions->Push(Pair->new($succpair->First,$arc));
	}
	my $newfstate = undef;
	foreach my $fairset (values %{$fair}) {
	    if (not $fairset->IsMember($proto) and $fairset->IsMember($anti)) {
		$newfstate = $proto;
	    }
	    if (not $fairset->IsMember($anti) and $fairset->IsMember($proto)) {
		$newfstate = $anti;
	    }
	}
	my $clone = $game->Clone;
	#totalmerge++;
	print "Additions: ", $additions->ToString, "\n" if $DEBUG > 1;
	my $changes = $clone->UpdateAL($self, $removals, $additions, newfair => $newfstate);
	$step++;
	# open(FP,">Game$step.dot");
# 	print FP $clone->ToDot("Game$step");
# 	close(FP);
	my $winningstates = $clone->lift($changes);
	print "Merging check:\n", $clone->ToString, "\n" if $DEBUG > 2;
	print $clone->ToDot("merging check"), "\n" if $DEBUG > 0;
	next unless $clone->AcceptChange($self, $winningstates);
	#print $winningstates->ToString,"\n";
	#print "accepted\n";
	#mergeaccept++;
	my $retained = $proto;
	my $removed  = $anti;
	print "Removed: ", $removed->ToString, "\n" if $DEBUG > 1;
	# This works for non-generalized Buechi automata.
	foreach my $fairset (values %{$fair}) {
	    if (not $fairset->IsMember($proto) and $fairset->IsMember($anti)) {
		$retained = $anti;
		$removed = $proto;
	    }
	}
	print "Removed: ", $removed->ToString, "\n" if $DEBUG > 1;
	$mergedStates++;
	if ($DEBUG > 0) {
	    print "Merging the states ", $proto->ToString, " and ",
	      $anti->ToString, "\n";
	}
	foreach my $succpair (values %{$$delta{$removed}}) {
	    my $slabel = $succpair->First;
	    my $succ = $succpair->Second;
	    next if $succ eq $removed;
	    $$inverse{$succ}->Delete(Pair->new($slabel,$removed));
	    $$inverse{$succ}->Push(Pair->new($slabel,$retained));
	    $$delta{$retained}->Push(Pair->new($slabel,$succ));
	}
	foreach my $predpair (values %{$$inverse{$removed}}) {
	    my $plabel = $predpair->First;
	    my $pred = $predpair->Second;
	    next if $pred eq $removed;
	    $$delta{$pred}->Delete(Pair->new($plabel,$removed));
	    $$delta{$pred}->Push(Pair->new($plabel,$retained));
	    $$inverse{$retained}->Push(Pair->new($plabel,$pred));
	}
	# Update the fair sets.
	foreach my $fairset (values %{$fair}) {
	    $fairset->Delete($removed);
	}
	# Remove state removed from automaton.
	if ($init->IsMember($removed)) {
	    $init->Delete($removed);
	    $init->Push($retained);
	}
	delete $$delta{$removed};
#	delete $$labels{$removed};
#	delete $$names{$removed};#causes an error in Game graph
#	delete $$dontcares{$removed};
	$states->Delete($removed);
	$game = $clone;
    }
    print "After merging equivalent states: \n", $self->ToString, "\n"
      if $DEBUG > 1;
    # Regenerate game automaton if something changed.
    if ($mergedStates > 0) {
	foreach my $pair (values %{$safety}) {
	    my ($anti, $proto) = ($pair->First, $pair->Second);
		    unless ($states->IsMember($anti) and $states->IsMember($proto)) {
		$safety->Delete($pair);
	    }
	}
	$game = Game->newAL($self,$safety,allLabels => $$game{allLabels});
	$seeds->Restrict($$game{states});
	#print $seeds->ToString, "\n";
	$game->lift($seeds);
    }
    # Remove arcs to fair-simulated states.
    my $additions = Set->new;
   #  open(FP,">selfarc.dot");
#      print FP $self->ToDot("selfarc");
#     close(FP);
#     open(FP,">gamearc.dot");
#      print FP $game->ToDot("gamearc");
#     close(FP);
    my $arcm= 0;
    foreach my $pair (values %{$fairsim}) {
	my ($anti,$proto) = ($pair->First,$pair->Second);
	# Make sure neither state has been removed because of
	# simulation equivalence.
	next unless $states->IsMember($anti) and $states->IsMember($proto);
	if ($DEBUG > 0) {
	    print "Dropping arcs of common parents ";
	    print "of $$names{$anti} and $$names{$proto}\n";
	}
	my $remi = Set->new;
	foreach my $spair (values %{$$inverse{$anti}}) {
	    my $sl = $spair->First;
	    my $s = $spair->Second;
	    my $flag = 0;
	    foreach my $lpair (values %{$$delta{$s}}) {
		next unless $lpair->First->IsIncluded($sl);
		$flag = 1 if $lpair->Second eq $proto;
	    }
	    next unless $flag;
	    if ($DEBUG > 0) {
		print "Checking arc from $$names{$s} to $$names{$anti}\n";
	    }
	    my $clone = $game->Clone;
	   #$totalarc++;
	    my $arc = Pair->new($s, $anti);
	    my $removals = Set->new($arc);
         #   print "Removals: ",$removals->ToString,"\n";
	    my $changes = $clone->UpdateAL($self, $removals, $additions);
            $arcm++;
           #  open(FP,">gamearc$arcm.dot");
#      	    print FP $clone->ToDot("gamearc$arcm");
#             close(FP);
	    my $winningstates = $clone->lift($changes);
	    if ($DEBUG > 1) {
		print $clone->ToDot("game-" . $time), "\n",
		  "winning states: ", $winningstates->ToString, "\n";
	    }
	    next unless $clone->AcceptChange($self, $winningstates);
	  #  print $winningstates->ToString,"\n";
	   #$arcaccept++;
	    if ($DEBUG > 0) {
		print "Dropping arc from $$names{$s} to $$names{$anti}\n";
	    }
	    $$delta{$s}->Delete(Pair->new($sl,$anti));
	    $remi->Push($spair);
	    $game = $clone;
	    $time++;
	}
	$$inverse{$anti}->Subtract($remi);
	# Remove state p from initial states if q is initial.
	$init->Delete($anti) if $init->IsMember($proto);
    }
    #a[0]+=$totalmerge;
    #a[1]+=$mergeaccept;
    #a[2]+=$totalarc;
    #a[3]+=$arcaccept;
    #close(RR);
    #open(RR,">ratios");
    #print RR "$a[0] $a[1] $a[2] $a[3]\n";
    #close(RR);
    if ($DEBUG > 0) {
	print $self->ToString;
    }

} # FairSimulationMinimization


######################################################################
# Compute the set of pairs (p,q) such that q simulates p and is
# distinct from it.
######################################################################
sub ComputeDirectSimulationRelation {
    my $self = shift;
    my %params = @_;
    my $states = $$self{states};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $names = $$self{names};
    my $inverse;
    if (defined $params{inverse}) {
	$inverse = $params{inverse};
    } else {
	$inverse = InvertDelta($states,$delta);
    }
    my $forbidden;
    if (defined $params{forbidden}) {
	$forbidden = $params{forbidden};
    } else {
	$forbidden = {};
    }
    # Initialize the direct simulation relation to all pairs (p,q)
    # that satisfy:
    # 0. p != q
    # 2. for each f in F, p in f -> q in f
    # Also, push all pairs in the simulation relation onto a queue.
    my $simul = Set->new;
    my @queue = ();
    my %enqueued = ();
  FIRST: foreach my $p (values %{$states}) {
      SECOND: foreach my $q (values %{$states}) {
	    next SECOND if $p eq $q;
	    foreach my $fairset (values %{$fair}) {
		if ($fairset->IsMember($p)) {
		    next SECOND unless $fairset->IsMember($q);
		}
	    }
	    my $pair = Pair->new($p,$q);
	    $simul->Push($pair);
	    push(@queue, $pair);
	    $enqueued{$pair} = 1;
	}
    }
#     print "Direct simulation relation initially contains ",
#       $simul->Size, " pairs\n";
#     foreach my $pair (values %{$simul}) {
# 	print $$names{$pair->First}, " is direct simulated by ",
# 	  $$names{$pair->Second}, "\n";
#     }
    # Compute the greatest fixpoint.
  PAIRS: while (@queue > 0) {
	my $pair = pop(@queue);
	delete $enqueued{$pair};
	my $p = $pair->First;
	my $q = $pair->Second;
	my $nogoodp = defined $$forbidden{$p} ? $$forbidden{$p} : Set->new;
	my $nogoodq = defined $$forbidden{$q} ? $$forbidden{$q} : Set->new;
#	print "Pair: $$names{$p} simulated by $$names{$q}"; #diag
      PLOOP: foreach my $s (values %{$$delta{$p}}) {
	    next PLOOP if $nogoodp->IsMember($s);
	    my $slabel = $s->First;
	    my $sstate = $s->Second;
	    #BJ: Cover over multiple edges
	    #Since we represent edges as cubes, we may get that a single
            #edge labeled with a cube is simulated by two or more other 
            #edges, so we compute the union over all labels belonging to a
            #'good' edge and see if we can cover our target label ($slabel)
# 	    my $cover = Cover->new;
	    # Negate label of target edge (represented as cube)
# 	    foreach my $literal (values %$slabel) {
# 		my $negSet = Set->new($literal->Negate);
# 		$cover->Push($negSet);
# 	    }
	    foreach my $t (values %{$$delta{$q}}) {
		next if $nogoodq->IsMember($s);
		my $tlabel = $t->First;
		my $tstate = $t->Second;
 		if ($tlabel->IsIncluded($slabel)) {
 		    next PLOOP if $sstate eq $tstate;
 		    next PLOOP if $simul->IsMember(Pair->new($sstate,$tstate));
		}
#  		} else {
# 		    #BJ: Cover over multiple edges
# 		    if (($sstate eq $tstate ) || 
# 			($simul->IsMember(Pair->new($sstate,$tstate)))) {
# 			$cover->Push($tlabel);
# 		    }
# 		}
	    }	    
# 	    #BJ: Cover over multiple edges
# 	    $cover = $cover->PrimeAndIrredundant;
# 	    next PLOOP if ($cover->Size == 1 && $cover->Pick->Size == 0);

	    $simul->Delete($pair);
	    # Enqueue perturbed pairs.
	    foreach my $u (values %{$$inverse{$p}}) {
		my $ulabel = $u->First;
		my $ustate = $u->Second;
		foreach my $v (values %{$$inverse{$q}}) {
		    my $vlabel = $v->First;
		    next unless $vlabel->IsIncluded($ulabel);
		    my $vstate = $v->Second;
		    my $newpair = Pair->new($ustate,$vstate);
		    if ($simul->IsMember($newpair)) {
			unless (exists $enqueued{$newpair}) {
			    push(@queue,$newpair);
			    $enqueued{$newpair} = 1;
			}
		    }
		}
	    }
#	    print " removed\n"; #diag
	    next PAIRS;
	}
#	print " retained\n"; #diag
    }
#     print "Direct simulation relation contains ", $simul->Size,
#       " pairs\n"; #diag
    # return $simul unless $simul->Size > 0;
    #print "Direct simulation sans identity: {[simulated,simulating],...}\n",
   #   $self->StateRelationToNameString($simul), "\n"; # diag

    return $simul;

} # ComputeDirectSimulationRelation


######################################################################
# Compute the set of pairs (p,q) such that q simulates p and is
# distinct from it.
######################################################################
sub SafetySimulationRelation{
    my $self = shift;
    my %params = @_;
    my $states = $$self{states};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $names = $$self{names};
    my $inverse;
    if (defined $params{inverse}) {
	$inverse = $params{inverse};
    } else {
	$inverse = InvertDelta($states,$delta);
    }
    my $forbidden;
    if (defined $params{forbidden}) {
	$forbidden = $params{forbidden};
    } else {
	$forbidden = {};
    }
    # Initialize the direct simulation relation to all pairs (p,q)
    # that satisfy p != q
    # Also, push all pairs in the simulation relation onto a queue.
    my $simul = Set->new;
    my @queue = ();
    my %enqueued = ();
  FIRST: foreach my $p (values %{$states}) {
      SECOND: foreach my $q (values %{$states}) {
	    next SECOND if $p eq $q;
	    my $pair = Pair->new($p,$q);
	    $simul->Push($pair);
	    push(@queue, $pair);
	    $enqueued{$pair} = 1;
	}
    }
#     print "Direct simulation relation initially contains ",
#       $simul->Size, " pairs\n";
#     foreach my $pair (values %{$simul}) {
# 	print $$names{$pair->First}, " is direct simulated by ",
# 	  $$names{$pair->Second}, "\n";
#     }
    # Compute the greatest fixpoint.
  PAIRS: while (@queue > 0) {
	my $pair = pop(@queue);
	delete $enqueued{$pair};
	my $p = $pair->First;
	my $q = $pair->Second;
	my $nogoodp = defined $$forbidden{$p} ? $$forbidden{$p} : Set->new;
	my $nogoodq = defined $$forbidden{$q} ? $$forbidden{$q} : Set->new;
	# print "Pair: $$names{$p} simulated by $$names{$q}"; #diag
      PLOOP: foreach my $s (values %{$$delta{$p}}) {
	    next PLOOP if $nogoodp->IsMember($s);
	    my $slabel = $s->First;
	    my $sstate = $s->Second;
	    foreach my $t (values %{$$delta{$q}}) {
		next if $nogoodq->IsMember($s);
		my $tlabel = $t->First;
		my $tstate = $t->Second;
		if ($tlabel->IsIncluded($slabel)) {
		    next PLOOP if $sstate eq $tstate;
		    next PLOOP if $simul->IsMember(Pair->new($sstate,$tstate));
		}
	    }
	    $simul->Delete($pair);
	    # Enqueue perturbed pairs.
	    foreach my $u (values %{$$inverse{$p}}) {
		my $ulabel = $u->First;
		my $ustate = $u->Second;
		foreach my $v (values %{$$inverse{$q}}) {
		    my $vlabel = $v->First;
		    next unless $vlabel->IsIncluded($ulabel);
		    my $vstate = $v->Second;
		    my $newpair = Pair->new($ustate,$vstate);
		    if ($simul->IsMember($newpair)) {
			unless (exists $enqueued{$newpair}) {
			    push(@queue,$newpair);
			    $enqueued{$newpair} = 1;
			}
		    }
		}
	    }
	    # print " removed\n"; #diag
	    next PAIRS;
	}
	# print " retained\n"; #diag
    }
    #print "Direct simulation relation contains ", $simul->Size,
     # " pairs\n"; #diag
    # return $simul unless $simul->Size > 0;
    #print "Direct simulation sans identity: {[simulated,simulating],...}\n",
   #   $self->StateRelationToNameString($simul), "\n"; # diag

    return $simul;

} # SafetySimulationRelation


######################################################################
# Computes the inverse of delta.
######################################################################
sub InvertDelta {
    my ($states,$delta) = @_;
    my %inverse = ();
    foreach my $state (keys %{$states}) {
	$inverse{$state} = Set->new;
    }
    foreach my $state (values %{$states}) {
	my $image = $$delta{$state};
	foreach my $succpair (values %{$image}) {
	    my $slabel = $succpair->First;
	    my $sstate = $succpair->Second;
	    $inverse{$sstate}->Push(Pair->new($slabel,$state));
	}
    }
    return \%inverse;

} # InvertDelta


######################################################################
# Merge transitions from the same source to the same destination
# with different labels.
######################################################################
sub MergeTransitions {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $names = $$self{names};
    foreach my $state (values %{$states}) {
	my $oldimg = $$delta{$state};
	my $newimg = Set->new;
	my %toLabels = ();
	my $destinations = Set->new;
	foreach my $pair (values %{$oldimg}) {
	    my $label = $pair->First;
	    my $dest = $pair->Second;
	    unless (defined $toLabels{$dest}) {
		$toLabels{$dest} = Cover->new;
	    }
	    $toLabels{$dest}->Push($label);
	    $destinations->Push($dest);
	}
	foreach my $dest (values %{$destinations}) {
	    my $picover = $toLabels{$dest}->PrimeAndIrredundant;
#	    print $$names{$state}, " - ",  $picover->ToString, " -> ",
#	      $$names{$dest}, "\n"; # diag
	    foreach my $label (values %{$picover}) {
		$newimg->Push(Pair->new($label,$dest));
	    }
	}
	$$delta{$state} = $newimg;
    }
} # MergeTransitions


######################################################################
# Minimization technique devised especially for "layered" weak automata.
#  1. Make all states simulated by an initial state initial.
#  2. Process accepting SCCs in topological order from sources to sinks.
#  3. Remove arcs out of SCC and compute simulation relation for result.
#  4. If initial states with path to SCC are simulated by initial states
#     without a path to the SCC, make SCC non-accepting.
#  5. Minimize automaton if any SCC was made non-accepting.
# We rely on the fact that direct simulation minimization removes from
# the initial states a state that is simulated by another initial state.
# Hence, we should end up with only one initial state if we started with
# one.
######################################################################
sub ReduceHeight {
    # Unpack.
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $fair = $$self{fair};
    # Compute simulation relation for original automaton and
    # make all states simulated by an initial state initial.
    my $inverse = InvertDelta($states,$delta);
    my $simul = $self->ComputeDirectSimulationRelation(inverse => $inverse);
    foreach my $pair (values %{$simul}) {
	$init->Push($pair->First) if $init->IsMember($pair->Second);
    }
    #print "augmented init ", $self->StateRelationToNameString($init), "\n";
    # Compute SCC quotient graph.
    my ($SCCs,$SCClist) = $self->SCC;
    # print "made it here\n";
    my $quotient = $self->Quotient($SCCs);
   #print $quotient->ToString;
    my $qfair = $$quotient{fair}->Pick;
    # print "fair SCCs: ", $quotient->StateRelationToNameString($qfair),
    #   "\n"; #diag
    my $demotions = 0;
    # $SCClist contains the SCCs in topological order from sources to sinks.
    foreach my $scc (@{$SCClist}) {
	next if (defined $qfair and (not($qfair->IsMember($scc))));
	#print "Examining fair SCC: ", $self->StateRelationToNameString($scc),
	 # "\n"; # diag
	# Check if this SCC can be demoted.  This is the case if every
	# word with an accepting run that eventually dwells in the SCC
	# also has an accepting run that does not dwell in the SCC.  A
	# sufficient condition is that, when the forbidden transitions
	# are excluded, every initial state with a path to the SCC is
	# simulated by an initial state with no path to the SCC.

	# Collect transitions out of SCC.
	my $forbidden = {};
	my $fcount = 0;
	foreach my $state (values %{$scc}) {
	    $$forbidden{$state} = Set->new;
	    my $transitions = $$delta{$state};
	    foreach my $trans (values %{$transitions}) {
		my $dest = $trans->Second;
		unless ($scc->IsMember($dest)) {
		    $$forbidden{$state}->Push($trans);
		    $fcount++;
		}
	    }
	}
	next unless $fcount > 0;
	# Diagnostic prints.
	# foreach my $state (values %{$scc}) {
# 	    my $transitions = $$forbidden{$state};
# 	    foreach my $trans (values %{$transitions}) {
# 		print "forbidden transition: ", $state->ToString, " -> ",
# 		  $trans->ToString, "\n";
# 	    }
# 	}
	# Should we add the "forbidden" option to InvertDelta?
	my $newsimul =
	  $self->ComputeDirectSimulationRelation(inverse => $inverse,
						 forbidden => $forbidden);
	# Separate initial states into those with path to SCC and
	# those without.
	my $backr = Reachable($scc,$inverse);
	my $backi = $backr->Intersection($init);
	my $otheri = $init->Difference($backi);
	#print "Backward reachable/other initial states: ",
	 # $self->StateRelationToNameString($backi), " / ",
	  #$self->StateRelationToNameString($otheri), "\n"; #diag
	# See if all initial states with a path to SCC are simulated
	# by some other initial state.  If so, make SCC non-accepting.
	foreach my $pair (values %{$newsimul}) {
	    my $p = $pair->First;
	    next unless $backi->IsMember($p);
	    my $q = $pair->Second;
	    next unless $otheri->IsMember($q);
	    $backi->Delete($p);
	    last if $backi->Size == 0;
	}
	if ($backi->Size == 0) {
	    #print "demote SCC\n";
	    $demotions++;
	    foreach my $fairset (values %{$fair}) {
		$fairset->Subtract($scc);
	    }
	}
    }
    if ($demotions > 0) {
	$self->DirectSimulationMinimization;
	$self->PruneUnreachable;
	# We should not have to explicitly return to one initial state.
	# Until we prove this is indeed the case, we check.
	if ($init->Size != 1) {
	    #print "Warning: multiple initial states\n";
	}
    }

} # ReduceHeight


######################################################################
# Remove states that cannot reach all fair sets and perform other
# simplifications of the automaton.
######################################################################
sub Prune {
    my $self = shift;
    my $states = $$self{states};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
   # my $labels = $$self{labels};
    my $names = $$self{names};
    my $oldstates = $states->Clone;

    # Eliminate redundant transitions from the predecessors of
    # universal states.  A universal state is a state with a TRUE
    # label snd a self-loop; it must belong to all fair sets.
    foreach my $state (values %{$states}) {
	my $flag = 0;
	foreach my $lpair (values %{$$delta{$state}}) {
	    if (($lpair->First->Size == 0) && ($lpair->Second eq $state)) {
		$flag = 1;
		#print $state->ToString,"  ",$lpair->ToString,"\n";
		last;
	    }
	}
	if ($flag) {
	    my $accept = 1;
	    foreach my $fairset (values %{$fair}) {
		unless ($fairset->IsMember($state)) {
		    $accept = 0;
		    last;
		}
	    }
	    next unless $accept;
	    # Universal state.  Remove transitions from its predecessors
	    # to other states because they are redundant.
	    foreach my $s (values %{$states}) {
		my $nflag = 0;
		my $clabelset = Set->new;
		foreach my $lpair (values %{$$delta{$s}}) {
		    if ($lpair->Second eq $state) {
			$nflag = 1;
			$clabelset->Push($lpair->First);
		    }
		}
		next unless $nflag;
	      TLOOP:foreach my $t (values %{$$delta{$s}}) {
		    unless ($t->Second eq $state) {
			foreach my $label (values %{$clabelset}) {
			    if ($label->IsIncluded($t->First)) {
				$$delta{$s}->Delete($t);
				next TLOOP;
			    }
			}
		    }
		}
	    }
	}
    }
    # Build SCC quotient graph to be used in subsequent pruning steps.
    my $quotient = $self->Quotient($self->SCC);
    my $classes = $$quotient{states};
    my $deltaQ = $$quotient{delta};

    # Mark as don't cares states that have no cycles going through them.
    $$self{dontcares} = {};
    my $dontcares = $$self{dontcares};
    foreach my $class (values %{$classes}) {
	unless ($class->Size > 1) {
	    my $state = $class->Pick; # only one state
	    my $flag = 0;
	    foreach my $lpair (values %{$$delta{$state}}) {
		if ($lpair->Second eq $state) {
		    $flag = 1;
		}
	    }
	    unless ($flag) {
		$$dontcares{$state} = 1;
	    }
	}
    }

    # Restrict automaton to those states that can reach a fair cycle.
    if ($$quotient{fair}->Size > 0) { # not all states accepting
	# Find states that are on fair cycles.
	my $fairstates = Set->new; # merge all fair SCCs
	my $fairQ = $$quotient{fair}->Pick; # only one element
	foreach my $class (values %{$fairQ}) {
	    $fairstates->Add($class);
	}
	# Shrink fair sets.
	foreach my $fairset (values %{$fair}) {
	    $fairset->Restrict($fairstates);
	}
	# Find states that can reach a fair cycle.
	my $inverse = Buechi::InvertDelta($classes,$deltaQ);
	my $rclasses = Buechi::Reachable($fairQ,$inverse);
	my $reach = Set->new;
	foreach my $class (values %{$rclasses}) {
	    $reach->Add($class);
	}
	$init->Restrict($reach);
	$states->Restrict($reach);
	foreach my $state (values %{$states}) {
	    my $rem = Set->new;
	    foreach my $lpair (values %{$$delta{$state}}) {
		unless ($states->IsMember($lpair->Second)) {
		    $rem->Push($lpair);
		}
	    }
	    $$delta{$state}->Subtract($rem);
	}
    } else { # all states are accepting
	# Here we rely on the fact that the quotient is restricted to
	# the reachable part of the automaton.
	my $reachable = Set->new;
	foreach my $class (values %{$classes}) {
	    $reachable->Add($class);
	}
	$init->Restrict($reachable);
	$states->Restrict($reachable);
	foreach my $fairset(values %{$fair}) {
	    $fairset->Restrict($reachable);
	}
    }

    # Clean up.
    # Discard states that have been dropped.
    foreach my $state (values %{$oldstates}) {
	unless ($states->IsMember($state)) {
	    delete $$delta{$state};
	    #delete $$labels{$state};
	    delete $$names{$state};
	    delete $$dontcares{$state} if exists $$dontcares{$state};
	}
    }
    # Update quotient by discarding states that have been dropped.
    foreach my $class (values %{$classes}) {
	foreach my $state (values %{$class}) {
	    $class->Delete($state) unless $states->IsMember($state);
	}
    }

    # Discard duplicate fair sets and fair sets including all states.
    # Here we also restrict fair sets by analyzing each SCC.  If,
    # within an SCC, a fair set dominates another, it can be
    # restricted to the dominated one.  As a special case, if an SCC
    # does not intersect all fair sets, its states are removed from
    # all fair sets.
    foreach my $fairset (values %{$fair}) {
	# Eliminate fair set if it includes all states.
	if ($fairset->IsEqual($states)) {
	    $fair->Delete($fairset);
	    next;
	}
	# Shrink the fair set inside an SCC if there is another fair
	# set that is contained in it when both fair sets are
	# restricted to the SCC.
	foreach my $scc (values %{$classes}) {
	    foreach my $otherset (values %{$fair}) {
		my $i1 = $fairset->Intersection($scc);
		my $i2 = $otherset->Intersection($scc);
		if ($i2->Size < $i1->Size && $i2->IsIncluded($i1)) {
		    $fairset->Subtract($scc->Difference($i2));
		}
	    }
	}
	# Remove fair set if another fair set is (globally) contained in it.
	foreach my $otherset (values %{$fair}) {
	    unless ($fairset eq $otherset) {
		if ($otherset->IsIncluded($fairset)) {
		    $fair->Delete($fairset);
		    last;
		}
	    }
	}
    }

    # If an SCC is a clique, and there is a state s whose label
    # exactly matches the GLB of all the labels of the clique, we can
    # remove s from every fair set such that it contains at least
    # another state of the SCC besides s.
    # foreach my $class (values %{$classes}) {
# 	next unless $class->Size > 1;
# 	next unless $self->IsClique($class);
# 	my ($glb,$least) = $self->labelGLB($class);
# 	next unless defined($least);
# 	my $rest = $class->Clone;
# 	$rest->Delete($least);
# 	foreach my $fairset (values %{$fair}) {
# 	    if ($fairset->IsMember($least)) {
# 		unless ($fairset->IsDisjoint($rest)) {
# 		    $fairset->Delete($least);
# 		}
# 	    }
# 	}
#     }

    # If an SCC contains a state s that simulates all the other states
    # in the same SCC (both forward and backward), then all states of
    # the SCC except s can be removed from all fair sets.
    # The following code checks for a special case of this theorem.
#     foreach my $class (values %{$classes}) {
# 	next unless $class->Size > 1;
# 	my ($lub,$glist) = $self->labelLUB($class);
#       SCCLUB: foreach my $greatest (@$glist) {
# 	    # $state must have a self loop.
# 	    next SCCLUB unless $$delta{$greatest}->IsMember($greatest);
# 	    # If the SCC contains initial states, $state must be initial.
# 	    unless ($init->IsDisjoint($class)) {
# 		next SCCLUB unless $init->IsMember($greatest);
# 	    }
# 	    # If the SCC intersects a fair set, then $state must
# 	    # belong to the fair set.  This may be simplified if we
# 	    # can assume that SCCs either intersect all fair sets or
# 	    # none.
# 	    foreach my $fairset (values %{$fair}) {
# 		unless ($fairset->IsDisjoint($class)) {
# 		    next SCCLUB unless $fairset->IsMember($greatest);
# 		}
# 	    }
# 	    # Every state outside of the SCC with a transition into
# 	    # the SCC must have a transition to $state.
# 	    my $inverse = InvertDelta($states,$delta);
# 	    my $fanin = Set->new;
# 	    foreach my $state (values %{$class}) {
# 		$fanin->Add($$inverse{$state}->Difference($class));
# 	    }
# 	    foreach my $state (values %{$fanin}) {
# 		next SCCLUB unless $$delta{$state}->IsMember($greatest);
# 	    }
# 	    # We are now ready to apply the theorem.
# 	    foreach my $fairset (values %{$fair}) {
# 		$fairset->Subtract($class->Difference(Set->new($greatest)));
# 	    }
# 	    last SCCLUB;
# 	}
#     }

    return $self;

} # Prune

######################################################################
# Remove unreachable states from automaton.
######################################################################
sub PruneUnreachable {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $reachable = Reachable($init,$delta);
    foreach my $state (values %{$states}) {
	delete $$delta{$state} unless $reachable->IsMember($state);
    }
    foreach my $fairset (values %{$fair}) {
	$fairset->Restrict($reachable);
    }
    $states->Restrict($reachable);

} # PruneUnreachable


######################################################################
# Computes the strongly connected components of an automaton.
# Tarjan's algorithm as described in Aho, Hopcroft, and Ullman,
# The Design and Analysis of Computer Algorithms.
######################################################################
sub SCC {
    my $self = shift;
    my @stack = ();
    my %onstack = ();
    my %dfnumber = ();
    my %lowlink = ();
    my @scclist = ();
    my $init = $$self{init};
    my $count = 0;
    foreach my $initial (values %{$init}) {
	unless (exists $dfnumber{$initial}) {
	    $self->searchSCC($initial,\@scclist,\@stack,\%onstack,
		      \%dfnumber,\%lowlink,\$count);
	}
    }
    my $scc = Set->new(@scclist);
    return ($scc,\@scclist);

} # SCC


######################################################################
# DFS for the computation of the strongly connected components.
######################################################################
sub searchSCC {
    my ($self,$v,$scc,$stack,$onstack,$dfnumber,$lowlink,$countr) = @_;
    die "$self is not a BuechiAL\n" if (ref($self) ne "BuechiAL");
    $$lowlink{$v} = $$dfnumber{$v} = $$countr;
    ${$countr}++;
    push(@{$stack},$v);
    $$onstack{$v} = 1;
    my $delta = $$self{delta};
    foreach my $transition (values %{$$delta{$v}}) {
	my $w = $transition->Second;
	unless (exists $$dfnumber{$w}) {
	    searchSCC($self,$w,$scc,$stack,$onstack,
		      $dfnumber,$lowlink,$countr);
	    $$lowlink{$v} = $$lowlink{$w} if $$lowlink{$w} < $$lowlink{$v};
	} elsif ($$dfnumber{$w} < $$dfnumber{$v} and exists $$onstack{$w}) {
	    $$lowlink{$v} = $$dfnumber{$w} if $$dfnumber{$w} < $$lowlink{$v};
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


######################################################################
# Returns the quotient graph for a partition of the states of an
# automaton.  The quotient graph has one fair set at most.
# A state of the quotient is fair if it intersects all the fair
# sets of the original automaton and it contains a cycle.
######################################################################
sub Quotient {
    my ($self,$partition) = @_;
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $names = $$self{names};
    my $fair = $$self{fair};
    my $initQ = Set->new;
    my %deltaQ = ();
    my $namesQ = AddNames($partition,"SCC");
    my %labelsQ = ();
    my %map = ();
    foreach my $class (values %{$partition}) {
	$initQ->Push($class) unless $class->IsDisjoint($init);
	my $name = Set->new;
	foreach my $state (values %{$class}) {
	    $name->Push($$names{$state});
	    $map{$state} = $class;
	}
	$labelsQ{$class} = $name;
	$deltaQ{$class} = Set->new;
    }
    my $states = $$self{states};
    foreach my $state (values %{$states}) {
	# Skip states that have become unreachable, and hence
	# are not in any SCC.
	next unless exists $map{$state};
	my $source = $map{$state};
	my $succ = $$delta{$state};
	foreach my $transition (values %{$succ}) {
	    my $otherstate = $transition->Second;
	    my $dest = $map{$otherstate};
	    $deltaQ{$source}->Push($dest);
	}
    }
    my $fairsetQ = $partition->Clone;
    # Remove SCCs consisting of one state only unless the state has
    # a self-loop.
    foreach my $class (values %{$fairsetQ}) {
	$fairsetQ->Delete($class) unless $deltaQ{$class}->IsMember($class);
    }
    # Remove from the fair set every SCC that does not intersect all fair
    # sets of the given automaton.
    foreach my $fairset (values %{$fair}) {
	foreach my $class (values %{$fairsetQ}) {
	    $fairsetQ->Delete($class) if $class->IsDisjoint($fairset);
	}
    }
    my $fairQ = Set->new;
    $fairQ->Push($fairsetQ) unless $fairsetQ->IsEqual($partition);
    return Buechi->new(
		       states => $partition,
		       init   => $initQ,
		       delta  => \%deltaQ,
		       names  => $namesQ,
		       labels => \%labelsQ,
		       fair   => $fairQ
		      );

} # Quotient

######################################################################
# Returns 1 if an automaton is weak; "" otherwise.
######################################################################
sub IsWeak {
    my $self = shift;
    my ($scc,$scclistd) = $self->SCC;
    my $fair = $$self{fair};
    my $ok = 1;
    foreach my $component (values %{$scc}) {
	#print "SCC:".$component->ToString($$self{names})."\n";
	foreach my $fairset (values %{$fair}) {
	    if ($component->IsDisjoint($fairset)) {
		$ok = 1;
		last;
	    }
	    $ok = 0 unless $component->IsIncluded($fairset);
	}
	return "" if $ok == 0;
    }
    return 1;
} # IsWeak

######################################################################
# Check whether the intersection of two automata is empty.
# We build a generalized automaton with labels on the states over a
# 1-letter alphabet that is empty iff the intersection of the two
# automata is empty.
######################################################################
sub IsIntersectionEmpty {
    my ($self,$other) = @_;
    my $sstates = $$self{states};
    my $sinit = $$self{init};
    my $sdelta = $$self{delta};
    my $snames = $$self{names};
    my $sfair = $$self{fair};
    my $ostates = $$other{states};
    my $oinit = $$other{init};
    my $odelta = $$other{delta};
    my $onames = $$other{names};
    my $ofair = $$other{fair};
    my %delta = ();
    my %labels = ();
    my %names = ();
    # The initial states of the intersection are those pairs of initial
    # states such that their labels are compatible.
    my $init = Buechi::Cartesian($sinit,$oinit);
    foreach my $newstate (values %{$init}) {
	my $sstate = $newstate->First;
	my $ostate = $newstate->Second;
	$labels{$newstate} = Set->new;
	$names{$newstate} = Pair->new($$snames{$sstate},
				      $$onames{$ostate})->ToString;
    }
    # Find reachable states.
    my $unexpanded = $init->Clone;
    my $states = $init->Clone;
    while ($unexpanded->Size > 0) {
	my $state = $unexpanded->Pop;
	my $sstate = $state->First;
	my $ostate = $state->Second;
	my $simage = $$sdelta{$sstate};
	my $oimage = $$odelta{$ostate};
	my $image = Set->new;
	my $new = Set->new;
	foreach my $stransition (values %{$$sdelta{$sstate}}) {
	    my $slabel = $stransition->First;
	    my $snext = $stransition->Second;
	    foreach my $otransition (values %{$$odelta{$ostate}}) {
		my $olabel = $otransition->First;
		my $label = $slabel->Union($olabel);
		next if Buechi::Contradiction($label);
		my $onext = $otransition->Second;
		my $newstate = Pair->new($snext,$onext);
		$image->Push($newstate);
		next if $states->IsMember($newstate);
		$new->Push($newstate);
		$labels{$newstate} = Set->new;
		$names{$newstate} = Pair->new($$snames{$snext},
					      $$onames{$onext})->ToString;
	    }
	}
	$delta{$state} = $image;
	$unexpanded->Add($new);
	$states->Add($new);
    }
    # The intersection inherits all the fair sets of the two automata.
    my $fair = Set->new;
    foreach my $sfairset (values %{$sfair}) {
	my $fairset = Set->new;
	foreach my $state (values %{$states}) {
	    if ($sfairset->IsMember($state->First)) {
		$fairset->Push($state);
	    }
	}
	$fair->Push($fairset);
    }
    foreach my $ofairset (values %{$ofair}) {
	my $fairset = Set->new;
	foreach my $state (values %{$states}) {
	    if ($ofairset->IsMember($state->Second)) {
		$fairset->Push($state);
	    }
	}
	$fair->Push($fairset);
    }
    my $intersection = Buechi->new(
				   states => $states,
				   init   => $init,
				   delta  => \%delta,
				   names  => \%names,
				   labels => \%labels,
				   fair   => $fair
				  );
    #print "No. of States : ",$intersection->NumberOfStates,"\n";
    $intersection->Prune;
    #print $intersection->ToDot("int");
    return $intersection->NumberOfStates == 0;

} # IsIntersectionEmpty


######################################################################
# Computes the reachable states of an automaton by BFS.
######################################################################
sub Reachable {
    my ($init,$delta) = @_;
    my $reached = $init->Clone;
    my $new = $init->Clone;
    while ($new->Size > 0) {
	my $image = Set->new;
	foreach my $state (values %{$new}) {
	    my $transitions = $$delta{$state};
	    foreach my $trans (values %{$transitions}) {
		$image->Push($trans->Second);
	    }
	}
	$new = $image->Difference($reached);
	$reached->Add($image);
    }
    return $reached;

} # Reachable



######################################################################
# Return the set of letters in the alphabet of the transitions of a
# set of states.
######################################################################
sub Letters {
    my ($self,$states) = @_;
    my $vars = $self->ExtractInputs($states);
    my $letters = Set->new;
    my @variables  = values %$vars;
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
	$letters->Push($l);
    }
    # print "Letters: ", $self->StateRelationToNameString($letters), "\n"; # dia
    return $letters;

} # Letters


######################################################################
# Extract the input variables from the labels of the transitions of a
# set of states.
######################################################################
sub ExtractInputs {
    my ($self,$states) = @_;
    my $delta = $$self{delta};
    my $atoms = Set->new;
    foreach my $state (values %{$states}) {
	my $transitions = $$delta{$state};
	foreach my $trans (values %{$transitions}) {
	    my $label = $trans->First;
	    # my $states = $trans->Second;
	    # print $label->ToString, " : ",
	    #   $self->StateRelationToNameString($states), "\n"; # dia
	    $atoms->Add($label);
	}
    }
    my $vars = Alternating::LabelToStringSet($atoms);
    # print "Inputs: ", $vars->ToString, "\n"; # dia
    return $vars;

} # ExtractInputs


sub CheckTypes {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $names = $$self{names};
    
    print "NBWTR CheckTypes ";
    #TODO: depending on the way the automaton is constructed the
    # type of the state and the init set is different
    die "NBWTR wrong state set" if ((ref($states) ne "Cover") &&
				    (ref($states) ne "Set"));
    die "NBWTR wrong delta" if (ref($delta) ne "HASH");
    die "NBWTR wrong init" if ((ref($init) ne "Cover") &&
			       (ref($init) ne "Set"));
    die "NBWTR wrong fair" if (ref($fair) ne "Set");

    my $labels = Set->new;
    foreach my $state (values %$states) {
	my $image = $$delta{$state};
	die "NBWTR wrong image" if (ref($image) ne "Set");
	foreach my $lpair (values %$image) {
	    die "NBWTR wrong tr" if (ref($lpair) ne "Pair");
	    my $label = $lpair->First;
	    my $dest  = $lpair->Second;
	    die "NBWTR wrong label" if (ref($label) ne "Set");
	    die "NBWTR wrong dest" if (ref($dest) ne "Set");
	}
    }

    print "done\n";
    return 1;
}

1;
