# $Id: Game.pm,v 1.2 2005/09/26 11:44:23 bjobst Exp $

######################################################################
# Functions to create and manipulate Buechi automata.
#
# Author: Sankar Gurumurthy <gurumurth@colorado.edu>
#         Fabio Somenzi <Fabio@Colorado.EDU>
#
######################################################################
package Game;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK $DEBUG);
@ISA       = qw(Exporter Buechi);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
$DEBUG = 0;
use strict;
use Set;
use Cover;
use Pair;
use Buechi;


#####################################################################
# Build the game automaton for fair simulation minimization.
######################################################################
sub new {
    my ($class,$buechi,$safety) = @_;
    my $bstates = $$buechi{states};
    my $bdelta = $$buechi{delta};
    my $blabels = $$buechi{labels};
    my $bnames = $$buechi{names};
    my $bfair = $$buechi{fair};
    my %delta = ();
    my %labels = ();
    my %names = ();
    my %priority = ();
    my %aToStates = ();
    my %pToStates = ();
    my $oddcount = 0;
    foreach my $bstate (values %{$bstates}) {
	$aToStates{$bstate} = Set->new;
	$pToStates{$bstate} = Set->new;
    }
    # Build the initial set of states.  An initial state of the game
    # automaton is a state (a,(i,s)) such that (i,s) is in the safety
    # relation.  We have to keep in mind that the identity relation is
    # not explicitly stored in $safety.
    my $states = Set->new;
    foreach my $pair (values %{$safety},
		      map {Pair->new($_,$_)} values %{$bstates}) {
	my $state = Pair->new("a",$pair);
	my ($anti, $proto) = ($pair->First, $pair->Second);
	$labels{$state} = $$blabels{$anti}->Clone unless ref($buechi) eq "BuechiAL";
	$names{$state} =
	  Pair->new("a",Pair->new($$bnames{$anti},$$bnames{$proto}))->ToString;
	#$names{$state} = "a,".$$bnames{$anti}."|".$$bnames{$proto};
	$states->Push($state);
	my $amap = $aToStates{$anti};
	$amap->Push($state);
	my $pmap = $pToStates{$proto};
	$pmap->Push($state);
    }

    # Build the reachable part of the parity game graph.
    my $bfairset = $bfair->Pick; # there is only one
    my $unexpanded = $states->Clone;
    my $astates = $states->Clone;
    while ($unexpanded->Size > 0) {
	my $state = $unexpanded->Pop;
	my $flag = $state->First;
	my $pair = $state->Second;
	my $antagonist  = $pair->First;
	my $protagonist = $pair->Second;
	#next unless ( $antagonist->Size > 0 && $protagonist->Size >0);
	my $image = Set->new;
	my $newflag;
	if ($flag eq "a") {
	    # Antagonist state.
	    my $bimage = $$bdelta{$antagonist};
	    foreach my $ianti (values %{$bimage}) {
		my $ipair;
		unless (ref($buechi) eq "BuechiAL") {
		    $ipair = Pair->new($ianti,$protagonist);
		}
		else {
		    $ipair = Pair->new($ianti->Second,$protagonist);
		}
		$image->Push(Pair->new("p",$ipair));
	    }
	    $newflag = "p";
	} else {
	    # Protagonist state.
	    my $bimage = $$bdelta{$protagonist};
	    foreach my $iproto (values %{$bimage}) {
		unless (ref($buechi) eq "BuechiAL") {
		    my $ipair =  Pair->new($antagonist,$iproto);
		    if ($antagonist eq $iproto or $safety->IsMember($ipair)) {
			$image->Push(Pair->new("a",$ipair));
		    }
		}
		else {
		    my $ipair =  Pair->new($antagonist,$iproto->Second);
		    if ($antagonist eq $iproto->Second or $safety->IsMember($ipair)) {
			$image->Push(Pair->new("a",$ipair));
		    }
		}
	    }
	    $newflag = "a";
	}
	my $new = $image->Difference($states);
	foreach my $newstate (values %{$new}) {
	    my $newpair = $newstate->Second;
	    my $newanti  = $newpair->First;
	    my $newproto = $newpair->Second;
	    my $label;
	    if ($newflag eq "a") {
		$label = $$blabels{$newanti}->Clone;
	    } else {
		$label = Set->new;
	    }
	    $labels{$newstate} = $label unless ref($buechi) eq "BuechiAL";
	   $names{$newstate} =
	      Pair->new($newflag,
			Pair->new($$bnames{$newanti},$$bnames{$newproto})
		       )->ToString;
	    #$names{$state} = $newflag.",".$$bnames{$newanti}."|".$$bnames{$newproto};
	    my $amap = $aToStates{$newanti};
	    $amap->Push($newstate);
	    my $pmap = $pToStates{$newproto};
	    $pmap->Push($newstate);
	}
	$delta{$state} = $image;
	if ($bfairset->IsMember($protagonist)) {
	    $priority{$state} = 0;
	} elsif ($bfairset->IsMember($antagonist) and $flag eq "a") {
	    $priority{$state} = 1;
	    $oddcount++;
	} else {
	    $priority{$state} = 2;
	}
	$unexpanded->Add($new);
	$states->Add($new);
	$astates->Add($new) if $newflag eq "a";
    }

    my %measure = map {$_ => 0} values %{$states};
    my %best    = map {$_ => 0} values %{$states};
    my %count   = map {$_ => $delta{$_}->Size} values %{$states};
    my $self = {
		states   => $states,
		init     => Set->new,
		priority => \%priority,
		measure  => \%measure,
		best     => \%best,
		count    => \%count,
		delta    => \%delta,
		inverse  => Buechi::InvertDelta($states,\%delta),
		names    => \%names,
		labels   => \%labels,
		fair     => Set->new,
		oddcount => $oddcount,
		astates  => $astates,
		amap     => \%aToStates,
		pmap     => \%pToStates
	       };
    return bless $self, $class;

} # new

#####################################################################
# Build the game automaton for fair simulation minimization for BuechiAL.
######################################################################
sub newAL {
    my ($class,$buechial,$safety,%params) = @_;
    my $bstates = $$buechial{states};
    my $bdelta = $$buechial{delta};
    my $blabels = $$buechial{labels};
    my $bnames = $$buechial{names};
    my $bfair = $$buechial{fair};
    my $binverse = BuechiAL::InvertDelta($bstates,$bdelta);
    my $allLabels;
    if (defined $params{allLabels}) {
	$allLabels = $params{allLabels};
    }
    else {
	$allLabels = Set->new;
    }
    my %delta = ();
    my %labels = ();
    my %names = ();
    my %priority = ();
    my %aToStates = ();
    my %pToStates = ();
    my $oddcount = 0;
    foreach my $bstate (values %{$bstates}) {
	$aToStates{$bstate} = Set->new;
	$pToStates{$bstate} = Set->new;
    }
    # Build the initial set of states.  An initial state of the game
    # automaton is a state (a,(i,s)) such that (i,s) is in the safety
    # relation.  We have to keep in mind that the identity relation is
    # not explicitly stored in $safety.
    my $states = Set->new;
    foreach my $pair (values %{$safety},
		      map {Pair->new($_,$_)} values %{$bstates}) {
	my ($anti, $proto) = ($pair->First, $pair->Second);
	my $label = Set->new;
	my $clabel = BuechiAL::CanonicalSet($label,$allLabels);
	my $state = Pair->new(Pair->new("a",$clabel),$pair);
	#$labels{$state} = $$blabels{$anti}->Clone unless ref($buechi) eq "BuechiAL";
	$names{$state} =
	  Pair->new(Pair->new("a",Set->new),Pair->new($$bnames{$anti},$$bnames{$proto}))->ToString;
	#$names{$state} = "a,".$$bnames{$anti}."|".$$bnames{$proto};
	$states->Push($state);
	my $amap = $aToStates{$anti};
	$amap->Push($state);
	my $pmap = $pToStates{$proto};
	$pmap->Push($state);
    }

    # Build the reachable part of the parity game graph.
    my $bfairset = $bfair->Pick; # there is only one
    my $unexpanded = $states->Clone;
    my $astates = $states->Clone;
    while ($unexpanded->Size > 0) {
	my $state = $unexpanded->Pop;
	my $flag = $state->First->First;
	my $pair = $state->Second;
	my $antagonist  = $pair->First;
	my $protagonist = $pair->Second;
	#next unless ( $antagonist->Size > 0 && $protagonist->Size >0);
	my $image = Set->new;
	my $newflag;
	if ($flag eq "a") {
	    # Antagonist state.
	    my $bimage = $$bdelta{$antagonist};
	    foreach my $ianti (values %{$bimage}) {
		my $label = $ianti->First;
		my $clabel = BuechiAL::CanonicalSet($label,$allLabels);
		my $ipair = Pair->new($ianti->Second,$protagonist);
		$image->Push(Pair->new(Pair->new("p",$clabel),$ipair));
	    }
	    $newflag = "p";
	} else {
	    # Protagonist state.
	    my $bimage = $$bdelta{$protagonist};
	    foreach my $iproto (values %{$bimage}) {
		my $label = Set->new;
		my $clabel = BuechiAL::CanonicalSet($label,$allLabels);
		next unless $iproto->First->IsIncluded($state->First->Second);
		my $ipair =  Pair->new($antagonist,$iproto->Second);
		if ($antagonist eq $iproto->Second or $safety->IsMember($ipair)) {
		    $image->Push(Pair->new(Pair->new("a",$clabel),$ipair));
		}
	    }
	    $newflag = "a";
	}
	my $new = $image->Difference($states);
	foreach my $newstate (values %{$new}) {
	    my $newflab = $newstate->First;
	    my $newpair = $newstate->Second;
	    my $newanti  = $newpair->First;
	    my $newproto = $newpair->Second;
	    my $label;
	    $names{$newstate} =
	      Pair->new($newflab,
			Pair->new($$bnames{$newanti},$$bnames{$newproto})
		       )->ToString;
	    #$names{$state} = $newflag.",".$$bnames{$newanti}."|".$$bnames{$newproto};
	    my $amap = $aToStates{$newanti};
	    $amap->Push($newstate);
	    my $pmap = $pToStates{$newproto};
	    $pmap->Push($newstate);
	}
	$delta{$state} = $image;
	if ($bfairset->IsMember($protagonist)) {
	    $priority{$state} = 0;
	} elsif ($bfairset->IsMember($antagonist) and $flag eq "a") {
	    $priority{$state} = 1;
	    $oddcount++;
	} else {
	    $priority{$state} = 2;
	}
	$unexpanded->Add($new);
	$states->Add($new);
	$astates->Add($new) if $newflag eq "a";
    }

    my %measure = map {$_ => 0} values %{$states};
    my %best    = map {$_ => 0} values %{$states};
    my %count   = map {$_ => $delta{$_}->Size} values %{$states};
    my $self = {
		states   => $states,
		init     => Set->new,
		priority => \%priority,
		measure  => \%measure,
		best     => \%best,
		count    => \%count,
		delta    => \%delta,
		inverse  => Buechi::InvertDelta($states,\%delta),
		names    => \%names,
		labels   => \%labels,
		fair     => Set->new,
		oddcount => $oddcount,
		astates  => $astates,
		allLabels => $allLabels,
		amap     => \%aToStates,
		pmap     => \%pToStates
	       };
    return bless $self, $class;

} # newAL


######################################################################
# Clones a pariry game graph.
######################################################################
sub Clone {
    my $self= shift;
    my $clone;
    unless (defined $$self{allLabels}) {
	$clone = {
		  states   => $$self{states}->Clone,
		  init     => $$self{init}->Clone,
		  priority => CloneHash($$self{priority}),
		  measure  => CloneHash($$self{measure}),
		  best     => CloneHash($$self{best}),
		  count    => CloneHash($$self{count}),
		  delta    => CloneHashOfSets($$self{delta}),
		  inverse  => CloneHashOfSets($$self{inverse}),
		  names    => \%{$$self{names}},
		  labels   => \%{$$self{labels}},
		  fair     => $$self{fair}->Clone,
		  oddcount => $$self{oddcount},
		  astates  => $$self{astates}->Clone,
		  amap     => CloneHashOfSets($$self{amap}),
		  pmap     => CloneHashOfSets($$self{pmap}),
		 };
    }
    else {
	$clone = {
		  states   => $$self{states}->Clone,
		  init     => $$self{init}->Clone,
		  priority => CloneHash($$self{priority}),
		  measure  => CloneHash($$self{measure}),
		  best     => CloneHash($$self{best}),
		  count    => CloneHash($$self{count}),
		  delta    => CloneHashOfSets($$self{delta}),
		  inverse  => CloneHashOfSets($$self{inverse}),
		  names    => \%{$$self{names}},
		  labels   => \%{$$self{labels}},
		  fair     => $$self{fair}->Clone,
		  oddcount => $$self{oddcount},
		  astates  => $$self{astates}->Clone,
		  allLabels =>$$self{allLabels}->Clone ,
		  amap     => CloneHashOfSets($$self{amap}),
		  pmap     => CloneHashOfSets($$self{pmap}),
		 };
    }
    return bless $clone, ref $self;

} # Clone


######################################################################
# Clone a hash of sets cloning the sets themselves.
######################################################################
sub CloneHash {
    my $hash = shift;
    my %clone = ();
    foreach (keys %{$hash}) {
	$clone{$_} = $$hash{$_};
    }
    return \%clone;

} # CloneHash


######################################################################
# Clone a hash of sets cloning the sets themselves.
######################################################################
sub CloneHashOfSets {
    my $hash = shift;
    my %clone = ();
    foreach (keys %{$hash}) {
	$clone{$_} = $$hash{$_}->Clone;
    }
    return \%clone;

} # CloneHashOfSets


######################################################################
# Update a game graph given a set of arcs to be removed, and a set of
# arcs to be added.
######################################################################
sub Update {
    my ($self,$buechi,$removals,$additions,%params) = @_;
    my $gstates = $$self{states};
    my $amap = $$self{amap};
    my $pmap = $$self{pmap};
    my $delta = $$self{delta};
    my $inverse = $$self{inverse};
    my $names = $$self{names};
    my $labels = $$self{labels};
    my $Wa = $$self{astates};
    my $priority = $$self{priority};
    my $measure = $$self{measure};
    my $best = $$self{best};
    my $count = $$self{count};
    my $bdelta = $$buechi{delta};
    my $bnames = $$buechi{names};
    my $bfair = $$buechi{fair};
    my $newfstate;
    if (defined $params{newfair}) {
	$newfstate = $params{newfair};
    }
    else {
	$newfstate = undef;
    }
    my $changes = Set->new;
    foreach my $arc (values %{$removals}) {
	# print "Removing arc: ", $arc->ToString, "\n";
	my $source = $arc->First;
	my $destination = $arc->Second;
	my $gsources = $$pmap{$source}->Difference($Wa);
	my $gdestinations = $$pmap{$destination}->Intersection($Wa);
	foreach my $gsource (values %{$gsources}) {
	    next if $$delta{$gsource}->IsDisjoint($gdestinations);
	    $changes->Push($gsource);
	    $$delta{$gsource}->Subtract($gdestinations);
	}
	foreach my $gdestination (values %{$gdestinations}) {
	    $$inverse{$gdestination}->Subtract($gsources);
	}
    }
    foreach my $arc (values %{$additions}) {
	my $source = $arc->First;
	my $destination = $arc->Second;
	my $gsources = $$amap{$source}->Intersection($Wa);
	my $gdestinations = $$amap{$destination}->Difference($Wa);
	foreach  my $gsource (values %{$gsources}) {
	    $changes->Push($gsource);
	    my $flag = $gsource->First;
	    my $pair = $gsource->Second;
	    my ($anti,$proto) = ($pair->First,$pair->Second);
	    my $nextstate = Pair->new("p", Pair->new($destination,$proto));
	    $$delta{$gsource}->Push($nextstate);
	    my $oldstateflag = $gdestinations->IsMember($nextstate);
	    if ($oldstateflag) {
		$$inverse{$nextstate}->Push($gsource);
	    } else {
#		$changes->Push($nextstate);
		$gstates->Push($nextstate);
		$$names{$nextstate} =
		  Pair->new("p", Pair->new($$bnames{$destination},
					   $$bnames{$proto}))->ToString;
		#$$names{$nextstate} ="p,".$$bnames{$destination}."|".$$bnames{$proto};
		$$labels{$nextstate} = Set->new unless ref($buechi) eq "BuechiAL";
		$$inverse{$nextstate} = Set->new($gsource);
		my $biproto = $$bdelta{$proto};
		my $dpairs = Buechi::Cartesian(Set->new($destination),
					       $biproto);
		my $gdestinations2 = Buechi::Cartesian(Set->new("a"),$dpairs);
		$gdestinations2->Restrict($Wa);
		$$delta{$nextstate} = $gdestinations2->Clone;
		foreach my $newsucc (values %{$gdestinations2}) {
		    $$inverse{$newsucc}->Push($nextstate);
		}
		$$priority{$nextstate} = 2;
		# This works for non-generalized Buechi automata.
		foreach my $bfairset(values %{$bfair}) {
		    $$priority{$nextstate} = 0 if $bfairset->IsMember($proto);
		}
		$$best{$nextstate}  = $self->val($nextstate);
		$$count{$nextstate} = $self->cnt($nextstate);
		$$measure{$nextstate} =
		  $self->incr($$best{$nextstate},$$priority{$nextstate});
		$$amap{$destination}->Push($nextstate);
		$$pmap{$proto}->Push($nextstate);
	    }
	}
    }
    return $changes unless defined($newfstate);
    foreach my $gstate (values %$gstates) {
	next if $$priority{$gstate} == 0;
	if ($gstate->Second->First eq $newfstate) {
	    if ($gstate->First eq "a") {
		 $$priority{$gstate} = 1;
	    }
	}
	# if ($gstate->Second->Second eq $newfstate) {
# 	    $$priority{$gstate} = 0;
# 	}
    }
    return $changes;

} # Update

######################################################################
# Update a game graph given a set of arcs to be removed, and a set of
# arcs to be added.(for BuechiAL)
######################################################################
sub UpdateAL {
    my ($self,$buechi,$removals,$additions,%params) = @_;
    my $gstates = $$self{states};
    my $amap = $$self{amap};
    my $pmap = $$self{pmap};
    my $delta = $$self{delta};
    my $inverse = $$self{inverse};
    my $names = $$self{names};
    my $labels = $$self{labels};
    my $Wa = $$self{astates};
    my $priority = $$self{priority};
    my $measure = $$self{measure};
    my $best = $$self{best};
    my $count = $$self{count};
    my $allLabels = $$self{allLabels};
    my $bdelta = $$buechi{delta};
    my $bnames = $$buechi{names};
    my $bfair = $$buechi{fair};
    my $newfstate;
    if (defined $params{newfair}) {
	$newfstate = $params{newfair};
    }
    else {
	$newfstate = undef;
    }
    my $changes = Set->new;
    foreach my $arc (values %{$removals}) {
	my $source = $arc->First;
	my $destination = $arc->Second;
	my $gsources = $$pmap{$source}->Difference($Wa);
	my $gdestinations = $$pmap{$destination}->Intersection($Wa);
	foreach my $gsource (values %{$gsources}) {
	    next if $$delta{$gsource}->IsDisjoint($gdestinations);
	    $changes->Push($gsource);
	    $$delta{$gsource}->Subtract($gdestinations);
	}
	foreach my $gdestination (values %{$gdestinations}) {
	    $$inverse{$gdestination}->Subtract($gsources);
	}
    }
    foreach my $arcpair (values %{$additions}) {
	my $label = $arcpair->First;
	my $clabel = BuechiAL::CanonicalSet($label,$allLabels);
	my $arc = $arcpair->Second;
	my $source = $arc->First;
	my $destination = $arc->Second;
	my $gsources = $$amap{$source}->Intersection($Wa);
	my $gdestinations = $$amap{$destination}->Difference($Wa);
	foreach  my $gsource (values %{$gsources}) {
	    $changes->Push($gsource);
	    my $flag = $gsource->First->First;
	    my $pair = $gsource->Second;
	    my ($anti,$proto) = ($pair->First,$pair->Second);
	    my $nextstate = Pair->new(Pair->new("p",$clabel),
						Pair->new($destination,$proto));
	    $$delta{$gsource}->Push($nextstate);
	    my $oldstateflag = $gdestinations->IsMember($nextstate);
	    if ($oldstateflag) {
		$$inverse{$nextstate}->Push($gsource);
	    } else {
#		$changes->Push($nextstate);
		$gstates->Push($nextstate);
		$$names{$nextstate} =
		  Pair->new(Pair->new("p",$clabel),Pair->new($$bnames{$destination},
					   $$bnames{$proto}))->ToString;
		#$$names{$nextstate} ="p,".$$bnames{$destination}."|".$$bnames{$proto};
		$$inverse{$nextstate} = Set->new($gsource);
		my $psucc = Set->new;
		foreach my $lpair (values %{$$bdelta{$proto}}) {
		    $psucc->Push($lpair->Second) if $lpair->First->IsIncluded($label);
		}
		my $dpairs = Buechi::Cartesian(Set->new($destination),
					       $psucc);
		my $alabel = Set->new;
		my $calabel = BuechiAL::CanonicalSet($alabel,$allLabels);
		my $gdestinations2 = Buechi::Cartesian(
					  Set->new(Pair->new("a",$calabel)),$dpairs);
		$gdestinations2->Restrict($Wa);
		$$delta{$nextstate} = $gdestinations2->Clone;
		foreach my $newsucc (values %{$gdestinations2}) {
		    $$inverse{$newsucc}->Push($nextstate);
		}
		$$priority{$nextstate} = 2;
		# This works for non-generalized Buechi automata.
		foreach my $bfairset(values %{$bfair}) {
		    $$priority{$nextstate} = 0 if $bfairset->IsMember($proto);
		}
		$$best{$nextstate}  = $self->val($nextstate);
		$$count{$nextstate} = $self->cnt($nextstate);
		$$measure{$nextstate} =
		  $self->incr($$best{$nextstate},$$priority{$nextstate});
		$$amap{$destination}->Push($nextstate);
		$$pmap{$proto}->Push($nextstate);
	    }
	}
    }
    return $changes unless defined($newfstate);
    foreach my $gstate (values %$gstates) {
	next if $$priority{$gstate} == 0;
	if ($gstate->Second->First eq $newfstate) {
	    if ($gstate->First eq "a") {
		 $$priority{$gstate} = 1;
	    }
	}
	# if ($gstate->Second->Second eq $newfstate) {
# 	    $$priority{$gstate} = 0;
# 	}
    }
    return $changes;

} # UpdateAL


######################################################################
# Convert a parity game graph into a string.
######################################################################
sub ToString {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $labels = $$self{labels};
    my $names = $$self{names};
    my $priority = $$self{priority};
    my $measure = $$self{measure};
    my $string = "States\n";
    foreach my $state (values %{$states}) {
	$string .= $$names{$state} . ": " . $state->ToString;
	if (defined $$labels{$state}) {
	    $string .=  " label: " . $$labels{$state}->ToString;
	}
	 $string.=   " priority: " . $$priority{$state} .
	      " measure: " . $$measure{$state} . "\n";
    }
    $string .= "Arcs\n";
    foreach my $state (values %{$states}) {
	$string .= ($init->IsMember($state) ? "-> " : "   ") .
	  $$names{$state} . " -> ";
	my $next = $$delta{$state};
	$string .= $self->StateRelationToNameString($next) . "\n";
    }
    $string .= "End\n";
    return $string;

} # ToString


######################################################################
# Converts a parity game graph to dot format.
# The label of each node consists of two lines:
#  1. antagonist and protagonist components, possibly followed by
#     delayed simulation flag;
#  2. priority and measure.  The measure may be undefined, in which
#     case a dash is printed.
# Each state is assumed to be a pair.  The second component is the pair
# (antagonist,protagonist).  The first component of the pair is the pair
# (a/p,b) for delayed simulation; otherwise it is just a/p.
# Antagonist states are drawn as boxes, while protagonist states are
# drawn as ellipses.  Nodes with priority 1 are shaded.
######################################################################
sub ToDot {
    my ($self,$graphname) = @_;
    my $nodes = $$self{states};
    my $names = $$self{names};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $priority = $$self{priority};
    my $measure = $$self{measure};
    my $string = qq!digraph "$graphname" {\nnode [shape=ellipse];\n!;
    $string .= qq!size = \"7.5,10\";\ncenter = true;\n!;
    $string .= qq!"title" [label=\"$graphname\",shape=plaintext];\n!;
    foreach my $node (values %{$nodes}) {
	my $flags = $node->First;
	my $pair  = $node->Second;
	my $type;
	my $delayflag;
	if (ref($flags) eq "Pair") {
	    $type = $flags->First;
	    $delayflag = $flags->Second;
	} else {
	    $type = $flags;
	    $delayflag = "";
	}
	my $name = $pair->ToString;
	#$name =~ tr/\{\}\[\]//d;
	if (ref($delayflag) eq "Set") {
	    $name .= $delayflag->ToString
	}
	elsif ($delayflag ne "") {
	    $name .= ",$delayflag";
	}
	my $style = $type eq "a" ? ",shape=box" : "";
	$style .= ",style=filled,color=lightgray" if $$priority{$node} == 1;
	my $rho = exists $$measure{$node} ? $$measure{$node} : "-";
	$string .= qq!"$$names{$node}" [label=\"$name\\n$$priority{$node},$rho\"$style];\n!;
	my $next = $$delta{$node};
	foreach my $succ (values %{$next}) {
	    $string .= qq!"$$names{$node}" -> "$$names{$succ}";\n!;
	}
	if ($init->IsMember($node)) {
	    my $pred = "init-" . $$names{$node};
	    $string .= qq!"$pred" [style=invis]\n!;
	    $string .= qq!"$pred" -> "$$names{$node}";\n!;
	}
    }
    $string .= qq!}\n!;
    return $string;

} # ParityGameToDot


#####################################################################
# Compute the angular brackets function.
#####################################################################
sub ang {
    my ($game,$x,$state) = @_;
    my $priority = $$game{priority};
    if ($$priority{$state} == 0 and $x <= $$game{oddcount}) {
	return 0;
    } else {
	return $x;
    }

} # ang


######################################################################
# Compute the val function.
######################################################################
sub val {
    my ($game,$state) = @_;
    my $delta = $$game{delta};
    my $measure = $$game{measure};
    my $Wa = $$game{astates};
    my $succ = $$delta{$state};
    if ($Wa->IsMember($state)) {
	my $max = 0;
	foreach my $succs (values %{$succ}) {
	    $max = $$measure{$succs} if $$measure{$succs} > $max;
	}
        return $game->ang($max,$state);
    } else {
	my $min = $$game{oddcount} + 1;
	foreach my $succs (values %{$succ}) {
	    $min = $$measure{$succs} if $$measure{$succs} < $min;
	}
        return $game->ang($min,$state);
    }

} # val


######################################################################
#  Compute the incr function.
######################################################################
sub incr {
    my ($game,$x,$priority) = @_;
    my $ret = 0;
    if ($priority != 1) {
	$ret = $x;
    } else {
	my $oddcount = $$game{oddcount};
	if ($x < $oddcount) {
	    $ret = $x + 1;
	} else {
            $ret = $oddcount + 1;
	}
    }
    return $ret;

} # incr


######################################################################
#  Compute the cnt function.
######################################################################
sub cnt {
    my ($game,$state) = @_;
    my $measure = $$game{measure};
    my $delta = $$game{delta};
    my $best = $$game{best};
    my $value = $$best{$state};
    my $count = 0;
    my $succ = $$delta{$state};
    foreach my $succs (values %{$succ}) {
	my $measurecur = $$measure{$succs};
	my $comp = $game->ang($measurecur,$state);
	if ($comp == $value) {
	    $count++;
	}
    }
    return $count;

} # cnt


######################################################################
# The lifting procedure.
######################################################################
sub lift {
    my ($game,$L) = @_;

    my $delta = $$game{delta};
    my $inverse = $$game{inverse};
    my $priority = $$game{priority};
    my $Wa = $$game{astates};
    my $measure = $$game{measure};
    my $best = $$game{best};
    my $count = $$game{count};
    while ($L->Size > 0) {
	my $state = $L->Pop;
	my $t = $$measure{$state};
	$$best{$state} = $game->val($state);
       	$$count{$state} = $game->cnt($state);
	$$measure{$state} = $game->incr($$best{$state},$$priority{$state});
	if ($$measure{$state} > $t) {
	    my $P = $$inverse{$state};
	    foreach my $w (values %{$P}) {
		unless ($L->IsMember($w)) {
		    if ($Wa->IsMember($w)) {
			$L->Push($w) if $$measure{$state} > $$best{$w};
		    } else {
			if ($game->ang($t,$w) == $$best{$w}) {
			    if ($$count{$w} == 1) {
				$L->Push($w);
			    } elsif ($$count{$w} > 1) {
				$$count{$w}--;
			    }
			}
		    }
		}
	    }
	}
    }
    my $oddcount = $$game{oddcount};
    my $winningstates = Set->new;
    foreach my $state (values %{$Wa}) {
	$winningstates->Push($state) if $$measure{$state} <= $oddcount;
    }
    return $winningstates;

} # lift


######################################################################
# Return true if each initial state of the antagonist has a
# simulating protagonist state.
######################################################################
sub AcceptChange {
    my ($self, $buechi, $winningstates) = @_;
    my $binit = $$buechi{init};
    my $allLabels;
    if (defined $$self{allLabels}) {
	$allLabels = $$self{allLabels};
    }
    else {
	$allLabels = undef;
    }
  ANTI: foreach my $ainit (values %{$binit}) {
      PROTO: foreach my $pinit (values %{$binit}) {
	    my $gstate;
	    if (defined $allLabels) {
		my $label = Set->new;
		my $clabel = BuechiAL::CanonicalSet($label,$allLabels);
		$gstate = Pair->new(Pair->new("a",$clabel),Pair->new($ainit,$pinit));
	    }
	    else {
		$gstate = Pair->new("a",Pair->new($ainit,$pinit));
	    }
	    next ANTI if $winningstates->IsMember($gstate);
	}
	return undef;
    }
    return 1;

} # AcceptChange

# Required return value.
1;
