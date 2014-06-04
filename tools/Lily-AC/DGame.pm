# $Id: DGame.pm,v 1.2 2005/09/26 11:44:23 bjobst Exp $

######################################################################
# Functions to create and manipulate Buechi automata.
#
# Author: Sankar Gurumurthy <gurumurth@colorado.edu>
#         Fabio Somenzi <Fabio@Colorado.EDU>
#
######################################################################
package DGame;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK $DEBUG $VALCNT);
@ISA       = qw(Exporter Game);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
$DEBUG = 0;
$VALCNT = 0;
use strict;
use Set;
use Cover;
use Pair;
use Buechi;
use Game;

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
    my %bit = ();
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
	my $bitflag = 0;
	foreach my $bfairset (values %{$bfair}) {
	    if ($bfairset->IsMember($anti) and not $bfairset->IsMember($proto)) {
		$bitflag = 1;
	    }
	}
	my $fpair = Pair->new("a",$bitflag);
	my $state = Pair->new($fpair,$pair);
	$labels{$state} = $$blabels{$anti}->Union($$blabels{$proto});
	$names{$state} =
	  Pair->new($fpair,Pair->new($$bnames{$anti},$$bnames{$proto}))->ToString;
	$states->Push($state);
	my $amap = $aToStates{$anti};
	$amap->Push($state);
	my $pmap = $pToStates{$proto};
	$pmap->Push($state);
#	$priority{$state} = 2;
    }

    # Build the reachable part of the parity game graph.
    my $unexpanded = $states->Clone;
    my $astates = $states->Clone;
    while ($unexpanded->Size > 0) {
	my $state = $unexpanded->Pop;
	my $flag = $state->First;
	my $pair = $state->Second;
	my $antagonist  = $pair->First;
	my $protagonist = $pair->Second;
	my $image = Set->new;
	my $newflag;
	my $newbit;
	if ($flag->First eq "a") {
	    # Antagonist state.
	    my $bimage = $$bdelta{$antagonist};
	    foreach my $antiimage (values %{$bimage}) {
		my $newbitflag = 0;
		foreach my $bfairset (values %{$bfair}) {
		    if ($bfairset->IsMember($antiimage) and not $bfairset->IsMember($protagonist)) {
			$newbitflag = 1;
		    }
		}
		if ($newbitflag) {
		    $newbit = 1;
		}
		else {
		    $newbit = $flag->Second;
		}
		$image->Push(Pair->new(Pair->new("p",$newbit)
			     ,Pair->new($antiimage,$protagonist)));
	    }
	    $newflag = "p";
	} else {
	    # Protagonist state.
	    my $bimage = $$bdelta{$protagonist};
	    $newbit = $flag->Second;
	    foreach my $protoimage (values %{$bimage}) {
		next unless $protoimage eq $antagonist or $safety->IsMember(Pair->new($antagonist,$protoimage));
		my $newbitflag = 0;
		foreach my $bfairset (values %{$bfair}) {
		     if ($bfairset->IsMember($antagonist)) {
			$newbit = 1;
		    }
		    if ($bfairset->IsMember($protoimage)) {
			$newbit = 0;
		    }
		}
		$image->Push(Pair->new(Pair->new("a",$newbit)
			     ,Pair->new($antagonist,$protoimage)));
	    }
	    $newflag = "a";
	}
	my $new = $image->Difference($states);
	foreach my $newstate (values %{$new}) {
	    my $bitflag = $newstate->First->Second;
	    my $newpair = $newstate->Second;
	    my $newanti  = $newpair->First;
	    my $newproto = $newpair->Second;
	    my $label;
	    if ($newflag eq "a") {
		$label = $$blabels{$newanti}->Union($$blabels{$newproto});
	    } else {
		$label = Set->new;
	    }
	    $labels{$newstate} = $label;
	    $names{$newstate} =
	      Pair->new(Pair->new($newflag,$bitflag),
			Pair->new($$bnames{$newanti},$$bnames{$newproto})
		       )->ToString;
	    my $amap = $aToStates{$newanti};
	    $amap->Push($newstate);
	    my $pmap = $pToStates{$newproto};
	    $pmap->Push($newstate);
	}
	$delta{$state} = $image;
	$priority{$state} = 2;
	$unexpanded->Add($new);
	$states->Add($new);
	$astates->Add($new) if $newflag eq "a";
    }

    # Build antagonist and protagonist fair sets.
    my $fair = Set->new;
    foreach my $state (values %{$astates}) {
	my $bit = ($state->First)->Second;
	$priority{$state} = $bit;
	if ($bit ==1) {
	    $oddcount++;
	}
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
		fair     => $fair,
		oddcount => $oddcount,
		astates  => $astates,
		amap     => \%aToStates,
		pmap     => \%pToStates
	       };
    return bless $self, $class;

} # new



######################################################################
# Update a game graph given a set of arcs to be removed, and a set of
# arcs to be added.
######################################################################
sub Update {
    my ($self,$buechi,$removals,$additions) = @_;
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
	    my $flags = $gsource->First;
	    my $pair = $gsource->Second;
	    my ($anti,$proto) = ($pair->First,$pair->Second);
	    my $newbit = 0;
	    foreach my $bfairset (values %{$bfair}) {
		if ($bfairset->IsMember($destination) and not $bfairset->IsMember($proto)){
		    $newbit = 1;
		}
	    }
	    my $newflags = Pair->new("p",$newbit);
	    my $nextstate = Pair->new($newflags, Pair->new($destination,$proto));
	    $$delta{$gsource}->Push($nextstate);
	    my $oldstateflag = $gdestinations->IsMember($nextstate);
	    if ($oldstateflag) {
		$$inverse{$nextstate}->Push($gsource);
	    } else {
		$changes->Push($nextstate);
		$gstates->Push($nextstate);
		$$names{$nextstate} =
		  Pair->new($newflags, Pair->new($$bnames{$destination},
					   $$bnames{$proto}))->ToString;
		$$labels{$nextstate} = Set->new;
		$$inverse{$nextstate} = Set->new($gsource);
		my $gdestinations2 = Set->new;
		foreach my $psucc (values %{$$bdelta{$proto}}) {
		    my $newbit2flag = 0;
		    my $newbit2 = $newbit;
		    foreach my $bfairset (values %{$bfair}) {
			if ($bfairset->IsMember($destination)) {
			    $newbit2=1;
			}
			if ($bfairset->IsMember($psucc)) {
			    $newbit2 = 0;
			}
		    }
		    $gdestinations2->Push(Pair->new(Pair->new("a",$newbit2),
						   Pair->new($destination,$psucc)));
		}
		$gdestinations2->Restrict($Wa);
		$$delta{$nextstate} = $gdestinations2->Clone;
		foreach my $newsucc (values %{$gdestinations2}) {
		    $$inverse{$newsucc}->Push($nextstate);
		}
		$$priority{$nextstate} = 2;
		$$best{$nextstate}  = $self->val($nextstate);
		$$count{$nextstate} = $self->cnt($nextstate);
		$$measure{$nextstate} =
		$self->incr($$best{$nextstate},$$priority{$nextstate});
		$$amap{$destination}->Push($nextstate);
		$$pmap{$proto}->Push($nextstate);
	    }
	}
    }
    return $changes;

} # Update

######################################################################
# Return true if each initial state of the antagonist has a
# simulating protagonist state.
######################################################################
sub AcceptChange {
    my ($self, $buechi, $winningstates) = @_;
    my $binit = $$buechi{init};
    my $bfair = $$buechi{fair};
  ANTI: foreach my $ainit (values %{$binit}) {
      PROTO: foreach my $pinit (values %{$binit}) {
	    my $bit = 0;
	    foreach my $bfairset(values %{$bfair}) {
		if ($bfairset->IsMember($ainit) and not $bfairset->IsMember($pinit)) {
		    $bit =1;
		}
	    }
	    my $gstate = Pair->new(Pair->new("a",$bit),Pair->new($ainit,$pinit));
	    next ANTI if $winningstates->IsMember($gstate);
	}
	return undef;
    }
    return 1;

} # AcceptChange

# Required return value.
1;
