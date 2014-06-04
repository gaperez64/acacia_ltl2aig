# $Id: Buechi.pm 2389 2008-06-19 09:09:53Z jobstman $

######################################################################
# Functions to create and manipulate Buechi automata.
#
# Author: Fabio Somenzi <Fabio@Colorado.EDU>
#         Sankar Gurumurthy <gurumurt@Colorado.EDU>
#
######################################################################
package Buechi;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK $nameIndex $DEBUG);
@ISA       = qw(Exporter);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
$DEBUG = -3;
use strict;
use Set;
use Cover;
use Pair;
use Game; #used in ReverseSimulationMinimization
use DGame;#used in DelayedSimulationMinimization

#used in Complement and for stats (Strength, ToDot, ToString)
use BuechiAL;
use CoBuechi;
use Alternating;

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
    $params{labels} = {} unless defined($params{labels});
    $params{names} = AddNames($params{states}) unless defined($params{names});

    $params{dontcares} = {} unless defined($params{dontcares});
    # Build the automaton.
    my $self = {
		states    => $params{states},
		init      => $params{init},
		delta     => $params{delta},
		fair      => $params{fair},
		labels    => $params{labels},
		names     => $params{names},
		dontcares => $params{dontcares}
	       };
    return bless $self, $class;

} # new


######################################################################
# Add a state to an automaton.
# The parameters are passed in a hash table.
#   state    => the unique state identifier (e.g., set of formulae)
#   init     => expression; if it evaluates to true, the state is initial
#   delta    => set of successor states
#   fair     => set of fair set to which state should be added
#   label    => label set
#   name     => (short) name for printing
#   dontcare => expression; if it evaluates to true, the state is don't care
######################################################################
sub AddState {
    my $self = shift;
    my %params = @_;
    # Read parameters and supply default values as needed.
    die "missing state\n" unless defined($params{state});
    $params{init} = "" unless defined($params{init});
    $params{delta} = Set->new unless defined($params{delta});
    $params{fair} = Set->new unless defined($params{fair});
    $params{label} = Set->new unless defined($params{label});
    $params{name} = newName("n") unless defined($params{name});
    $params{dontcare} = "" unless defined($params{dontcare});
    # Add state to automaton.
    my $state = $params{state};
    $$self{states}->Push($state);
    $$self{init}->Push($state) if $params{init};
    my $delta = $$self{delta};
    $$delta{$state} = $params{delta};
    my $labels = $$self{labels};
    $$labels{$state} = $params{label};
    my $names = $$self{names};
    $$names{$state} = $params{name};
    my $dontcares = $$self{dontcares};
    $$dontcares{$state} = 1 if $params{dontcare};
    my $fair = $$self{fair};
    foreach my $fairset (values %{$params{fair}}) {
	die "unrecognized fair set\n" unless $fair->IsMember($fairset);
	$fairset->Push($state);
    }

} # AddState


######################################################################
# Add names to states of an automaton.
######################################################################
sub AddNames {
    my ($states,$prefix) = @_;
    $prefix = "n" unless defined($prefix);
    my %names = ();
    $nameIndex = 0;
    my @sortLst = $states->Sort( sub{length($Set::a->ToString) <=> length($Set::b->ToString)});
    foreach my $state ( @sortLst ) {
	$names{$state} = newName($prefix,$state);
    }
    return \%names;

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
# Remove states that cannot reach all fair sets and perform other
# simplifications of the automaton.
######################################################################
sub Prune {
    my $self = shift;
    my $states = $$self{states};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $labels = $$self{labels};
    my $names = $$self{names};
    my $oldstates = $states->Clone;

    # Eliminate redundant transitions from the predecessors of
    # universal states.  A universal state is a state with a TRUE
    # label snd a self-loop; it must belong to all fair sets.
    foreach my $state (values %{$states}) {
	if ($$labels{$state}->Size == 0 &&
	    $$delta{$state}->IsMember($state)) {
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
		next unless $$delta{$s}->IsMember($state);
		foreach my $t (values %{$$delta{$s}}) {
		    unless ($t eq $state) {
			$$delta{$s}->Delete($t);
		    }
		}
	    }
	}
    }

    print $self->Stats, "\n";
#    die;
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
	    unless ($$delta{$state}->IsMember($state)) {
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
	my $inverse = InvertDelta($classes,$deltaQ);
	my $rclasses = Reachable($fairQ,$inverse);
	my $reach = Set->new;
	foreach my $class (values %{$rclasses}) {
	    $reach->Add($class);
	}
	$init->Restrict($reach);
	$states->Restrict($reach);
	foreach my $state (values %{$states}) {
	    $$delta{$state}->Restrict($states);
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
	    delete $$labels{$state};
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
    foreach my $class (values %{$classes}) {
	next unless $class->Size > 1;
	next unless $self->IsClique($class);
	my ($glb,$least) = $self->labelGLB($class);
	next unless defined($least);
	my $rest = $class->Clone;
	$rest->Delete($least);
	foreach my $fairset (values %{$fair}) {
	    if ($fairset->IsMember($least)) {
		unless ($fairset->IsDisjoint($rest)) {
		    $fairset->Delete($least);
		}
	    }
	}
    }

    # If an SCC contains a state s that simulates all the other states
    # in the same SCC (both forward and backward), then all states of
    # the SCC except s can be removed from all fair sets.
    # The following code checks for a special case of this theorem.
    foreach my $class (values %{$classes}) {
	next unless $class->Size > 1;
	my ($lub,$glist) = $self->labelLUB($class);
      SCCLUB: foreach my $greatest (@$glist) {
	    # $state must have a self loop.
	    next SCCLUB unless $$delta{$greatest}->IsMember($greatest);
	    # If the SCC contains initial states, $state must be initial.
	    unless ($init->IsDisjoint($class)) {
		next SCCLUB unless $init->IsMember($greatest);
	    }
	    # If the SCC intersects a fair set, then $state must
	    # belong to the fair set.  This may be simplified if we
	    # can assume that SCCs either intersect all fair sets or
	    # none.
	    foreach my $fairset (values %{$fair}) {
		unless ($fairset->IsDisjoint($class)) {
		    next SCCLUB unless $fairset->IsMember($greatest);
		}
	    }
	    # Every state outside of the SCC with a transition into
	    # the SCC must have a transition to $state.
	    my $inverse = InvertDelta($states,$delta);
	    my $fanin = Set->new;
	    foreach my $state (values %{$class}) {
		$fanin->Add($$inverse{$state}->Difference($class));
	    }
	    foreach my $state (values %{$fanin}) {
		next SCCLUB unless $$delta{$state}->IsMember($greatest);
	    }
	    # We are now ready to apply the theorem.
	    foreach my $fairset (values %{$fair}) {
		$fairset->Subtract($class->Difference(Set->new($greatest)));
	    }
	    last SCCLUB;
	}
    }

    return $self;

} # Prune


######################################################################
# Merge states while preserving trace equivalence.  This procedure
# performs local minimization.  It is less powerful than
# simulation-based minimization, but it is fast.  Hence, it is used
# for preprocessing.  Also, it can use information on don't care
# states, and applies some transformations that go beyond what
# simulation-based minimization can do.
######################################################################
sub Minimize {
    my $self = shift;
    my $states = $$self{states};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $labels = $$self{labels};
    my $names = $$self{names};
    my $dontcares = $$self{dontcares};
    my $inverse = InvertDelta($states,$delta);
    my $envelope = $states->Clone;
    my $change = 1;
    while ($change) {
	$change = 0;
      FIRST: foreach my $state (values %{$states}) {
	    # Check for input compatibility.
	    my $incand = pickInputCandidates($state,$delta,$inverse,$states);
	  SECOND: foreach my $otherstate (values %{$incand}) {
		next SECOND if $state eq $otherstate;
		next SECOND unless
		  $$labels{$state}->IsEqual($$labels{$otherstate});
		if ($init->IsMember($state)) {
		    next SECOND unless $init->IsMember($otherstate);
		} else {
		    next SECOND if $init->IsMember($otherstate);
		}
		unless (exists $$dontcares{$state} ||
			exists $$dontcares{$otherstate}) {
		    foreach my $fairset (values %{$fair}) {
			if ($fairset->IsMember($state)) {
			    next SECOND unless $fairset->IsMember($otherstate);
			} else {
			    next SECOND if $fairset->IsMember($otherstate);
			}
		    }
		}
		my $difference =
		  $$inverse{$state}->SymmDifference($$inverse{$otherstate});
		next SECOND unless
		  $difference->IsIncluded(Set->new($state,$otherstate));
		if ($$delta{$state}->IsMember($state) ||
		   $$delta{$otherstate}->IsMember($state)) {
		    next SECOND unless $$delta{$state}->IsMember($otherstate)
		      || $$delta{$otherstate}->IsMember($otherstate);
		} else {
		    next SECOND if $$delta{$state}->IsMember($otherstate)
		      || $$delta{$otherstate}->IsMember($otherstate);
		}
		# If we get here the two states are input compatible: merge.
		$change = 1;
		# print "Merging ", $$names{$state}, " into ",
		#   $$names{$otherstate}, " (input compatibility)\n";
		# Update initial states.
		$init->Delete($state);
		# Update delta and its inverse.
		foreach my $s (values %{$$delta{$state}}) {
		    next if $s eq $state;
		    $$inverse{$s}->Delete($state);
		    $$inverse{$s}->Push($otherstate);
		    $$delta{$otherstate}->Push($s);
		}
		foreach my $s (values %{$$inverse{$state}}) {
		    next if $s eq $state;
		    $$delta{$s}->Delete($state);
		}
		# Update don't care conditions.  If both states are
		# don't care it is safe to keep them so because it
		# means that there was no cycle through them before
		# merging them, and hence there is no cycle through
		# the surviving one after the merger.
		unless (exists $$dontcares{$state}) {
		    delete $$dontcares{$otherstate};
		}
		# Update fairness conditions.
		foreach my $fairset (values %{$fair}) {
		    if ($fairset->IsMember($state)) {
			$fairset->Delete($state);
			$fairset->Push($otherstate);
		    }
		}
		# Remove $state from the automaton.
		delete $$delta{$state};
		delete $$labels{$state};
		delete $$names{$state};
		delete $$dontcares{$state};
		$states->Delete($state);
		# print $self->ToString;
		next FIRST;
	    }
	    # Check for output compatibility.
	    my $outcand = pickOutputCandidates($state,$delta,$inverse,$states);
	  THIRD: foreach my $otherstate (values %{$outcand}) {
		next THIRD if $state eq $otherstate;
		next THIRD unless
		  $$labels{$state}->IsEqual($$labels{$otherstate});
		unless (exists $$dontcares{$state} ||
			exists $$dontcares{$otherstate}) {
		    foreach my $fairset (values %{$fair}) {
			if ($fairset->IsMember($state)) {
			    next THIRD unless $fairset->IsMember($otherstate);
			} else {
			    next THIRD if $fairset->IsMember($otherstate);
			}
		    }
		}
		my $difference =
		  $$delta{$state}->SymmDifference($$delta{$otherstate});
		next THIRD unless
		  $difference->IsIncluded(Set->new($state,$otherstate));
		if ($$delta{$state}->IsMember($state) ||
		   $$delta{$state}->IsMember($otherstate)) {
		    next THIRD unless $$delta{$otherstate}->IsMember($state)
		      || $$delta{$otherstate}->IsMember($otherstate);
		} else {
		    next THIRD if $$delta{$otherstate}->IsMember($state)
		      || $$delta{$otherstate}->IsMember($otherstate);
		}
		# If we get here the two states are output compatible: merge.
		$change = 1;
		# print "Merging ", $$names{$state}, " into ",
		#   $$names{$otherstate}, " (output compatibility)\n";
		# Update initial states.
		if ($init->IsMember($state)) {
		    $init->Delete($state);
		    $init->Push($otherstate);
		}
		# Update delta and its inverse.
		foreach my $s (values %{$$delta{$state}}) {
		    next if $s eq $state;
		    $$inverse{$s}->Delete($state);
		}
		foreach my $s (values %{$$inverse{$state}}) {
		    next if $s eq $state || $s eq $otherstate;
		    $$delta{$s}->Delete($state);
		    $$delta{$s}->Push($otherstate);
		    $$inverse{$otherstate}->Push($s);
		}
		if ($$delta{$state}->IsMember($otherstate) ||
		   $$delta{$state}->IsMember($state)) {
		    $$delta{$otherstate}->Push($otherstate);
		    $$inverse{$otherstate}->Push($otherstate);
		}
		$$delta{$otherstate}->Delete($state);
		# Update don't care conditions.  If both states are
		# don't care it is safe to keep them so because it
		# means that there was no cycle through them before
		# merging them, and hence there is no cycle through
		# the surviving one after the merger.
		unless (exists $$dontcares{$state}) {
		    delete $$dontcares{$otherstate};
		}
		# Update fairness conditions.
		foreach my $fairset (values %{$fair}) {
		    if ($fairset->IsMember($state)) {
			$fairset->Delete($state);
			$fairset->Push($otherstate);
		    }
		}
		# Remove $state from the automaton.
		delete $$delta{$state};
		delete $$labels{$state};
		delete $$names{$state};
		delete $$dontcares{$state};
		$states->Delete($state);
		# print $self->ToString;
		next FIRST;
	    }
	    # Check for dominance.
	    my $domcand = pickOutputCandidates($state,$delta,$inverse,$states);
	  FOURTH: foreach my $otherstate (values %{$domcand}) {
		next FOURTH if $state eq $otherstate;
		next FOURTH unless
		  $$labels{$otherstate}->IsIncluded($$labels{$state});
		if ($init->IsMember($state)) {
		    next FOURTH unless $init->IsMember($otherstate);
		}
		unless (exists $$dontcares{$state} ||
			exists $$dontcares{$otherstate}) {
		    foreach my $fairset (values %{$fair}) {
			if ($fairset->IsMember($state)) {
			    next FOURTH unless $fairset->IsMember($otherstate);
			}
		    }
		}
		next FOURTH
		  unless $$delta{$state}->IsIncluded($$delta{$otherstate});
		if ($$delta{$state}->IsMember($state)) {
		    next FOURTH
		      unless $$delta{$otherstate}->IsMember($otherstate);
		}
		my $difference =
		  $$inverse{$state}->Difference($$inverse{$otherstate});
		next FOURTH unless $difference->IsIncluded(Set->new($state));
		# If we get here, otherstate dominates state: remove state.
		$change = 1;
		# print "Merging ", $$names{$state}, " into ",
		#   $$names{$otherstate}, " (dominance)\n";
		# Update initial states.
		$init->Delete($state);
		# Update delta and its inverse.
		foreach my $s (values %{$$delta{$state}}) {
		    next if $s eq $state;
		    $$inverse{$s}->Delete($state);
		}
		foreach my $s (values %{$$inverse{$state}}) {
		    next if $s eq $state;
		    $$delta{$s}->Delete($state);
		}
		# Update don't care conditions.  If both states are
		# don't care it is safe to keep them so because it
		# means that there was no cycle through them before
		# merging them, and hence there is no cycle through
		# the surviving one after the merger.
		unless (exists $$dontcares{$state}) {
		    delete $$dontcares{$otherstate};
		}
		# Update fairness conditions.
		foreach my $fairset (values %{$fair}) {
		    if ($fairset->IsMember($state)) {
			$fairset->Delete($state);
			$fairset->Push($otherstate);
		    }
		}
		# Remove $state from the automaton.
		delete $$delta{$state};
		delete $$labels{$state};
		delete $$names{$state};
		delete $$dontcares{$state};
		$states->Delete($state);
		# print $self->ToString;
		next FIRST;
	    }
	}
    }
    return $self;

} # Minimize


######################################################################
# Pick candidates for input compatibility.
# Used by Minimize.
######################################################################
sub pickInputCandidates {
    my ($state,$delta,$inverse,$states) = @_;
    my $preimage = $$inverse{$state};
    my $size = $preimage->Size;
    return $states if $size == 0;
    return $states if $size == 1 and $preimage->IsMember($state);
    my $candidates = Set->new;
    my $i = 0;
    foreach my $s (values %{$$inverse{$state}}) {
	$candidates->Add($$delta{$s});
	$candidates->Push($s) if $size == 1;
	last if $i == 1;
	$i++;
    }
    $candidates->Delete($state);
    return $candidates;

} # pickOutputCandidates


######################################################################
# Pick candidates for output compatibility.
# Used by Minimize.
######################################################################
sub pickOutputCandidates {
    my ($state,$delta,$inverse,$states) = @_;
    my $image = $$delta{$state};
    my $size = $image->Size;
    return $states if $size == 0;
    return $states if $size == 1 and $image->IsMember($state);
    my $candidates = Set->new;
    my $i = 0;
    foreach my $s (values %{$image}) {
	$candidates->Add($$inverse{$s});
	$candidates->Push($s) if $size == 1;
	last if $i == 1;
	$i++;
    }
    $candidates->Delete($state);
    return $candidates;

} # pickOutputCandidates


######################################################################
# Compute the largest safety simulation relation of an automaton.
######################################################################
sub SafetySimulationRelation {
    my $self = shift;
    my $states = $$self{states};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $labels = $$self{labels};
    my $names = $$self{names};
    my $dontcares = $$self{dontcares};
    my $inverse = InvertDelta($states,$delta);

    # Initialize the direct simulation relation to all pairs (p,q)
    # that satisfy:
    # 0. p != q
    # 1. label(p) contains label(q) (hence, implies)
    # Also, push all pairs in the simulation relation onto a queue.
    my $simul = Set->new;
    my @queue = ();
    my %enqueued = ();
  FIRST: foreach my $p (values %{$states}) {
      SECOND: foreach my $q (values %{$states}) {
	    next SECOND if $p eq $q;
	    next SECOND unless $$labels{$q}->IsIncluded($$labels{$p});
	    my $pair = Pair->new($p,$q);
	    $simul->Push($pair);
	    push(@queue, $pair);
	    $enqueued{$pair} = 1;
	}
    }
    if ($DEBUG > 2) {
	print "Safety simulation relation initially contains ",
	  $simul->Size, " pairs\n";
	foreach my $pair (values %{$simul}) {
	    print $$names{$pair->First}, " is simulated by ",
	      $$names{$pair->Second}, "\n";
	}
    }
    # Compute the greatest fixpoint.
  PAIRS: while (@queue > 0) {
	my $pair = pop(@queue);
	delete $enqueued{$pair};
	my $p = $pair->First;
	my $q = $pair->Second;
	print "Pair: $$names{$p} simulated by $$names{$q}" if $DEBUG > 3;
      PLOOP: foreach my $s (values %{$$delta{$p}}) {
	    foreach my $t (values %{$$delta{$q}}) {
		next PLOOP if $s eq $t;
		next PLOOP if $simul->IsMember(Pair->new($s,$t));
	    }
	    $simul->Delete($pair);
	    # Enqueue perturbed pairs.
	    foreach my $u (values %{$$inverse{$p}}) {
		foreach my $v (values %{$$inverse{$q}}) {
		    my $newpair = Pair->new($u,$v);
		    if ($simul->IsMember($newpair)) {
			unless (exists $enqueued{$newpair}) {
			    push(@queue,$newpair);
			    $enqueued{$newpair} = 1;
			}
		    }
		}
	    }
	    print " removed\n" if $DEBUG > 3;
	    next PAIRS;
	}
	print " retained\n" if $DEBUG > 3;
    }
#     print "Safety simulation relation contains ", $simul->Size, " pairs\n";
#     foreach my $pair (values %{$simul}) {
# 	print $$names{$pair->First}, " is simulated by ",
# 	  $$names{$pair->Second}, "\n";
#     }

    return $simul;

} # SafetySimulationRelation


######################################################################
# Apply direct simulation minimization to an automaton.
######################################################################
sub DirectSimulationMinimization {
    my $self = shift;
    my $states = $$self{states};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $labels = $$self{labels};
    my $names = $$self{names};
    my $dontcares = $$self{dontcares};
    my $inverse = InvertDelta($states,$delta);
    # Initialize the direct simulation relation to all pairs (p,q)
    # that satisfy:
    # 0. p != q
    # 1. label(p) contains label(q) (hence, implies)
    # 2. for each f in F, p in f -> q in f
    # Also, push all pairs in the simulation relation onto a queue.
    my $simul = Set->new;
    my @queue = ();
    my %enqueued = ();
  FIRST: foreach my $p (values %{$states}) {
      SECOND: foreach my $q (values %{$states}) {
	    next SECOND if $p eq $q;
	    next SECOND unless $$labels{$q}->IsIncluded($$labels{$p});
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
#	print "Pair: $$names{$p} simulated by $$names{$q}";
      PLOOP: foreach my $s (values %{$$delta{$p}}) {
	    foreach my $t (values %{$$delta{$q}}) {
		next PLOOP if $s eq $t;
		next PLOOP if $simul->IsMember(Pair->new($s,$t));
	    }
	    $simul->Delete($pair);
	    # Enqueue perturbed pairs.
	    foreach my $u (values %{$$inverse{$p}}) {
		foreach my $v (values %{$$inverse{$q}}) {
		    my $newpair = Pair->new($u,$v);
		    if ($simul->IsMember($newpair)) {
			unless (exists $enqueued{$newpair}) {
			    push(@queue,$newpair);
			    $enqueued{$newpair} = 1;
			}
		    }
		}
	    }
#	    print " removed\n";
	    next PAIRS;
	}
#	print " retained\n";
    }
#     print "Direct simulation relation contains ", $simul->Size, " pairs\n";
    return unless $simul->Size > 0;
    # print "Direct simulation sans identity: {[simulated,simulating],...}\n",
     #  $self->StateRelationToNameString($simul), "\n";
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
# 	print "$$names{$p} is direct-simulation equivalent to $$names{$q}\n";
	# Update inverse image of successors.
	foreach my $s (values %{$$delta{$p}}) {
	    next if $s eq $p;
	    $$inverse{$s}->Delete($p);
	}
	# Update image of predecessors.
	foreach my $s (values %{$$inverse{$p}}) {
	    next if $s eq $p;
	    $$delta{$s}->Delete($p);
	    $$delta{$s}->Push($q);
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
	delete $$labels{$p};
	delete $$names{$p};
	delete $$dontcares{$p};
	$states->Delete($p);
	# print $self->ToString;
    }
    # Remove arcs to direct-simulated states.
    foreach my $pair (values %{$simul}) {
	my $p = $pair->First;
	my $q = $pair->Second;
	# Make sure neither state has been removed because of
	# simulation equivalence.
	next unless $states->IsMember($p) and $states->IsMember($q);
	# Theorem applies.  Drop arcs to p from parents of both p and q.
	# print "Dropping arcs of common parents ";
	# print "of $$names{$p} and $$names{$q}\n";
	# Update image of predecessors.
	foreach my $s (values %{$$inverse{$p}}) {
	    next unless $$delta{$s}->IsMember($q);
	    # print "Dropping arc from $$names{$s} to $$names{$p}\n";
	    $$delta{$s}->Delete($p);
	    $$inverse{$p}->Delete($s);
	}
	# Remove state p from initial states if q is initial.
	$init->Delete($p) if $init->IsMember($q);
    }
    # print $self->ToString;

} # DirectSimulationMinimization


######################################################################
# Apply reverse simulation minimization to an automaton.
######################################################################
sub ReverseSimulationMinimization {
    my $self = shift;
    my $states = $$self{states};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $labels = $$self{labels};
    my $names = $$self{names};
    my $dontcares = $$self{dontcares};
    my $inverse = InvertDelta($states,$delta);
    # Initialize the reverse simulation relation to all pairs (p,q)
    # that satisfy:
    # 0. p != q
    # 1. label(p) contains label(q) (hence, implies)
    # 2. init(p) -> init(q)
    # 3. for each f in F, p in f -> q in f
    # Also, push all pairs in the simulation relation onto a queue.
    my $simul = Set->new;
    my @queue = ();
    my %enqueued = ();
  FIRST: foreach my $p (values %{$states}) {
      SECOND: foreach my $q (values %{$states}) {
	    next SECOND if $p eq $q;
	    next SECOND unless $$labels{$q}->IsIncluded($$labels{$p});
	    if ($init->IsMember($p)) {
		next SECOND unless $init->IsMember($q);
	    }
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
#     print "Reverse simulation relation initially contains ",
#       $simul->Size, " pairs\n";
#     foreach my $pair (values %{$simul}) {
# 	print $$names{$pair->First}, " is reverse simulated by ",
# 	  $$names{$pair->Second}, "\n";
#     }
    # Compute the greatest fixpoint.
  PAIRS: while (@queue > 0) {
	my $pair = pop(@queue);
	delete $enqueued{$pair};
	my $p = $pair->First;
	my $q = $pair->Second;
# 	print "Pair: $$names{$p}, $$names{$q}";
      PLOOP: foreach my $s (values %{$$inverse{$p}}) {
	    foreach my $t (values %{$$inverse{$q}}) {
		next PLOOP if $s eq $t;
		next PLOOP if $simul->IsMember(Pair->new($s,$t));
	    }
	    $simul->Delete($pair);
	    # Enqueue perturbed pairs.
	    foreach my $u (values %{$$delta{$p}}) {
		foreach my $v (values %{$$delta{$q}}) {
		    my $newpair = Pair->new($u,$v);
		    if ($simul->IsMember($newpair)) {
			unless (exists $enqueued{$newpair}) {
			    push(@queue,$newpair);
			    $enqueued{$newpair} = 1;
			}
		    }
		}
	    }
# 	    print " removed\n";
	    next PAIRS;
	}
# 	print " retained\n";
    }
   # print "Reverse simulation relation contains ", $simul->Size, " pairs\n";
    #return unless $simul->Size > 0;
    # print "Reverse simulation sans identity: {[simulated,simulating],...}\n",
     #  $self->StateRelationToNameString($simul), "\n";
    # Simplify the automaton.
    # Find reverse-simulation equivalent states.
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
	# Throw away p and add arcs from q.
#  	print "$$names{$p} is reverse-simulation equivalent to $$names{$q}\n";
	# Update inverse image of successors.
	foreach my $s (values %{$$delta{$p}}) {
	    next if $s eq $p;
	    $$inverse{$s}->Delete($p);
	    $$inverse{$s}->Push($q);
	    $$delta{$q}->Push($s);
	}
	# Update image of predecessors.
	foreach my $s (values %{$$inverse{$p}}) {
	    next if $s eq $p;
	    # print "Dropping arc from $$names{$s} to $$names{$p}\n";
	    $$delta{$s}->Delete($p);
	}
	# Update the fairsets.
	foreach my $fairset (values %{$fair}) {
	    $fairset->Delete($p);
	}
	# Remove state p from automaton.
	delete $$delta{$p};
	delete $$labels{$p};
	delete $$names{$p};
	delete $$dontcares{$p};
	$states->Delete($p);
	$init->Delete($p);
	# print $self->ToString;
    }
    # Remove arcs from reverse-simulated states.
    foreach my $pair (values %{$simul}) {
	my $p = $pair->First;
	my $q = $pair->Second;
	# Make sure neither state has been removed because of
	# simulation equivalence.
	next unless $states->IsMember($p) and $states->IsMember($q);
	# Theorem applies.  Drop arcs from p to children of both p and q.
	# print "Dropping arcs to common children ";
	# print "of $$names{$p} and $$names{$q}\n";
	# Update inverse image of successors.
	foreach my $s (values %{$$delta{$p}}) {
	    next unless $$inverse{$s}->IsMember($q);
	    # print "Dropping arc from $$names{$p} to $$names{$s}\n";
	    $$inverse{$s}->Delete($p);
	    $$delta{$p}->Delete($s);
	}
    }
    # print $self->ToString;

} # ReverseSimulationMinimization


######################################################################
# Apply reverse simulation minimization to an automaton.
######################################################################
sub ReverseSimulationMinimizationnew {
    #This module does reverse simulation minimization without safety
    #constraints. Arc removal is checked for fairness while state collapsing
    #is not.
    my $self = shift;
    my $states = $$self{states};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $labels = $$self{labels};
    my $names = $$self{names};
    my $dontcares = $$self{dontcares};
    my $inverse = InvertDelta($states,$delta);
    return unless ($fair->Size ==1);
    if ($DEBUG > 1) {
	print $self->ToDot("autob4");
    }
    # Initialize the reverse simulation relation to all pairs (p,q)
    # that satisfy:
    # 0. p != q
    # 1. label(p) contains label(q) (hence, implies)
    # 2. init(p) -> init(q)
    # 3. for each f in F, p in f -> q in f (this goes)
    # Also, push all pairs in the simulation relation onto a queue.
    my $simul = Set->new;
    my @queue = ();
    my %enqueued = ();
    FIRST: foreach my $p (values %{$states}) {
      SECOND: foreach my $q (values %{$states}) {
	    #condition 0
	    next SECOND if $p eq $q;
	    #condition 1
	    next SECOND unless $$labels{$q}->IsIncluded($$labels{$p});
	    #condition 2
	    if ($init->IsMember($p)) {
		next SECOND unless $init->IsMember($q);
	    } 
	   # foreach my $fairset (values %{$fair}) {
		#if ($fairset->IsMember($p)) {
		 #   next SECOND unless $fairset->IsMember($q);
	#	}
	 #   }
	    my $pair = Pair->new($p,$q);
	    $simul->Push($pair);
	    push(@queue, $pair);
	    $enqueued{$pair} = 1;
	}
    }
     #print "Reverse simulation relation initially contains ",
      # $simul->Size, " pairs\n";
     #foreach my $pair (values %{$simul}) {
 	#print $$names{$pair->First}, " is reverse simulated by ",
 	 # $$names{$pair->Second}, "\n";
    # }
    # Compute the greatest fixpoint.
  PAIRS: while (@queue > 0) {
	my $pair = pop(@queue);
	delete $enqueued{$pair};
	my $p = $pair->First;
	my $q = $pair->Second;
# 	print "Pair: $$names{$p}, $$names{$q}";
      PLOOP: foreach my $s (values %{$$inverse{$p}}) {
	    foreach my $t (values %{$$inverse{$q}}) {
		next PLOOP if $s eq $t;
		next PLOOP if $simul->IsMember(Pair->new($s,$t));
	    }
	    $simul->Delete($pair);
	    # Enqueue perturbed pairs.
	    foreach my $u (values %{$$delta{$p}}) {
		foreach my $v (values %{$$delta{$q}}) {
		    my $newpair = Pair->new($u,$v);
		    if ($simul->IsMember($newpair)) {
			unless (exists $enqueued{$newpair}) {
			    push(@queue,$newpair);
			    $enqueued{$newpair} = 1;
			}
		    }
		}
	    }
# 	    print " removed\n";
	    next PAIRS;
	}
# 	print " retained\n";
    }
    my $safety = $self->SafetySimulationRelation;
    return if $safety->Size == 0;
   #  print "The states in automaton are ",$$self{states}->ToString,"\n\n";
    # print "The safety in automaton are ",$safety->ToString,"\n\n";
    my $game = Game->new($self, $safety);
    print $game->ToDot("initial game") if $DEBUG > 2;
    my $gstates = $$game{states};
    if ($DEBUG > 4) {
	print "Game graph\n", $game->ToString, "End game graph\n";
	my $Wa = $$game{astates};
	print "Wa: ", $game->StateRelationToNameString($Wa), "\n";
	if ($DEBUG > 4) {
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
    my $winningstatesinitial = $game->lift($seeds->Clone);
    print $game->ToDot("parity game") if $DEBUG > 2;
  #  print "Relaxed Reverse simulation relation contains ", $simul->Size, " pairs\n";
   # return unless $simul->Size > 0;
    #print "Reverse simulation sans identity: {[simulated,simulating],...}\n",
#       $self->StateRelationToNameString($simul), "\n";
    # Simplify the automaton.
    # Find reverse-simulation equivalent states.
    my $mergedStates = 0;
    my $time = 0;
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
	# Throw away p and add arcs from q.
#  	print "$$names{$p} is reverse-simulation equivalent to $$names{$q}\n";
	# Update inverse image of successors.
	#print "Merging states ",$p->ToString," and ",$q->ToString,"\n";
	my $removals = Set->new;
	my $additions = Set->new;
	if ($DEBUG > 1) {
	    print "Checking the collapsing of reverse equivalent states ",
	      "$$names{$p} and $$names{$q}\n";
	}
	foreach my $pred (values %{$$inverse{$p}}) {
	    next unless $states->IsMember($pred);
	    next if $$delta{$pred}->IsMember($q);
	    my $arc = Pair->new($pred,$q);
	    $additions->Push($arc);
	}
	foreach my $pred (values %{$$inverse{$q}}) {
	    next unless $states->IsMember($pred);
	    next if $$delta{$pred}->IsMember($p);
	    my $arc = Pair->new($pred,$p);
	    $additions->Push($arc);
	}
	foreach my $succ (values %{$$delta{$q}}) {
	    next unless $states->IsMember($succ);
	    next if $$inverse{$succ}->IsMember($p);
	    my $arc = Pair->new($p,$succ);
	    $additions->Push($arc);
	}
	foreach my $succ (values %{$$delta{$p}}) {
	    next unless $states->IsMember($succ);
	    next if $$inverse{$succ}->IsMember($q);
	    my $arc = Pair->new($q,$succ);
	    $additions->Push($arc);
	}
	my $clone = $game->Clone;
	#totalmerge++;
	print "Additions: ", $additions->ToString, "\n" if $DEBUG > 4;
	my $changes = $clone->Update($self, $removals, $additions);
	my $winningstates = $clone->lift($changes);
	print "Merging check:\n", $clone->ToString, "\n" if $DEBUG > 4;
	print $clone->ToDot("merging check"), "\n" if $DEBUG > 4;
	next unless $clone->AcceptChange($self, $winningstates);
	#mergeaccept++;
	my $retained = $q;
	my $removed  = $p;
	print "Removed: ", $removed->ToString, "\n" if $DEBUG > 1;
	# This works for non-generalized Buechi automata.not necessarily what
	# happens if antagonist is in one fairset and protagonist in another
	foreach my $fairset (values %{$fair}) {
	    if (not $fairset->IsMember($q) and $fairset->IsMember($p)) {
		$retained = $p;
		$removed = $q;
	    }
	}
	print "Removed: ", $removed->ToString, "\n" if $DEBUG > 1;
	$mergedStates++;
	if ($DEBUG > 1) {
	    print "Merging the states ", $removed->ToString, " and ",
	      $retained->ToString, "\n";
	}
	foreach my $s (values %{$$delta{$removed}}) {
	    next if $s eq $removed;
	    $$inverse{$s}->Delete($removed);
	    $$inverse{$s}->Push($retained);
	    $$delta{$retained}->Push($s);
	}
	# Update image of predecessors.
	foreach my $s (values %{$$inverse{$removed}}) {
	    next if $s eq $removed;
	    # print "Dropping arc from $$names{$s} to $$names{$removed}\n";
	    $$delta{$s}->Delete($removed);
	    $$delta{$s}->Push($retained);
	    $$inverse{$retained}->Push($s);
	}
	# Update the fairsets.
	foreach my $fairset (values %{$fair}) {
	    $fairset->Delete($removed);
	}
	# Remove state p from automaton.
	delete $$delta{$removed};
	delete $$labels{$removed};
	#delete $$names{$removed};
	delete $$inverse{$removed};
	delete $$dontcares{$removed};
	$states->Delete($removed);
	$init->Delete($removed);
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
	$game = Game->new($self,$safety);
	$seeds->Restrict($$game{states});
	# print $seeds->ToString, "\n";
	$game->lift($seeds);
    }
    if ($DEBUG > 4) {
	print $self->ToDot("autoaftermerge");
    }
    # Remove arcs from reverse-simulated states.
    foreach my $pair (values %{$simul}) {
	my $p = $pair->First;
	my $q = $pair->Second;
	print "Checking the pair " ,$$names{$p}," ",$$names{$q},"\n"
	  if $DEBUG > 1;
	# Make sure neither state has been removed because of
	# simulation equivalence.
	next unless $states->IsMember($p) and $states->IsMember($q);
	# Theorem applies.  Drop arcs from p to children of both p and q.
	# print "Dropping arcs to common children ";
	# print "of $$names{$p} and $$names{$q}\n";
	# Update inverse image of successors.
	foreach my $s (values %{$$delta{$p}}) {
	    next unless $$inverse{$s}->IsMember($q);
	 #   print "checking arc from $$names{$p} to $$names{$s}\n";
	   # $$inverse{$s}->Delete($p);
	    #$$delta{$p}->Delete($s);
      	   #$totalarc++;
	    my $arc = Pair->new($p, $s);
	    my $removals = Set->new($arc);
	    my $additions = Set->new;
	    if ($DEBUG > 0) {
		print "checking arc from $$names{$p} to $$names{$s}\n";
	    }
	    my $clone = $game->Clone;
	    my $changes = $clone->Update($self, $removals, $additions);
	    if ($DEBUG > 1) {
		print $game->ToDot("gameb4- $time"), "\n",
	    }
	    #print $game->ToString,"\n";
	    my $winningstates = $clone->lift($changes);
	   # print $game->ToString,"\n";
	    if ($DEBUG > 1) {
		print $clone->ToDot("game- $time"), "\n",
		  "winning states: ", $winningstates->ToString, "\n";
	    }
	    next unless $clone->AcceptChange($self, $winningstates);
	   #$arcaccept++;
	    if ($DEBUG >  1) {
		print "Dropping arc from $$names{$p} to $$names{$s}\n";
	    }
	    $$inverse{$s}->Delete($p);
	    $$delta{$p}->Delete($s);
	    $game = $clone;
	    $time++;
	}
    }
    # print $self->ToString;

} # ReverseSimulationMinimizationnew



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
    my $safety = $self->SafetySimulationRelation;
    print "Safety simulation sans identity: {[simulated,simulating],...}\n",
      $self->StateRelationToNameString($safety), "\n" if $DEBUG > 0;
    # There is nothing to be gained by attempting fair simulation
    # minimization unless the safety simulation relation is a proper
    # superset of the identity.
    return if $safety->Size == 0;
    my $game = Game->new($self, $safety);
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
    my $labels = $$self{labels};
    my $names = $$self{names};
    my $dontcares = $$self{dontcares};
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
    foreach my $pair (values %{$checked}) {
	my ($anti,$proto) = ($pair->First,$pair->Second);
	my $additions = Set->new;
	# Make sure neither state has been removed yet.
	next unless $states->IsMember($anti) and $states->IsMember($proto);
	if ($DEBUG > 0) {
	    print "Checking the collapsing of fair equivalent states ",
	      "$$names{$anti} and $$names{$proto}\n";
	}
	foreach my $pred (values %{$$inverse{$anti}}) {
	    next unless $states->IsMember($pred);
	    next if $$delta{$pred}->IsMember($proto);
	    my $arc = Pair->new($pred,$proto);
	    $additions->Push($arc);
	}
	foreach my $pred (values %{$$inverse{$proto}}) {
	    next unless $states->IsMember($pred);
	    next if $$delta{$pred}->IsMember($anti);
	    my $arc = Pair->new($pred,$anti);
	    $additions->Push($arc);
	}
	foreach my $succ (values %{$$delta{$proto}}) {
	    next unless $states->IsMember($succ);
	    next if $$inverse{$succ}->IsMember($anti);
	    my $arc = Pair->new($anti,$succ);
	    $additions->Push($arc);
	}
	foreach my $succ (values %{$$delta{$anti}}) {
	    next unless $states->IsMember($succ);
	    next if $$inverse{$succ}->IsMember($proto);
	    my $arc = Pair->new($proto,$succ);
	    $additions->Push($arc);
	}
	my $clone = $game->Clone;
	#totalmerge++;
	print "Additions: ", $additions->ToString, "\n" if $DEBUG > 1;
	my $changes = $clone->Update($self, $removals, $additions);
	my $winningstates = $clone->lift($changes);
	print "Merging check:\n", $clone->ToString, "\n" if $DEBUG > 2;
	print $clone->ToDot("merging check"), "\n" if $DEBUG > 0;
	next unless $clone->AcceptChange($self, $winningstates);
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
	foreach my $succ (values %{$$delta{$removed}}) {
	    next if $succ eq $removed;
	    $$inverse{$succ}->Delete($removed);
	    $$inverse{$succ}->Push($retained);
	    $$delta{$retained}->Push($succ);
	}
	foreach my $pred (values %{$$inverse{$removed}}) {
	    next if $pred eq $removed;
	    $$delta{$pred}->Delete($removed);
	    $$delta{$pred}->Push($retained);
	    $$inverse{$retained}->Push($pred);
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
	delete $$labels{$removed};
#	delete $$names{$removed};
	delete $$dontcares{$removed};
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
	$game = Game->new($self,$safety);
	$seeds->Restrict($$game{states});
	# print $seeds->ToString, "\n";
	$game->lift($seeds);
    }
    # Remove arcs to fair-simulated states.
    my $additions = Set->new;
    foreach my $pair (values %{$fairsim}) {
	my ($anti,$proto) = ($pair->First,$pair->Second);
	# Make sure neither state has been removed because of
	# simulation equivalence.
	next unless $states->IsMember($anti) and $states->IsMember($proto);
	if ($DEBUG > 0) {
	    print "Dropping arcs of common parents ";
	    print "of $$names{$anti} and $$names{$proto}\n";
	}
	foreach my $s (values %{$$inverse{$anti}}) {
	    next unless $$delta{$s}->IsMember($proto);
	    if ($DEBUG > 0) {
		print "Checking arc from $$names{$s} to $$names{$anti}\n";
	    }
	    my $clone = $game->Clone;
	   #$totalarc++;
	    my $arc = Pair->new($s, $anti);
	    my $removals = Set->new($arc);
	    my $changes = $clone->Update($self, $removals, $additions);
	    my $winningstates = $clone->lift($changes);
	    if ($DEBUG > 1) {
		print $clone->ToDot("game-" . $time), "\n",
		  "winning states: ", $winningstates->ToString, "\n";
	    }
	    next unless $clone->AcceptChange($self, $winningstates);
	   #$arcaccept++;
	    if ($DEBUG > 0) {
		print "Dropping arc from $$names{$s} to $$names{$anti}\n";
	    }
	    $$delta{$s}->Delete($anti);
	    $$inverse{$anti}->Delete($s);
	    $game = $clone;
	    $time++;
	}
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
# Apply delayed simulation minimization to an automaton.
######################################################################
sub DelayedSimulationMinimization {
    my $self = shift;

    my $fair = $$self{fair};
    # Currently we can only deal with one fairness condition.  If there are
    # no fair sets, fair simulation minimization will do nothing.
    return unless $fair->Size == 1;
    my $safety = $self->SafetySimulationRelation;
    print "Safety simulation sans identity: {[simulated,simulating],...}\n",
      $self->StateRelationToNameString($safety), "\n" if $DEBUG > 0;
    # There is nothing to be gained by attempting delayed simulation
    # minimization unless the safety simulation relation is a proper
    # superset of the identity.
    return if $safety->Size == 0;
    my $game = DGame->new($self, $safety);
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
 #   open (DGAME,">dgame.dot");
  #  print $$game{states}->ToString;
 #  print DGAME "\n",$game->ToDot("Delaygame"),"\n";
 #   close(DGAME);
    print $game->ToDot("parity game") if $DEBUG > 0;
    print "Winning states: ", $game->StateRelationToNameString($winningstates),
      "\n" if $DEBUG > 1;
    my $fairsim = Set->new;
    foreach my $winnings (values %{$winningstates}) {
	my $pair = $winnings->Second;
	$fairsim->Push($pair) unless $pair->First eq $pair->Second;
    }
    print "Delayed simulation sans identity: {[simulated,simulating],...}\n",
      $self->StateRelationToNameString($fairsim), "\n" if $DEBUG > 1;
    # Minimize the automaton.
    my $states = $$self{states};
    my $init = $$self{init};
    my $delta = $$self{delta};
    my $labels = $$self{labels};
    my $names = $$self{names};
    my $dontcares = $$self{dontcares};
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
    foreach my $pair (values %{$checked}) {
	my ($anti,$proto) = ($pair->First,$pair->Second);
	my $retained = $proto;
	my $removed  = $anti;
	next if not $states->IsMember($retained) or not $states->IsMember($removed);
	print "Removed: ", $removed->ToString, "\n" if $DEBUG > 1;
	# This works for non-generalized Buechi automata.
	foreach my $fairset (values %{$fair}) {
	    if (not $fairset->IsMember($proto) and $fairset->IsMember($anti)) {
		$retained = $anti;
		$removed = $proto;
	    }
	}
	print "Removed: ", $removed->ToString, "\n" if $DEBUG > 1;
	if ($DEBUG > 0) {
	    print "Merging the states ", $proto->ToString, " and ",
	      $anti->ToString, "\n";
	}
	foreach my $succ (values %{$$delta{$removed}}) {
	    next if $succ eq $removed or not $states->IsMember($succ);
	    $$inverse{$succ}->Delete($removed);
	    $$inverse{$succ}->Push($retained);
	    $$delta{$retained}->Push($succ);
	}
	foreach my $pred (values %{$$inverse{$removed}}) {
	    next if $pred eq $removed or not $states->IsMember($pred);
	    $$delta{$pred}->Delete($removed);
	    $$delta{$pred}->Push($retained);
	    $$inverse{$retained}->Push($pred);
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
	delete $$labels{$removed};
#	delete $$names{$removed};
	delete $$dontcares{$removed};
	$states->Delete($removed);
    }
    print "After merging equivalent states: \n", $self->ToString, "\n"
      if $DEBUG >1;

} # DelayedSimulationMinimization


######################################################################
# Optimize an automaton.
######################################################################
sub Optimize {
    my ($self,$verb) = @_;
    print "Before optimization : ", $self->Stats, "\n" if $verb > 1;
    print $self->ToString if $verb > 2;
    print $self->ToDot("Before") if $verb > 3;
    $self->Prune;
    #my $labels = $$self{labels};
    #my $states = $$self{states};
    #foreach my $state(values %{$states}) {
	#print $$labels{$state}->ToString,"\n";
    #}
    #print $self->ToDot("Before");
    #print $self->ToString,"\n";
    #print $self->ToString,"\n";
    print "After first pruning : ", $self->Stats, "\n" if $verb > 1;
    print $self->ToString if $verb > 2;
    print $self->ToDot("Pruned") if $verb > 3;
    $self->Minimize;
    print "After minimization  : ", $self->Stats, "\n" if $verb > 1;
    print $self->ToString if $verb > 2;
    print $self->ToDot("Minimized") if $verb > 3;
    # my $discard = $self->ComputeExpandedFairSets;
    $self->DirectSimulationMinimization;
    #print "b4 \n";
    #$self->DirectSimulationMinimization;
    $self->ReverseSimulationMinimization;
    $self->FairSimulationMinimization;
    #$self->Prune;
    #print "After min. \n",$self->ToString,"\n";
    #print $self->ToDot("Present"),"\n";
    $self->DelayedSimulationMinimization;
    $self->Prune;
    #print $self->ToString, "\n";
    #return;

    # open (NN,"Nongeneralfinal");
#     my $ts = <NN>;
#     chomp($ts);
#     my @ta = split(/ /,$ts);
#     my $totalst = $ta[0];
#     my $totaltr = $ta[1];
#     my $totalfa = $ta[2];
#     my $totalin = $ta[3];
#     close(NN);
#     if ($$self{fair}->Size == 1) {
#    # $self->DelayedSimulationMinimization;
#    # $self->ReverseSimulationMinimization;
#    # $self->Prune;
#       open(TT,">>Nongeneral");
#       my $nostates = $self->NumberOfStates;
#       $totalst+=$nostates;
#       my $notrans = $self->NumberOfTransitions;
#       $totaltr += $notrans;
#       my $nofair = $self->NumberOfFairSets;
#       $totalfa += $nofair; 
#       my $noinitial = $self->NumberOfInitialStates;
#       $totalin += $noinitial;
#       my $strength = $self->Strength;
#       #$totalst += $strength; 
#       #print TT  "$nostates $notrans $nofair $noinitial $strength \n";
#       close(TT);
#       open (NN,">Nongeneralfinal");
#       #print NN "$totalst $totaltr $totalfa $totalin\n";
#       close(NN);
#     } else {
# 	#$self->DirectSimulationMinimization;
# 	#$self->ReverseSimulationMinimization;
# 	#$self->Prune;
#     }
    #print "after 1 \n";
    #print "After sim. minimiz. : ", $self->Stats, "\n" if $verb > 1;
    #print $self->ToString if $verb > 2;
    #print $self->ToDot("SimMinimized") if $verb > 3;
    ##$self->ReverseSimulationMinimization;
    #$self->Prune;
} # Optimize

sub Complement {
    my ($self,$verb) = @_;
    if ($$self{fair}->Size != 1) {
	open (FP,">>outours");
	print FP "fair set size not equal to 1\n";
	close(FP);
	open (FP,">>outcomp");
	print FP '-' x 70,"\nfair set size not equal to 1\n",'-' x 70,"\n";
	close(FP);
#	return;
	print "No of fairness condition > 1\n";
	$self = $self->CountingConstruction;
    } else {
	print "No of fairness condition = 1\n";
    }

    if ($verb > 2) {
	open(UCW, ">comp-ucw.dot");
	open(AWW, ">comp-aww.dot");
    }
    if (not($self->IsWeak)) {
	alarm 120;
	$SIG{'ALRM'} = \&timeouthandler;
	my $bl = $self;
	unless (ref($self) eq 'BuechiAL') { #we already have a BuechiAL)
	    $bl= BuechiAL->fromBuechi($self);
	    $bl->DirectSimulationMinimization;
	    $bl->FairSimulationMinimization;
	    print $bl->ToString,"\n" if $verb > 2;
	    print $bl->ToDot("Arcs") if $verb > 2;
	}
	my $cb = CoBuechi->fromBuechi($bl);
	print "CoBuechi\n" if $verb > 2;
	print $cb->ToString,"\n" if $verb > 2;
	print UCW $cb->ToDot("CoBuechi") if $verb > 2;
	close UCW if $verb > 2;
#	print $cb->ToDot("CoBuechi") if $verb > 2;
	print "printed\n" if $verb > 2;
	my $alt = Alternating->fromBuechi($cb,0);
	# #$alt->MergeTransitions;
 	$alt->DirectSimulationMinimization;
	my $stti = time();
 	my $WAA2n = $alt->ToBuechi;
 	$WAA2n->DirectSimulationMinimization;
	my $endi = time();
	open(WP,">>WAAd");
	print WP "done ",$endi - $stti,"\n";
	close(WP);
 	#print $WAA2n->Prune->ToString,"\n";
 	print "alternatinng \n" if $verb > 2;
	
 	print $alt->ToString,"\n"  if $verb > 2;
	my $al = Alternating->fromBuechi($cb,0,WAA2n => $WAA2n);
	#print "Alternating\n";
	$al->MergeTransitions;
	print $al->ToString,"\n"  if $verb > 2;
	$al->DirectSimulationMinimization;
	print $al->ToString,"\n"  if $verb > 2;
	$al->PruneHeight($WAA2n);
	print $al->ToString,"\n"  if $verb > 2;
	print AWW $al->ToDot("Alternating-comp"),"\n" if $verb > 2;
	close AWW if $verb > 2;
	open(FP,">>altstates");
	print FP $$al{states}->Size,"\n";
	close(FP);
	my $co = $al->ToBuechi;
	open(FP,">>states");
	print FP $$co{states}->Size," ";
	print $co->ToString,"\n" if $verb > 2;
	$co->MergeTransitions;
	print $co->ToString,"\n" if $verb > 2;
	$co->DirectSimulationMinimization;
	print $co->ToString,"\n" if $verb > 2;
	open(FP2,">>reduceheightst");
	print FP2 $$co{states}->Size," ";
	$co->ReduceHeight;
	print FP2 $$co{states}->Size,"\n ";
	close(FP2);
	print $co->ToString,"\n" if $verb > 2;
	$co->FairSimulationMinimization;
	$co->MergeTransitions;
	$co->Prune;
	print FP $$co{states}->Size,"\n";
	close(FP);
	print "END\n";
	unless ($co->IsIntersectionEmpty($bl)) {
	    open(FP,">>out1000ltl13");
	    print "Intersection not empty\n";
	    close(FP);
	    exit 0;
	}
	#alarm 0;
	print "complement\n" if $verb > 2;
	print $co->ToString,"\n" if $verb > 2;
	print $co->ToDot("comp") if $verb > 2;
	return $co;
    }
    else {
	alarm 60;
	$SIG{'ALRM'} = \&timeouthandler;
	my $bl= BuechiAL->fromBuechi($self);
	$bl->DirectSimulationMinimization;
	$bl->FairSimulationMinimization;
	print $bl->ToString,"\n" if $verb > 2;
	print $bl->ToDot("Arcs") if $verb > 2;
	my $cb = CoBuechi->fromBuechi($bl);
	print "CoBuechi\n" if $verb > 2;
	print $cb->ToString,"\n" if $verb > 2;
	print UCW $cb->ToDot("CoBuechi-comp") if $verb > 2;
	close UCW if $verb > 2;
	print "printed\n" if $verb > 2;
	my $stti = time();
	my $al = Alternating->fromBuechi($cb,1);
	print "alternating \n" if $verb > 2;
	print $al->ToString,"\n" if $verb > 2;
	$al->DirectSimulationMinimization;
	print $al->ToString,"\n" if $verb > 2;
	print AWW $al->ToDot("Alternating-comp"),"\n" if $verb > 2;
	close AWW if $verb > 2;
	open(FP,">>altstates");
	print FP $$al{states}->Size,"\n";
	close(FP);
	my $co = $al->ToBuechi;
	my $endi = time();
	open(FP,">>states");
	open(WP,">>WAAd");
	print WP "done ",$endi - $stti,"\n";
	close(WP);
	print FP $$co{states}->Size," ";
	print $co->ToString,"\n" if $verb > 2;
	$co->MergeTransitions;
	print $co->ToString,"\n" if $verb > 2;
	$co->DirectSimulationMinimization;
	print $co->ToString,"\n" if $verb > 2;
	open(FP2,">>reduceheightwk");
	print FP2 $$co{states}->Size," ";
	$co->ReduceHeight;
	print FP2 $$co{states}->Size,"\n ";
	close(FP2);
	print $co->ToString,"\n" if $verb > 2;
	$co->FairSimulationMinimization;
	$co->MergeTransitions;
	$co->Prune;
	print FP $$co{states}->Size,"\n";
	close(FP);
	unless ($co->IsIntersectionEmpty($bl)) {
	    open(FP,">>out1000ltl13");
	    print "Intersection not empty\n";
	    close(FP);
	    exit 0;
	}
       	#alarm 0;
	print "complement\n" if $verb > 2;
	print $co->ToString,"\n" if $verb > 2;
	print $co->ToDot("comp") if $verb > 2;
	return $co;
    }
} #Complement

######################################################################
# Compute expanded fair sets by adding to a fair set all states such
# that all cycles through them intersect the fair set.  This is done
# by finding those states such that all paths from them that are
# confined to their SCC intersect the fair set.
######################################################################
sub ComputeExpandedFairSets {
    my $self = shift;
    my $states = $$self{states};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $inverse = InvertDelta($states,$delta);

    # Find SCCs.
    my $classes = $self->SCC;

    my $result = Set->new;
    foreach my $fairset (values %{$fair}) {
	my $expanded = Set->new;
	foreach my $class (values %{$classes}) {
	    if ($class->Size == 1) {
		# SCCs with just one state are treated separately,
		# because they may be trivial.  If there are no cycles
		# the treatment below is incorrect.  The solution we
		# use for the singleton case is correct regardless of
		# the presence of a self-loop.
		$expanded->Add($class->Intersection($fairset));
	    } else {
		# Compute AF p as !EG !p.  The universe is the current SCC.
		my $z = $class->Difference($fairset);
		my $zeta = Set->new;
		while (not $z->IsEqual($zeta)) {
		    $zeta = $z->Clone;
		    $z = Set->new;
		    foreach my $state (values %{$zeta}) {
			$z->Add($$inverse{$state});
		    }
		    $z->Restrict($zeta);
		}
		$expanded->Add($class->Difference($z));
	    }
	}
	$result->Push($expanded);
	if ($expanded->Size > $fairset->Size) {
	 #   print "Expansion from ",
	  #    $self->StateRelationToNameString($fairset), "\n to ",
	   #   $self->StateRelationToNameString($expanded), "\n\n";
	} elsif (not $expanded->IsEqual($fairset)) {
	   # print "Error in expanding ",
	    #  $self->StateRelationToNameString($fairset), "\n to ",
	     # $self->StateRelationToNameString($expanded), "\n\n";
	}
    }

    return $result;

} # ComputeExpandedFairSets


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
	    $image->Add($$delta{$state});
	}
	$new = $image->Difference($reached);
	$reached->Add($image);
    }
    return $reached;

} # Reachable


######################################################################
# Computes the transitive closure of an automaton by iterated squaring.
######################################################################
sub TransitiveClosure {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my %closure = ();
    foreach my $state (values %{$states}) {
	$closure{$state} = $$delta{$state}->Clone($state);
    }
    while (1) {
	my $change = 0;
	foreach my $state (keys %{$states}) {
	    my $old = $closure{$state};
	    my $new = $old->Clone;
	    foreach my $otherstate (keys %{$old}) {
		$new->Add($closure{$otherstate});
	    }
	    unless ($new->Size == $old->Size) {
		$closure{$state} = $new;
		$change = 1;
	    }
	}
	last unless $change == 1;
    }
    return \%closure;

} # TransitiveClosure


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
	foreach my $succ (keys %{$image}) {
	    $inverse{$succ}->Push($state);
	}
    }
    return \%inverse;

} # InvertDelta


######################################################################
# Returns 1 if an automaton is weak; "" otherwise.
######################################################################
sub IsWeak {
    my $self = shift;
    my $scc = $self->SCC;
    my $fair = $$self{fair};
    my $ok = 1;
    foreach my $component (values %{$scc}) {
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
# Returns:
#   "terminal" if the automaton is terminal;
#   "weak"   if an automaton is weak;
#   "strong" otherwise.
######################################################################
sub Strength {
    my $self = shift;
    my $delta = $$self{delta};
    my $labels = $$self{labels};
    my $quotient = $self->Quotient($self->SCC);
    my $scc = $$quotient{states};
    my $fair = $$self{fair};
    my $ok = 1;
    # Check for weakness and collect fair SCCs.
    my $faircomp = Set->new;
  COMP: foreach my $component (values %{$scc}) {
	foreach my $fairset (values %{$fair}) {
	    if ($component->IsDisjoint($fairset)) {
		$ok = 1;
		next COMP;
	    }
	    $ok = 0 unless $component->IsIncluded($fairset);
	}
	return "strong" if $ok == 0;
	$faircomp->Push($component);
    }
    # Check for terminality.
    # Collect conclusive SCCs.  An SCC is conclusive if it is complete
    # and all its successors (excluding itself) have been proved conclusive.
    # SCCs are added to the conclusive set bottom-up, starting with terminal
    # SCCs.
    my $conclusive = Set->new;
    my $change = 1;
    while ($change) {
	$change = 0;
	foreach my $component (values %{$faircomp}) {
	    my $imageQ = $$quotient{delta}{$component};
	    if ($imageQ->IsIncluded($conclusive->Clone($component))) {
		foreach my $state (values %{$component}) {
		    my $image = $$delta{$state};
		    my $cover = Cover->new;
		    foreach my $successor (values %{$image}) {
			$cover->Push($$labels{$successor}) if ref($self) eq "Buechi";
			$cover->Push($successor->First) if ref($self) eq "BuechiAL";
		    }
		    return "weak" unless $cover->IsTautology;
		}
		# At this point the fair SCC is complete.
		$conclusive->Push($component);
		$faircomp->Delete($component);
		$change = 1;
	    }
	}
    }
    # The automaton is terminal if all fair SCCs are conclusive.
    return $faircomp->Size == 0 ? "terminal" : "weak";

} # Strength


######################################################################
# Computes the strongly connected components of an automaton.
# Tarjan's algorithm as described in Aho, Hopcroft, and Ullman,
# The Design and Analysis of Computer Algorithms.
######################################################################
sub SCC {
    my $self = shift;
    my %old = ();
    my @stack = ();
    my %onstack = ();
    my %dfnumber = ();
    my %lowlink = ();
    my $scc = Set->new;
    my $init = $$self{init};
    my $count = 0;
    foreach my $initial (values %{$init}) {
	unless (exists $old{$initial}) {
	    searchSCC($self,$initial,$scc,\%old,\@stack,\%onstack,
		      \%dfnumber,\%lowlink,\$count);
	}
    }
    return $scc;

} # SCC


######################################################################
# DFS for the computation of the strongly connected components.
######################################################################
sub searchSCC {
    my ($self,$v,$scc,$old,$stack,$onstack,$dfnumber,$lowlink,$countr) = @_;
    $$old{$v} = 1;
    $$lowlink{$v} = $$dfnumber{$v} = $$countr;
    ${$countr}++;
    push(@{$stack},$v);
    $$onstack{$v} = 1;
    my $delta = $$self{delta};
    foreach my $w (values %{$$delta{$v}}) {
	unless (exists $$old{$w}) {
	    searchSCC($self,$w,$scc,$old,$stack,$onstack,
		      $dfnumber,$lowlink,$countr);
	    $$lowlink{$v} = $$lowlink{$w} if $$lowlink{$w} < $$lowlink{$v};
	} else {
	    if ($$dfnumber{$w} < $$dfnumber{$v} && exists $$onstack{$w}) {
		$$lowlink{$v} = $$dfnumber{$w}
		  if $$dfnumber{$w} < $$lowlink{$v};
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
	$scc->Push($component);
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
	foreach my $otherstate (values %{$succ}) {
	    my $dest = $map{$otherstate};
	    $deltaQ{$source}->Push($dest);
	}
    }
    my $fairsetQ = $partition->Clone;
    # Remove SCCs consisting of one state only unless the state has
    # a self-loop.
    foreach my $class (values %{$fairsetQ}) {
	if ($class->Size == 1) {
	    my $state = $class->Pick;
	    $fairsetQ->Delete($class) unless $$delta{$state}->IsMember($state);
	}
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
# Return 1 if the language of a nongeneralized Buechi automaton is empty.
######################################################################
sub IsEmpty {
    my $self = shift;
    my $init = $$self{init};
    my $fair = $$self{fair};
    my %onstack = ();
    my %visited = ();
    my %flagged = ();
    die "IsEmpty only works for non-generalized automata\n"
      unless $fair->Size <= 1;
    my $fairset = $fair->Pick;
    if ($fair->Size == 0) { #all states are accepting
	$fairset = $$self{states};
    }
    foreach my $initial (values %{$init}) {
	unless (exists $visited{$initial}) {
	    return "" unless outerDFS($self,$initial,\%onstack,\%visited,
				      \%flagged,$fairset);
	}
    }
    return 1;

} # IsEmpty


######################################################################
# Outer DFS for the language emptiness check.
# Return "" as soon as the language has been found to be nonempty.
######################################################################
sub outerDFS {
    my ($self,$v,$onstack,$visited,$flagged,$fairset) = @_;
    $$visited{$v} = 1;
    $$onstack{$v} = 1;
    my $delta = $$self{delta};
    foreach my $w (values %{$$delta{$v}}) {
	unless (exists $$visited{$w}) {
	    return "" unless outerDFS($self,$w,$onstack,$visited,
				      $flagged,$fairset);
	}
    }
    if ($fairset->IsMember($v)) {
	return "" unless innerDFS($self,$v,$onstack,$flagged);
    }
    delete $$onstack{$v};
    return 1;

} # outerDFS


######################################################################
# Inner DFS for the language emptiness check.
# Return "" as soon as the language has been found to be nonempty.
######################################################################
sub innerDFS {
    my ($self,$v,$onstack,$flagged) = @_;
    $$flagged{$v} = 1;
    my $delta = $$self{delta};
    foreach my $w (values %{$$delta{$v}}) {
	return "" if exists $$onstack{$w};
	unless (exists $$flagged{$w}) {
	    return "" unless innerDFS($self,$w,$onstack,$flagged);
	}
    }
    return 1;

} # innerDFS


######################################################################
# Return 1 if a set of states forms a clique.
######################################################################
sub IsClique {
    my ($self, $set) = @_;
    my $delta = $$self{delta};
    foreach my $state (values %{$set}) {
	my $image = $$delta{$state};
	return "" unless $set->IsIncluded($image);
    }
    return 1;

} # IsClique


######################################################################
# Finds the least upper bound of the labels of a set of states and
# a (possibly empty) list of the states that have such label.
######################################################################
sub labelLUB {
    my ($self, $set) = @_;
    my $labels = $$self{labels};
    my @greatest = ();
    my $lub = undef;
    foreach my $state (values %{$set}) {
	my $label = $$labels{$state};
	if (defined($lub) and $label->IsEqual($lub)) {
	    push(@greatest,$state);
	} elsif (!defined($lub) or $label->IsIncluded($lub)) {
	    $lub = $label;
	    @greatest = ($state);
	} elsif (!$lub->IsIncluded($label)) {
	    my $cover = Cover->new($lub,$label);
	    $lub = $cover->Supercube;
	    @greatest = ();
	}
    }
    return ($lub,\@greatest);

} # labelLUB


######################################################################
# Finds the greatest lower bound of the labels of a set of states and
# a state that has such label if one exists.
######################################################################
sub labelGLB {
    my ($self, $set) = @_;
    my $labels = $$self{labels};
    my $least = undef;
    my $glb = Set->new;
    foreach my $state (values %{$set}) {
	$glb->Add($$labels{$state});
	if (Contradiction($glb)) {
	    return (LTL->new("FALSE"),undef);
	} elsif (!defined($least) or !$glb->IsEqual($$labels{$least})) {
	    if ($glb->IsEqual($$labels{$state})) {
		$least = $state;
	    } else {
		$least = undef;
	    }
	}
    }
    return ($glb,$least);

} # labelGLB


######################################################################
# Completes the transition relation of an automaton.
######################################################################
sub MakeComplete {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $labels = $$self{labels};
    my $trap = undef;
    foreach my $state (values %{$states}) {
	my $image = $$delta{$state};
	my $cover = Cover->new;
	foreach my $successor (values %{$image}) {
	    $cover->Push($$labels{$successor});
	}
	unless ($cover->IsTautology) {
	    unless (defined $trap) {
		$trap = Set->new;
		$self->AddState(
				state => $trap,
				delta => Set->new($trap),
				name => "trap"
			       );
	    }
	    $$delta{$state}->Push($trap);
	}
    }
    # Fix fair sets.
    my $fair = $$self{fair};
    if ($fair->Size == 0 && defined $trap) {
	my $fairset = $states->Difference(Set->new($trap));
	$fair->Push($fairset);
    }

} # MakeComplete


######################################################################
# Builds the intersection of two automata.
######################################################################
sub Intersection {
    my ($self,$other) = @_;
    my $sstates = $$self{states};
    my $sinit = $$self{init};
    my $sdelta = $$self{delta};
    my $slabels = $$self{labels};
    my $snames = $$self{names};
    my $sfair = $$self{fair};
    my $ostates = $$other{states};
    my $oinit = $$other{init};
    my $odelta = $$other{delta};
    my $olabels = $$other{labels};
    my $onames = $$other{names};
    my $ofair = $$other{fair};
    my %delta = ();
    my %labels = ();
    my %names = ();
    # The initial states of the intersection are those pairs of initial
    # states such that their labels are compatible.
    my $init = Cartesian($sinit,$oinit);
    foreach my $newstate (values %{$init}) {
	my $sstate = $newstate->First;
	my $ostate = $newstate->Second;
	my $label = $$slabels{$sstate}->Union($$olabels{$ostate});
	if (Contradiction($label)) {
	    $init->Delete($newstate);
	} else {
	    $labels{$newstate} = $label;
	    $names{$newstate} = Pair->new($$snames{$sstate},
					  $$onames{$ostate})->ToString;
	}
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
	my $image = Cartesian($simage,$oimage);
	my $new = $image->Difference($states);
	foreach my $newstate (values %{$new}) {
	    my $sstate = $newstate->First;
	    my $ostate = $newstate->Second;
	    my $label = $$slabels{$sstate}->Union($$olabels{$ostate});
	    if (Contradiction($label)) {
		$new->Delete($newstate);
		$image->Delete($newstate);
	    } else {
		$labels{$newstate} = $label;
		$names{$newstate} = Pair->new($$snames{$sstate},
					      $$onames{$ostate})->ToString;
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
    return Buechi->new(
		       states => $states,
		       init   => $init,
		       delta  => \%delta,
		       names  => \%names,
		       labels => \%labels,
		       fair   => $fair
		      );

} # Intersection


######################################################################
# Computes the Cartesian product of two sets.
######################################################################
sub Cartesian {
    my ($first,$second) = @_;
    my $product = Set->new;
    foreach my $felement (values %{$first}) {
	foreach my $selement (values %{$second}) {
	    my $element = Pair->new($felement, $selement);
	    $product->Push($element);
	}
    }
    return $product;

} # Cartesian


######################################################################
# Returns 1 if the label contains contradictory atoms.
######################################################################
sub Contradiction {
    my $label = shift;
    foreach my $atom (values %{$label}) {
	my $negation = $atom->Negate;
	return 1 if $label->IsMember($negation);
    }
    return "";

} # Contradiction


######################################################################
# Builds the union of two automata.
######################################################################
sub Union {
    my ($self,$other) = @_;
    my $sstates = $$self{states};
    my $sinit = $$self{init};
    my $sdelta = $$self{delta};
    my $slabels = $$self{labels};
    my $snames = $$self{names};
    my $sfair = $$self{fair};
    my $ostates = $$other{states};
    my $oinit = $$other{init};
    my $odelta = $$other{delta};
    my $olabels = $$other{labels};
    my $onames = $$other{names};
    my $ofair = $$other{fair};
    my %delta = ();
    my %labels = ();
    my %names = ();
    my $states0 = Set->new;
    my $states1 = Set->new;
    my $init = Set->new;
    my $dummy = Set->new;
    # Make states unique, and merge the two sets.
    foreach my $sstate (values %{$sstates}) {
	my $state = Pair->new($sstate,$dummy);
	$states0->Push($state);
	$init->Push($state) if $sinit->IsMember($sstate);
	my $simage = $$sdelta{$sstate};
	my $image = Set->new;
	foreach my $ssucc (values %{$simage}) {
	    my $succ = Pair->new($ssucc,$dummy);
	    $image->Push($succ);
	}
	$delta{$state} = $image;
	$labels{$state} = $$slabels{$sstate};
	$names{$state} = $$snames{$sstate} . "-0";
    }
    foreach my $ostate (values %{$ostates}) {
	my $state = Pair->new($dummy,$ostate);
	$states1->Push($state);
	$init->Push($state) if $oinit->IsMember($ostate);
	my $oimage = $$odelta{$ostate};
	my $image = Set->new;
	foreach my $osucc (values %{$oimage}) {
	    my $succ = Pair->new($dummy,$osucc);
	    $image->Push($succ);
	}
	$delta{$state} = $image;
	$labels{$state} = $$olabels{$ostate};
	$names{$state} = $$onames{$ostate} . "-1";
    }
    # Fix fair sets.
    my $fair = Set->new;
    foreach my $sfairset (values %{$sfair}) {
	my $fairset = $states1->Clone;
	foreach my $sstate (values %{$sfairset}) {
	    my $state = Pair->new($sstate,$dummy);
	    $fairset->Push($state);
	}
	$fair->Push($fairset);
    }
    foreach my $ofairset (values %{$ofair}) {
	my $fairset = $states0->Clone;
	foreach my $ostate (values %{$ofairset}) {
	    my $state = Pair->new($dummy,$ostate);
	    $fairset->Push($state);
	}
	$fair->Push($fairset);
    }
    my $states = $states0->Union($states1);
    return Buechi->new(
		       states => $states,
		       init   => $init,
		       delta  => \%delta,
		       names  => \%names,
		       labels => \%labels,
		       fair   => $fair
		      );


} # Union


######################################################################
# Returns a statistics string about an automaton.
######################################################################
sub Stats {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $fair = $$self{fair};
    my $init = $$self{init};
    my $stats = $self->NumberOfStates . " states, " .
      $self->NumberOfTransitions . " trans, " .
	$self->NumberOfFairSets . " fair sets, " .
	  $self->NumberOfInitialStates . " init states, " .
	    $self->Strength;
    return $stats;

} # Stats


######################################################################
# Returns the number of states of an automaton.
######################################################################
sub NumberOfStates {
    my $self = shift;
    return $$self{states}->Size;

} # NumberOfStates


######################################################################
# Returns the number of transitions of an automaton.
######################################################################
sub NumberOfTransitions {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $transitions = 0;
    foreach my $state (values %{$states}) {
	$transitions += $$delta{$state}->Size;
    }
    return $transitions;

} # NumberOfTransitions


######################################################################
# Returns the number of fair sets of an automaton.
######################################################################
sub NumberOfFairSets {
    my $self = shift;
    return $$self{fair}->Size;

} # NumberOfFairSets


######################################################################
# Returns the number of initial states of an automaton.
######################################################################
sub NumberOfInitialStates {
    my $self = shift;
    return $$self{init}->Size;

} # NumberOfInitialStates


######################################################################
# Convert an automaton into a string.
######################################################################
sub ToString {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $labels = $$self{labels};
    my $names = $$self{names};
    my $fair = $$self{fair};
    my $string = "States\n";
    foreach my $state (values %{$states}) {
	$string .= $$names{$state} . ": " . $state->ToString;
	if (defined($$labels{$state})) {
	    $string .= " label: " . $$labels{$state}->ToString;
	}
	$string .= "\n";
    }
    $string .= "Arcs\n";
    foreach my $state (values %{$states}) {
	$string .= ($init->IsMember($state) ? "-> " : "   ") .
	  $$names{$state} . " -> ";
	my $next = $$delta{$state};
	$string .= $self->StateRelationToNameString($next) . "\n";
    }
    # Convert accepting conditions.
    $string .= "Fair Sets\n";
    foreach my $fairset (values %{$fair}) {
	# This is to accommodate Streett fairness constraints.
	if ((ref($fairset) eq "Pair") && (ref($self) ne "Alternating")) {
	    #print "fair is pair\n";
	    $string .= $self->StateRelationToNameString($fairset->First)
	      . " -> " . $self->StateRelationToNameString($fairset->Second)
		. "\n";
	} else {
	    $string .= $self->StateRelationToNameString($fairset) . "\n";
	}
    }
    $string .= "End\n";
    return $string;

} # ToString


######################################################################
# Convert a relation over states into a string of names.
# The tuples of the relation must be (possibly nested) pairs.
######################################################################
sub StateRelationToNameString {
    my ($self,$relation) = @_;
    my $names = $$self{names};
    my $string .= "{";
    my $delim = "";
  #  if ($relation->Size == 0) {
	#$string = " FALSE ";
    #}
    #else {
	foreach my $tuple (values %{$relation}) {
	    my $name = GetTupleName($tuple,$names);
	    $string .= $delim . $name;
	    $delim = ",";
	}
	$string .= "}";
    #}
    return $string;

} # StateRelationToNameString


######################################################################
# Recursively convert a tuple of states into a name.
######################################################################
sub GetTupleName {
    my ($tuple,$names) = @_;
    if (defined $$names{$tuple}) {
	return $$names{$tuple};
    } elsif (ref($tuple) eq "Pair") {
	my $first = $tuple->First;
	my $second = $tuple->Second;
	#print ref($first->Pick);
	my $fname = GetTupleName($first,$names);
	my $sname = GetTupleName($second,$names);
#	print "[" ,$fname,",", $sname, "]";
	return "[" . $fname . "," . $sname . "]";
    } elsif ((ref($tuple) eq "Set") ||
	     (ref($tuple) eq "UniqSet")) {
	my $delim = "";
	my $string = "";
	foreach my $element (values %{$tuple}) {
	    my $name = GetTupleName($element,$names);
	    $string .= $delim.$name;
	    $delim = ",";
	}
	#print "{",$string,"}";
	return "{".$string."}";
    }
    elsif (ref($tuple) eq "LTL") {
	#print $tuple->ToString;
	return $tuple->ToString;
    }
    else {
	#print ref($tuple);
	die " Unexpected object type ";
    }

} # GetTupleName


######################################################################
# Converts an automaton to dot format.
######################################################################
sub ToDot {
    my ($self,$graphname) = @_;
    my $nodes = $$self{states};
    my $fair = $$self{fair};
    my $names = $$self{names};
    my $labels = $$self{labels};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my %fairness = ();
    foreach (values %{$nodes}) {
	$fairness{$_} = "(";
    }
    my $i = 1;
    foreach my $fairset (values %{$fair}) {
	# Hack to deal with Streett game automata.
	if (ref($fairset) eq "Pair") {
	    my $antecedent = $fairset->First;
	    my $consequent = $fairset->Second;
	    foreach my $node (values %{$antecedent}) {
		$fairness{$node} .= "," unless $fairness{$node} eq "(";
		$fairness{$node} .= "a" . $i;
	    }
	    foreach my $node (values %{$consequent}) {
		$fairness{$node} .= "," unless $fairness{$node} eq "(";
		$fairness{$node} .= "c" . $i;
	    }
	} else {
	    foreach my $node (values %{$fairset}) {
		$fairness{$node} .= "," unless $fairness{$node} eq "(";
		$fairness{$node} .= $i;
	    }
	}
	$i++;
    }
    foreach (values %{$nodes}) {
	$fairness{$_} .= ")";
    }
    my $string = qq!digraph "$graphname" {\nnode [shape=ellipse];\n!;
    $string .= qq!size = \"11,7.5\";\ncenter = true;\nrotate = 90;\n!;
    $string .= qq!"title" [label=\"$graphname\",shape=plaintext];\n!;
    foreach my $node (values %{$nodes}) {
	my $label = ((ref($self) eq "BuechiAL") || (ref($self) eq "CoBuechi")
		     || (ref($self) eq "Alternating"))?
	             "":$$labels{$node}->ToString."\\n";
	$string .= qq!"$$names{$node}" [label=\"$$names{$node}\\n$label$fairness{$node}\"];\n!;
	my $next = $$delta{$node};
	foreach my $succ (values %{$next}) {
	    if (ref($self) eq "BuechiAL") {
		my $slabel = $succ->First->ToString;
		my $dest = $succ->Second;
		$string .= qq!"$$names{$node}" -> "$$names{$dest}" [label="$slabel"];\n!;
	    }
	    elsif (ref($self) eq "CoBuechi") {
		my $slabel = $succ->First->ToString;
		my $nlabel = $slabel;
		$nlabel =~ s/{//;
		$nlabel =~ s/}//;
		$nlabel =~ s/=//;
		my $dest = $succ->Second;
		if ($dest->Size == 1) {
		    my $destnode = $dest->Pick;
		    $string .= qq!"$$names{$node}" -> "$$names{$destnode}"[label="$slabel"];\n!;
		}
		else {
		    $string .= qq!"$$names{$node}" -> "tri$nlabel$$names{$node}"[label="$slabel"];\n!;
		    $string.= qq!"tri$nlabel$$names{$node}" [label="",shape=triangle,height=0.2,width=0.2];\n!;
		    foreach my $succnode (values %{$dest}) {
			$string .= qq!"tri$nlabel$$names{$node}" -> "$$names{$succnode}";\n!;
		    }
		}
	    }
	    elsif (ref($self) eq "Alternating") {
		my $slabel = $succ->First->ToString;
		my $nlabel = $slabel;
		$nlabel =~ s/{//;
		$nlabel =~ s/}//;
		$nlabel =~ s/=//;
		my $destset = $succ->Second;
		my $i=1;
		my $j=1;
		foreach my $dest (values %{$destset}) {
		    if ($dest->Size == 0) {
			$string .= qq!"$$names{$node}" -> "truenode$j"[label="$slabel"];\n!;
			$string .= qq!"truenode$j" [style=filled,
                                         color=white,label="TRUE"]\n!;
			$j++;
		    }
		    elsif (($dest->Size == 1)) {
			my $destnode = $dest->Pick;
			$string .= qq!"$$names{$node}" -> "$$names{$destnode}"[label="$slabel"];\n!;
		    }
		    else {
			$string .= qq!"$$names{$node}" -> "tri$nlabel$$names{$node}$i"[label="$slabel"];\n!;
			$string.= qq!"tri$nlabel$$names{$node}$i" [label="",shape=triangle,height=0.2,width=0.2];\n!;
			foreach my $succnode (values %{$dest}) {
			    $string .= qq!"tri$nlabel$$names{$node}$i" -> "$$names{$succnode}";\n!;
			}
			$i++;
		    }
		}
	    }
	    else {
		$string .= qq!"$$names{$node}" -> "$$names{$succ}";\n!;
	    }
	}
	if ($init->IsMember($node)) {
	    my $pred = "init-" . $$names{$node};
	    $string .= qq!"$pred" [style=invis]\n!;
	    $string .= qq!"$pred" -> "$$names{$node}";\n!;
	}
    }
    $string .= qq!}\n!;
    return $string;

} # ToDot


######################################################################
# Converts a string into an automaton.
# The string must use the format produced by ToString.
######################################################################
sub FromString {
    my %params = @_;
    my $string;
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
    my $states = Set->new;
    my $init = Set->new;
    my %delta = ();
    my %labels = ();
    my %names = ();
    my %statemap = ();
    my $fair = Set->new;
    # my $count = 0;
    my $state = "start";
    while (defined $string) {
	my $line;
	($line,$string) = split(/^/m, $string, 2);
	# print $count++, ": ", $line;
	chop $line;
	# Remove comments and trailing spaces, and skip empty lines.
	$line =~ s/\s*\#.*//;
	$line =~ s/\s+$//;
	next if $line eq "";
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
		unless ($line =~ s/\s+label:\s*({.*})//) {
		    die "missing label specification";
		}
		my $labelspec = $1;
		my $label = BuildState($labelspec);
		my $state = BuildState($line);
		$statemap{$name} = $state;
		$names{$state} = $name;
		$labels{$state} = $label;
		$states->Push($state);
		# print "State: ", $name, ": ", $state->ToString, "\n";
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
		my @successors = SplitStateList($line);
		my $img = Set->new;
		foreach my $succ (@successors) {
		    my $sstate = $statemap{$succ};
		    $img->Push($sstate);
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
		my @fairstates = SplitStateList($line);
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
    my $self = Buechi->new(
			   states => $states,
			   init   => $init,
			   delta  => \%delta,
			   names  => \%names,
			   labels => \%labels,
			   fair   => $fair);
    # print $self->ToString;
    return $self;

} # FromString


######################################################################
# Build a set or pair from a string describing a state.
######################################################################
sub BuildState {
    my $string = shift;
    my $state;

    if ($string =~ s/^\{//) {
	($state,$string) = SetState($string);
	$string   =~ s/^\}// || die "Missing right brace: $string\n";
    } elsif ($string =~ s/^\[//) {
	($state,$string) = PairState($string);
	$string   =~ s/^\]// || die "Missing right bracket: $string\n";
    } elsif ($string =~ s/^([^\[\{].*)//) {
	$state = Set->new($1);
    }

    return $state;

} # BuildState


######################################################################
# Convert a bracketed list to a set of nested pairs.
######################################################################
sub PairState {
    my $string = shift;
    my $first;
    my $second;
    if ($string =~ s/^\[//) {
	($first,$string) = PairState($string);
	$string   =~ s/^\]// || die "Missing right bracket: $string\n";
    } elsif ($string =~ s/^\{//) {
	($first,$string) = SetState($string);
	$string   =~ s/^\}// || die "Missing right brace: $string\n";
    } elsif ($string =~ s/^([^\,]+)//) {
	$first = $1;
    }
    $string   =~ s/^\,// || die "Missing comma: $string\n";
    if ($string =~ s/^\[//) {
	($second,$string) = PairState($string);
	$string   =~ s/^\]// || die "Missing right bracket: $string\n";
    } elsif ($string =~ s/^\{//) {
	($second,$string) = SetState($string);
	$string   =~ s/^\}// || die "Missing right brace: $string\n";
    } elsif ($string =~ s/^([^\,\]]+)//) {
	$second = $1;
    }
    my $pair = Pair->new($first,$second);
    return ($pair,$string);

} # PairState


######################################################################
# Convert a list of formulae in braces into a set of LTL formulae.
# However, if a formula does not contain "=", is it not an LTL
# formula, and is regarded as a simple string.
######################################################################
sub SetState {
    my $string = shift;
    my $set = Set->new;
    while ($string =~ s/^([^\,\}]+)//) {
	my $formula = $1;
	if ($formula =~ m/=/) {
	    $set->Push(LTL->new($formula));
	} else {
	    $set->Push($formula);
	}
	$string =~ s/^\,//;
    }
    return ($set,$string);

} # SetState


######################################################################
# Split a comma-separated list of state names into a list.  The names
# may also contain commas as in [a,[b,c]].  Hence we count the left
# brackets and the commas to know when a name finishes.
######################################################################
sub SplitStateList {
    my $string = shift;
    my @list = ();
    while ($string ne "") {
	my $leftbrackets = 0;
	my $commas = 0;
	my $i;
	for ($i = 0; $i < length($string); $i++) {
	    my $first = substr($string,$i,1);
	    if ($first eq "[") {
		$leftbrackets++;
	    } elsif ($first eq ",") {
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

} # SplitStateList

######################################################################
#   Time out handler
######################################################################
sub timeouthandler {
    my $sig = shift;
    open (FP,">>out1000ltl13");
    print FP "timeout occured \n";
    print "timeout occured \n";
    close(FP);
    exit 0;
}
# Required return value.


######################################################################
# Apply Counting Construction to reduce the fairness conditions to 1.
######################################################################
sub CountingConstruction {
    my $self = shift;
    my $states = $$self{states};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $labels = $$self{labels};
    my $names = $$self{names};

    my $fairNo =  $fair->Size;
    return $self if ($fairNo <= 1);

    #make LTL-expressions for fairness sets
    my %exps = ();
    my %fairSets = ();
    my $i = 0;
    foreach my $fset (values %$fair) {
	$exps{$i} = LTL->new("F$i=1");
	$fairSets{$i} = $fset;
	$i++;
    }
    #make fair layer
    $exps{$fairNo} = LTL->new("F$fairNo=1");
    $fairSets{$fairNo} = $states;
    
    #copy copies, names, and labels
    my $ccstates = Cover->new;
    my %cclabels = ();
    my %ccnames  = ();
    my %match = ();
    my $ccstate;
    foreach my $state (values %$states) {
	$match{$state} = ();
	foreach my $e (keys %exps) {
	    if (ref $state eq "Pair") {
		$ccstate = Set->new;
		$ccstate->Push($state->First);
		$ccstate->Push($state->Second);
	    } else {
		$ccstate = $state->Clone;
	    }
	    $ccstate->Push($exps{$e});
	    $ccstates->Push($ccstate);
	    $match{$state}{$e} = $ccstate;
	    $ccnames{$ccstate} = $$names{$state}."F".$e;
	    $cclabels{$ccstate} = $$labels{$state};
	}
    }
    #print $match{$states->Pick}{"0"}->ToString(\%ccnames)."\n";
    #print $match{$states->Pick}{"1"}->ToString(\%ccnames)."\n";
    #print "SC".$ccstates->ToString(\%ccnames)."\n";

    #make init
    my $ccinit = Set->new;
    foreach my $state (values %$init) {
	$ccinit->Push($match{$state}{"0"});
    }
    #print "I :".$init->ToString($names)."\n";
    #print "IC:".$ccinit->ToString(\%ccnames)."\n";

    #make fairness
    my $fairC = Set->new;
    foreach my $state (values %{$fairSets{$fairNo}}) {
	$fairC->Push($match{$state}{$fairNo});
    }
    my $ccfair = Set->new($fairC);
    #print "FC:".$ccfair->ToString(\%ccnames)."\n";

    #make transition relation
    my %ccdelta = ();
    foreach my $state (values %$states) {
	my $image = $$delta{$state}; #set of states
	#print  $state->ToString($names)."->".$image->ToString($names)."\n";
	foreach my $e (keys %exps) {
	    my $nxt = ($e eq $fairNo)? 0 : $e+1;
	    my $ccimage = Set->new;
	    foreach my $succ (values %$image) {
		if ($fairSets{$e}->IsMember($state)) {
		    $ccimage->Push($match{$succ}{$nxt});
		} else {
		    $ccimage->Push($match{$succ}{$e});
		}
	    }
	    $ccdelta{$match{$state}{$e}} = $ccimage;
	    #print  $match{$state}{$e}->ToString(\%ccnames)."->".$ccimage->ToString(\%ccnames)."\n";
	}
    }

    my $cc = Buechi->new( states => $ccstates,
			  init   => $ccinit,
			  fair   => $ccfair,
			  delta  => \%ccdelta,
			  labels => \%cclabels,
			  names  => \%ccnames);
    return $cc;
}

######################################################################
# CheckTypes
######################################################################
sub CheckTypes {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $labels = $$self{labels};
    my $names = $$self{names};
    my $dontcares = $$self{dontcares};
    
    print "NBW CheckTypes ";
    #TODO: depending on the way the automaton is constructed the
    # type of the state and the init set is different
    die "NBW wrong state set" if ((ref($states) ne "Cover") &&
				  (ref($states) ne "Set"));
    die "NBW wrong delta" if (ref($delta) ne "HASH");
    die "NBW wrong init" if ((ref($init) ne "Cover") &&
			     (ref($init) ne "Set"));
    die "NBW wrong fair" if (ref($fair) ne "Set");

    foreach my $state (values %$states) {
	my $image = $$delta{$state};
	die "NBW wrong image" if (ref($image) ne "Set");
	foreach my $dest (values %$image) {
	    die "NBW wrong dest" if (ref($dest) ne "Set");
	}
    }

    print "done\n";
    return 1;
}


#############################################################
# Project to variables not in variable list
#############################################################
sub Project {
    my ($self, $variables) = @_;
    my $states = $self->{states};
    my $names  = $self->{names};
    my $labels = $self->{labels};

    #make letters
    my $letters = Set->new;
    my $l;
    foreach my $var (values %{$variables}) {
	$l = LTL->new($var."=0");
	$letters->Push($l);
	$l = LTL->new($var."=1");
	$letters->Push($l);
    }
    
    foreach my $state (values %$states) {
 	my $label = $labels->{$state};
 	$label->Subtract($letters);
# 	print $self->{labels}->{$state}->ToString,"\n";
    }
}

1;
