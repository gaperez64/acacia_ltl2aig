######################################################################
# Functions to reduce labels of Buechi automata, hopefully toward
# the goal of reducing the number of additional state variables needed.
# Written as additional methods for the Buechi.pm package
#
# For ECEN 5139, Fabio Somenzi, Fall 2000
#
# Author: Matthew Lovell <lovell@indra.com>
#
######################################################################

package Buechi;

use POSIX;
use Data::Dumper;         # for debug uses

$RDEBUG = 0;

######################################################################
# Extract all variables from atomic propositions
#
sub ExtractVars {
  my $self = shift;

  my $states    = $self->{states};
  my $labels    = $self->{labels};
  my $names     = $self->{names};
  my $dontcares = $self->{dontcares};

  # return if extraction has already been performed
  return if (exists $self->{label_vars});

  # initialize new structures
  $self->{label_vars} = [];
  $self->{label_enc}  = {};
  $self->{label_vec}  = {};
  my $label_vars = $self->{label_vars};
  my $label_enc  = $self->{label_enc};
  my $label_vec  = $self->{label_vec};

  my %encountered = ();

  # find all variables in state labels
  foreach my $state (values %{$states}) {
    my @atoms = map { $_->Value() } (values %{$labels->{$state}});

    # as long as we're here, extract out values and store them as well
    foreach (@atoms) {
      my ($var, $value) = m/^([\w<>]+)\s*=\s*([01])/;
      unless (exists $encountered{$var}) {
	push(@{$label_vars}, $var);
	$encountered{$var}++;
      }
      $label_enc->{$state}{$var} = $value;
    }
  }

  # Debug information
  if ($RDEBUG) {
    print "Label vars: " . join(" ", @{$label_vars}) . "\n";
    print "Dont Care states: ";
    print join(",", map { $names->{$_} } (keys %{$dontcares})) , "\n";
  }

} # ExtractVars


######################################################################
# Count how many states match each possible encoding of the
# atomic propositions and return the maximum.
#
sub CountOverlap {
  my $self = shift;

  my $states    = $self->{states};
  my $labels    = $self->{labels};
  my $label_vars = $self->{label_vars};

  my $max_overlap = 0;

  for ($i=0; $i<(2**scalar @{$label_vars}); $i++) {
    my $encoding = EncodeAtoms($label_vars,$i);
    my $count = grep { $labels->{$_}->IsIncluded($encoding) }
      (values %{$states});
    if ($count > $max_overlap) { $max_overlap = $count }
  }

  return $max_overlap;

} # CountOverlap


######################################################################
# Determine how many extra state variables would be needed
# to encode this automaton, based upon the maximum overlap
# of state labels for a given encoding of propositional vars.
#
sub CountExtraVars {
  my $self = shift;

  $self->ExtractVars();
  my $overlap = $self->CountOverlap();
  return 0 if ($overlap == 0);
  my $extra = ceil(log($overlap)/log(2));
  print "needed state variables = $extra\n" if ($RDEBUG);
  return $extra;

} # CountExtraVars


######################################################################
# Given a list of propositional variables and an integer,
# assign each variable according to the integer's binary value.
#
sub EncodeAtoms {
  my $vars = shift;
  my $number = shift;

  my $encoding = Set->new;
  my $node;
  my @values = reverse(split(//,dec2bin($number)));
  foreach (@{$vars}) {
    my $value = "$_=" . shift(@values);
    $node = LTL::findOrAdd('atom', $value, undef, undef);
    $encoding->Push($node);
  }
  return $encoding;

} # EncodeAtoms


######################################################################
# Reduce nondeterminism in the labels of the Buchi automaton
#
sub ShrinkLabels {
  my $self = shift;
  my $names = $self->{names};

  # local variables for use by called functions
  local $labels = $self->{labels};
  local $label_pairs = $self->FindLabelPairs();

  local $split = 0;

  # Place pairs with most general first state labels first,
  # For ties, sort by the most general second state labels
  local @sorted_pairs =
    sort {
      scalar (values %{$labels->{$a->First}}) <=>
	scalar (values %{$labels->{$b->First}})
	  or
	    scalar (values %{$labels->{$a->Second}}) <=>
	      scalar (values %{$labels->{$b->Second}}) }
      (values %{$label_pairs});

  if ($RDEBUG) {
    print "Sorted Theorem pairs:\n";
    map { print "(" . $names->{$_->First} . "," .
	    $names->{$_->Second} . ")\n" } @sorted_pairs;
  }

  while (scalar @sorted_pairs) {
    my $pair = shift @sorted_pairs;
    $self->TryShrink($pair);
  }

  # always optimize (originally only done if splitting occurred)
  open(UNMIN, ">unminimized.dot");
  print UNMIN $self->ToDot("");
  close(UNMIN);

  $self->Optimize(0);
  return $label_pairs->Size();

} # ShrinkLabels


######################################################################
# Try reducing the label of a particular state (p), given
# a helping state (q)
#
sub TryShrink {
  my $self = shift;
  my $pair = shift;
  my ($p, $q) = ($pair->First, $pair->Second);

  my $labels = $self->{labels};
  my $names = $self->{names};

  print "Considering ($names->{$p},$names->{$q})\n" if ($RDEBUG);

  my ($label_p, $label_q) = ($labels->{$p}, $labels->{$q});

  # Check for label overlap by looking for contradiction
  return if (Contradiction($label_p->Union($label_q)));

  # Form negation of helper state's label
  my $neg = Set->new;
  foreach my $atom (values %{$label_q}) {
    $neg->Push($atom->Negate) unless ($label_p->IsMember($atom->Negate));
  }

  print "  reducer is " . $neg->ToString . "\n" if ($RDEBUG);

  # Each literal in the negation could possible form a
  # new state, via state splitting
  if ((scalar (values %{$neg})) == 1) {
    # only adding a single literal
    my ($atom) = (values %{$neg});
    my $reduced = $label_p->Clone;
    $reduced->Push($atom);
    # disregard if contradiction
    return if (Contradiction($reduced));
    print "  new label: " . $reduced->ToString . "\n" if ($RDEBUG);
    return unless ($self->legal_reduction($p,$q));
    $labels->{$p}->Push($atom);

  } else {
    # disjunction, must split state.  Alter the state itself
    # first, then split thereafter
    my $count = 0;
    my $orig_label = $labels->{$p}->Clone;
    foreach my $atom (values %{$neg}) {
      my $reduced = $label_p->Clone;

      $reduced->Push($atom);
      # disregard if contradiction
      next if (Contradiction($reduced));
      if ($count == 0) {
	$labels->{$p}->Push($atom);
      } else {
	$split = 1; print " SPLITTING\n" if ($RDEBUG);

	my $new_state = $self->split_state($p,$names->{$p} . "_$count");
	$labels->{$new_state} = $orig_label->Clone;
	$labels->{$new_state}->Push($atom);

	print " Added new state $names->{$new_state}\n" if ($RDEBUG);

	# Update the label pairs list to reflect new state
	foreach my $old_pair (grep { $_->First eq $p } (@sorted_pairs)) {
	  push(@sorted_pairs,Pair->new($new_state,$old_pair->Second));
	}
      }
      $count++;
    }

  }

} # TryShrink


######################################################################
# Given a state and a name, split it and return the new state
#
sub split_state {
  my $self = shift;
  my $p    = shift;
  my $name = shift;

  my $states = $self->{states};
  my $init = $self->{init};
  my $fair = $self->{fair};
  my $delta = $self->{delta};
  my $labels = $self->{labels};
  my $names = $self->{names};
  my $dontcares = $self->{dontcares};
  my $inverse = InvertDelta($states,$delta);

  my $new_delta = $delta->{$p}->Clone;
  my $new_label = $labels->{$p}->Clone;
  my $new_dc    = $dontcares->{$p};
  my $new_init  = $init->{$p};

  $new_state = Set->new;
  $self->AddState(
		  state => $new_state,
		  name  => $name,
		  delta => $new_delta,
		  label => $new_label,
		  init  => $new_init,
		  dontcare => $new_dc
		 );

  # copy fairsets
  foreach my $fairset (values %{$fair}) {
    if ($fairset->IsMember($p)) {
      $fairset->Push($new_state);
    }
  }

  # if p self-loops, then the new state should self loop.
  if ($delta->{$p}->IsMember($p)) {
    $delta->{$new_state}->Push($new_state);
    $delta->{$new_state}->Delete($p);
  }

  return $new_state;

} # split_state


######################################################################
# Determine whether a label reduction is safe.  Reducing state
# p's label using state q's is safe if either
#
#  - every predecessor of p is also a predecessor of q or
#
#  - every predecessor of p has *another* simulation equivalent
#    successor whose label is a superset of L(p) conjoined with
#    L(q)  (*** check with Dr. Somenzi ***)
#
sub legal_reduction {
  my $self = shift;
  my $p = shift;
  my $q = shift;

  my $states  = $self->{states};
  my $labels  = $self->{labels};
  my $delta   = $self->{delta};
  my $inverse = InvertDelta($states,$delta);
  my $simul   = $self->{direct_simulation};
  my $names = $self->{names};

  my $reduction = $labels->{$p}->Union($labels->{$q});

 PRED: foreach my $pred (values %{$inverse->{$p}}) {
    next PRED if ($pred eq $p);
    next PRED if ($delta->{$pred}->IsMember($q));

    # now consider successors
    my @successors = grep {
      defined $_ and
      $simul->IsMember(Pair->new($p,$_))
    } (values %{$delta->{$pred}});

  SUCC: foreach my $succ (@successors) {
      next SUCC if ($succ eq $p);
      next PRED if ($labels->{$succ}->IsIncluded($reduction));
    }

    # reduction isn't fine!
    return 0;
  }

  # reduction is fine
  return 1;

} # legal_reduction



######################################################################
# Apply Theorem 23 from unpublished version of "Efficient Buchi
# Automata from LTL Formulae" by F. Somenzi and R. Bloem.
#
# The loops below serve to build up the list of (p,q) states
# where the label of p *may* be reduced by substracting q.
#
sub Theorem23Pairs {
  my $self = shift;

  my $states = $self->{states};
  my $init = $self->{init};
  my $fair = $self->{fair};
  my $delta = $self->{delta};
  my $labels = $self->{labels};
  my $names = $self->{names};
  my $dontcares = $self->{dontcares};
  my $inverse = InvertDelta($states,$delta);

  my $domin = Set->new;

 FIRST: foreach my $p (values %{$states}) {
  SECOND: foreach my $q (values %{$states}) {

      # only insert distinct pairs (p,q)
      next SECOND if $p eq $q;

      # 1. if p in init, then q in init
      next SECOND if ($init->IsMember($p) and
		      !$init->IsMember($q));

      # 2. for each fairset F: if p in F, then q in F
      foreach my $fairset (values %{$fair}) {
	next SECOND if ($fairset->IsMember($p) and
			!$fairset->IsMember($q) and
			!(exists $dontcares->{$q}));
      }

      # 3. ensure that p's successors are a subset of q's successors
      next SECOND unless ($delta->{$p}->IsIncluded($delta->{$q}));

      # 4. ensure predecessors of p (excluding p) are
      # subset of predecessors of q (excluding p)
      my $pred_p = $inverse->{$p}->Difference(Set->new($p));
      my $pred_q = $inverse->{$q}->Difference(Set->new($p));
      next SECOND unless ($pred_p->IsIncluded($pred_q));

      # 5. if p self-loops, then q must self-loop
      next SECOND if ($delta->{$p}->IsMember($p) and
		      !$delta->{$q}->IsMember($q));

      # pairs which make it this far may be interesting!
      $domin->Push(Pair->new($p,$q));
    }
  }

  if ($RDEBUG) {
    print "Theorem 23 pairs:\n";
    map { print "(" . $names->{$_->First} . "," .
	    $names->{$_->Second} . ")\n" } (values %{$domin});
  }
  return $domin->Size();

} # Theorem23Pairs


######################################################################
# Apply a more generalized version of Theorem 23 to find
# pairs of states which *may* be useful in label reduction.
#
# Email from Dr. Somenzi
# ----------------------
#  The extension of Theorem 23 is:
#
#  For each predecessor r of p distinct from p there must exist a
#  successor q of r such that:
#
#    * 2 as in Theorem 23
#
#    * for each successor t of p there must exist a successor u of q
#      that direct-simulates t
#
#  If p is initial, then there must also exist a q that is initial
#  and satisfies the above conditions.
#
sub FindLabelPairs {
  my $self = shift;

  my $states = $self->{states};
  my $init = $self->{init};
  my $fair = $self->{fair};
  my $delta = $self->{delta};
  my $labels = $self->{labels};
  my $names = $self->{names};
  my $dontcares = $self->{dontcares};
  my $inverse = InvertDelta($states,$delta);

  my $pairs = Set->new;

  my $simul = $self->DirectSimulation;

  # Attach direct simulation results to automaton
  $self->{direct_simulation} = $simul;


 FIRST: foreach my $p (values %{$states}) {

    # find predecessors of p (excluding p itself)
    my $pred_p = $inverse->{$p}->Difference(Set->new($p));

    # keep track of predecessors which meet criteria
    my $good_pred = Set->new;
    my $possible;

  PRED: foreach my $pred (values %{$pred_p}) {
      $possible = Set->new;

    SUCC: foreach my $q (values %{$delta->{$pred}}) {
	next SUCC if ($q eq $p);

	#print " Now considering successor $names->{$q} of state $names->{$pred}...\n";

	# for each fairset F: if p is in F, then q must be in F
	unless (exists $dontcares->{$p}) {
	  foreach my $fairset (values %{$fair}) {
	    next SUCC if ($fairset->IsMember($p) and
			  !$fairset->IsMember($q) and
			  !(exists $dontcares->{$q}));
	  }
	}

	#print "  Made it here with $names->{$q} of state $names->{$pred}...\n";

	# for each successor t of p, there must exist a successor u of
	# q that direct-simulates t
	$succ_q = $delta->{$q};

	foreach my $t (values %{$delta->{$p}}) {
	  my @test = grep {($_->First eq $t) and 
			     ($succ_q->IsMember($_->Second))
			   } (values %{$simul});
	  next SUCC unless (scalar @test > 0);
	}

	# if we make it this far then (p,q) is a potential pair
	$possible->Push(Pair->new($p,$q));
	$good_pred->Push($pred);

      } # end SUCC

    } # end PRED

    # if p is initial, then there must exist a q that is initial
    if ($init->IsMember($p)) {
      my @test = grep { $init->IsMember($_->Second()) } (values %{$possible});
      next FIRST unless (scalar @test > 0);
    }

    # all predecessors must have alternative accepting routes
    if ($pred_p->IsEqual($good_pred)) {
      $pairs = $pairs->Union($possible);
    }
  } # end FIRST

  # print "Extended Theorem pairs:\n";
  # map { print "(" . $names->{$_->First} . "," .
  # 	  $names->{$_->Second} . ")\n" } (values %{$pairs});

  # Add potential label pairs to automaton
  $self->{label_pairs} = $pairs;

  return $pairs;

} # FindLabelPairs


######################################################################
# Build (direct) simulation relation and return it
# Body of code is from DirectSimulationMinimization()
# in Buechi.pm with minimal alterations.
#
sub DirectSimulation {
  my $self = shift;
  my $states = $self->{states};
  my $init = $self->{init};
  my $fair = $self->{fair};
  my $delta = $self->{delta};
  my $labels = $self->{labels};
  my $names = $self->{names};
  my $dontcares = $self->{dontcares};
  my $inverse = InvertDelta($states,$delta);

  # Initialize the direct simulation relation to all pairs (p,q)
  # that satisfy:
  # 0. p != q
  # 1. label(p) contains label(q) (hence, implies)
  # 3. for each f in F, p in f -> q in f
  # Also, push all pairs in the simulation relation onto a queue.
  # In the following code, p is $state, and q is $otherstate.
  my $simul = Set->new;
  my @queue = ();
  my %enqueued = ();
 FIRST: foreach my $state (values %{$states}) {
  SECOND: foreach my $otherstate (values %{$states}) {
      # here, we are interested in the fact that a state simulates itself 
      #next SECOND if $state eq $otherstate;

      next SECOND
	unless $$labels{$otherstate}->IsIncluded($$labels{$state});

      #print "made it here!\n";

      unless (exists $$dontcares{$state} ||
	      exists $$dontcares{$otherstate}) {
	foreach my $fairset (values %{$fair}) {
	  #print "  $names->{$state} " . $fairset->IsMember($state) . "\n";
	  #print "  $names->{$otherstate} " . $fairset->IsMember($otherstate) . "\n";
	  if ($fairset->IsMember($state)) {
	    next SECOND unless $fairset->IsMember($otherstate);
	  }
	}
      }

      my $pair = Pair->new($state,$otherstate);
      $simul->Push($pair);
      push(@queue, $pair);
      $enqueued{$pair} = 1;
    }
  }

  # Compute the greatest fixpoint.
 PAIRS: while (@queue > 0) {
    my $pair = pop(@queue);
    delete $enqueued{$pair};
    my $p = $pair->First;
    my $q = $pair->Second;
    	#print "Pair: $$names{$p} simulated by $$names{$q}";
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
      	 #   print " removed\n";
      next PAIRS;
    }
    	#print " retained\n";
  }

  return $simul;

} # DirectSimulation


#########################
#       Utilities       #
#########################

# Convert an ASCII string representing a binary number to a true decimal number
sub bin2dec {
  return unpack("N", pack("B32", substr("0" x 32 . shift, -32)));
}

# Convert a true number to a binary ASCII string (32-bits only)
sub dec2bin {
  my $str = unpack("B32", pack("N", shift));
  return $str;
}

# Covert an ASCII string representing a hex number to a binary ASCII string (32-bits)
sub hex2bin {
  return unpack("B32", pack("N", hex(shift)));
}

# Convert an ASCII string representing a binary number to a hex ASCII string
sub bin2hex {

    my $Bin = shift(@_);
    my $Hex;

    # Clean up string and look for errors
    chomp $Bin;

    if ($Bin =~ m/[^10]/) {
        print STDERR "ERROR: $Bin is not binary\n";
        return ("");
    }
    return scalar reverse unpack "h*",(pack "b*", scalar reverse $Bin);
} # bin2hex


# Required
1;
