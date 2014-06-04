# $Id: AAemptiness.pm,v 1.2 2005/09/26 11:44:23 bjobst Exp $

######################################################################
# Functions to test language emptiness of an alternating automaton.
#
# Author: Fabio Somenzi <Fabio@Colorado.EDU>
#
######################################################################

package Alternating;

use strict;

######################################################################
# Returns 1 if the language of the co-Buechi automaton is empty;
# "" otherwise.
# Buechi and co-Buechi automata are represented identically.  The
# difference is in the interpretation of the acceptance condition.
# This function assumes that an infinite path of an accepting run
# visits a "fair" state only finitely many times.
######################################################################
sub CoBuechiIsEmpty {
    my $self = shift;
    my %params = @_;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $names = $$self{names};

    print "*** Entering CoBuechiIsEmpty ***\n"; # dia
    # Support for inconsistent subset detection.  If the "maxindex"
    # parameter is defined, then states are assumed to be pairs whose
    # second component is a nonnegative integer.  The parameter is the
    # maximum value this index may take.  Consistent configurations do not
    # contain two states that differ only in the index, unless the index
    # equals maxindex.
    my $maxindex = defined $params{maxindex} ? $params{maxindex} : undef;
    # Associate an integer index to each state for hashing.
    my $index = 0;
    my %map = ();
    foreach my $state (values %$states) {
	# print "Map(", $$names{$state}, ") = $index\n"; #dia
	$map{$state} = $index++;
    }

    # $self->Letters($states); #dia
    # A configuration is a set of states that may occur at the same level
    # of a run of the co-Buechi automaton.
    my $config = Set->new($init);
    print "Initial: ", $self->StateRelationToNameString($config), "\n"; # dia
    # A partial run is a DAG consisting of a set of configurations and the
    # arcs connecting them.
    my @stack = ();
    my %active = ();
    my %dfnumber = ();
    my %lowlink = ();
    my $count = 0;
    my %cyclestart = ();
    return enumSCCs($self,$init,\@stack,\%active,\%dfnumber,\%lowlink,
		    \$count,\%cyclestart,\%map,$maxindex);

} # CoBuechiIsEmpty


######################################################################
# Perform DFS to find SCCs of configuration graph.  Mark the configurations
# that are the targets of back arcs.  For each DFS, enumerate cycles
# starting from all marked states.
######################################################################
sub enumSCCs {
    my ($self,$conf,$stack,$active,$dfnumber,$lowlink,$countr,
	$cyclestart,$map,$max) = @_;
    print "Conf: ", $self->StateRelationToNameString($conf), "\n"; # dia
    # Assign the DFS (preorder) number and initialize the "low link,"
    # which eventually will indicate the lowest DFS number among those
    # of the nodes reachable from this node.  Push the node on the
    # stack.  When we enumerate the simple cycles of an SCC, "active"
    # prevents us from following transitions out of the SCC.
    my $hashval = hashConf($conf,$map);
    $$lowlink{$hashval} = $$dfnumber{$hashval} = $$countr++;
    $$active{$hashval} = scalar @$stack;
    push(@$stack,$conf);
    # Examine all successors.
    my $delta = $$self{delta};
    my $letters = $self->Letters($conf);
    foreach my $letter (values %$letters) {
	my $successors = $self->successorConfigurations($conf,$letter,$max);
	my @sorted = sort {$a->First->Size <=> $b->First->Size}
	  values %$successors;
	foreach my $pair (@sorted) {
	    my $newconf = $pair->First;
	    my $newHV = hashConf($newconf,$map);
	    unless (exists $$dfnumber{$newHV}) {
		my $retval = enumSCCs($self,$newconf,$stack,$active,$dfnumber,
				      $lowlink,$countr,$cyclestart,$map,$max);
		return "" if $retval eq "";
		$$lowlink{$hashval} = $$lowlink{$newHV}
		  if $$lowlink{$newHV} < $$lowlink{$hashval};
	    } elsif ($$dfnumber{$newHV} <= $$dfnumber{$hashval} and
		     exists $$active{$newHV}) {
		# We have found a back arc.
		$$cyclestart{$newHV} = $$active{$newHV};
		$$lowlink{$hashval} = $$dfnumber{$newHV}
		  if $$dfnumber{$newHV} < $$lowlink{$hashval};
	    }
	}
    }
    # Analyze SCC if we found its entry point.
    if ($$dfnumber{$hashval} == $$lowlink{$hashval}) {
	print "SCC entry point: ",
	      $self->StateRelationToNameString($conf), "\n"; # dia
	# Scan SCC for cycle starting configurations.
	for (my $i=$$active{$hashval}; $i<@$stack; $i++) {
	    my $startconf = $$stack[$i];
	    if (exists $$cyclestart{hashConf($startconf,$map)}) {
		my %blocked = ();
		my %back = ();
		my @runNodes = ();
		my @runArcs = ();
		my %onstack = ();
		print "Enumerating cycles from ",
		  $self->StateRelationToNameString($startconf), "\n"; # dia
		my @retval = circuit($self,$startconf,$startconf,$active,
				     \%blocked,\%back,\@runNodes,\@runArcs,
				     \%onstack,$map);
		return "" unless $retval[1];
	    }
	}
	# Remove this SCC from the stack.
	my $x;
	do {
	    $x = pop(@{$stack});
	    delete $$active{hashConf($x,$map)};
	} while ($x ne $conf);
    }
    return 1;

} # enumSCCs


######################################################################
# Enumeration of simple cycles from a starting configuration using
# Johnson's algorithm (SIAM J. Comput. 1975).
# The return value is a pair.  The first element says whether a cycle
# was found.  The second says whether an _accepting_ cycle was found.
# Execution terminates as soon as an accepting cycle is found.  No
# clean up is performed at that point.
######################################################################
sub circuit {
    my ($self,$conf,$startconf,$active,$blocked,$back,$nodes,$arcs,
	$onstack,$map) = @_;
    my $found = "";
    # Mark configuration as visited.
    my $hashval = hashConf($conf,$map);
    $$blocked{$hashval} = 1;
    # Push configuration on DFS stack.
    $$onstack{$hashval} = scalar @$nodes; # record position on stack
    push(@$nodes,$conf);
    # Enumerate all possible (minimal) sets of successors.
    my $delta = $$self{delta};
    my $letters = $self->Letters($conf);
    my $hashstart = hashConf($startconf,$map);
    foreach my $letter (values %$letters) {
	my $successors = $self->successorConfigurations($conf,$letter,undef);
	my @sorted = sort {$a->First->Size <=> $b->First->Size}
	  values %$successors;
	foreach my $pair (@sorted) {
	    my $newconf = $pair->First;
	    my $newlayer = $pair->Second;
	    my $hashnew = hashConf($newconf,$map);
	    # Make sure successor is in the same SCC, and that it follows
	    # the cycle starting point in DFS order.  (The latter is to
	    # avoid repeating the same cycle from different starting points.)
	    next unless exists $$active{$hashnew} and
	      $$active{$hashnew} >= $$active{$hashstart};
	    if ($newconf->IsEqual($startconf)) {
		# print "Found cycle\n"; # dia
		$found = 1;
		push(@$arcs,$newlayer);
		my $stackposn = $$onstack{hashConf($newconf,$map)};
		return (1,"") unless analyzeRun($self,$nodes,$arcs,$stackposn);
		pop(@$arcs);
	    } elsif (not exists $$blocked{hashConf($newconf,$map)}) {
		push(@$arcs,$newlayer);
		my @retval = circuit($self,$newconf,$startconf,$active,
				     $blocked,$back,$nodes,$arcs,$onstack,
				     $map);
		return (1,"") unless $retval[1];
		$found = 1 if $retval[0];
		pop(@$arcs);
	    }
	}
    }
    if ($found) {
	unblock($hashval,$blocked,$back);
    } else {
	# Keep track of which configurations will cause this one to be
	# unblocked when they are unblocked.
	foreach my $letter (values %$letters) {
	    my $successors = $self->successorConfigurations($conf,$letter,
							    undef);
	    foreach my $pair (values %$successors) {
		my $otherconf = $pair->First;
		my $hashother = hashConf($otherconf,$map);
		# Make sure successor is in the same SCC, and that it
		# follows the cycle starting point in DFS order.
		next unless exists $$active{$hashother} and
		  $$active{$hashother} >= $$active{$hashstart};
		my $otherHV = hashConf($otherconf,$map);
		my $bconf = $$back{$otherHV};
		$$bconf{$hashval} = 1;
	    }
	}
    }
    # Remove configuration from stack.
    pop(@$nodes);
    delete $$onstack{$hashval};
    return ($found,1);

} # circuit


######################################################################
# DFS to unblock a node during the search for simple cycles.
######################################################################
sub unblock {
    my ($hashval,$blocked,$back) = @_;
    delete $$blocked{$hashval};
    my $bconf = $$back{$hashval};
    foreach my $w (values %$bconf) {
	if ($$blocked{$w}) {
	    unblock($w,$blocked,$back);
	}
    }
    $$back{$hashval} = ();

} # unblock


######################################################################
# Return a set of successor configurations of one configuration for a
# given alphabet letter.
######################################################################
sub successorConfigurations {
    my ($self,$conf,$letter,$max) = @_;
    my $delta = $$self{delta};
    # my $fair = $$self{fair};
    my @states = values %$conf;
    my @transitions = ();
    my @sizes = ();
    my $totalsize = 1;
    # Collect and count enabled transitions out of each state in the
    # configuration.  The enabled transitions are stored in a list of lists:
    # one list for each state of the configuration.
    foreach my $state (@states) {
	my $succ = $$delta{$state};
	my @enabled = ();
	foreach my $t (values %$succ) {
	    my $label = $t->First;
	    my $dest = $t->Second;
	    if ($label->IsIncluded($letter)) { # transition is enabled
		foreach my $d (values %$dest) {
		    push(@enabled,$d);
		}
	    }
	}
	my $size = @enabled;
	$totalsize *= $size;
	push(@sizes, $size);
	push(@transitions,\@enabled);
    }
    # Find configurations reachable in one step.
    # my $fairset = $fair->Pick;	# there is only one fair set
    my $successors = Set->new;
    my @indices = map 0, @sizes;
  OLOOP: for (my $i=0; $i < $totalsize; $i++) {
	my $flip = 1;
	my $newconf = Set->new;
	my %arcs = ();
	for (my $j=0; $j < $conf->Size; $j++) {
	    my $destination = $transitions[$j][$indices[$j]];
	    $newconf->Add($destination);
	    $arcs{$states[$j]} = $destination;
	    if ($flip) {
		$indices[$j]++;
		if ($indices[$j] == $sizes[$j]) {
		    $indices[$j] = 0;
		} else {
		    $flip = 0;
		}
	    }
	}
	if (defined $max) {
	    # Consistency check
	    my $sstate = undef;
	    foreach my $nstate (values %$newconf) {
		my $index = $nstate->Second;
		unless ($index == $max) {
		    my $cstate = $nstate->First;
		    if (defined $sstate) {
			next OLOOP unless $sstate->IsEqual($cstate);
		    } else {
			$sstate = $cstate;
		    }
		}
	    }
	}
	# The code below is commented out because the "optimization" is
	# incorrect.  It is left here in case we discover something correct
	# along these lines.

#	# Here we make sure that no new configuration is a superset of another,
#	# unless the other configuration contains a fair state.
#	# print "Examining configuration for ", $letter->ToString, ": ",
#	#   $self->StateRelationToNameString($newconf),
#	#     $newconf->IsDisjoint($fairset) ? " (disjoint)" : "", "\n"; # dia
#	my $found = 0;
# 	my $delenda = Set->new;
# 	foreach my $pair (values %$successors) {
# 	    my $already = $pair->First;	# the configuration
# 	    if ($already->IsDisjoint($fairset) and
# 		$already->IsIncluded($newconf)) {
# 		$found = 1;
# 		# print "found: ", $self->StateRelationToNameString($newconf),
# 		#   " ", $self->StateRelationToNameString($already),
# 		#     "\n"; # dia
# 		last;
# 	    } elsif ($newconf->IsIncluded($already) and
# 		    $newconf->IsDisjoint($fairset)) {
# 		$delenda->Push($pair);
# 		# print "delete: ", $self->StateRelationToNameString($newconf),
# 		#   " ", $self->StateRelationToNameString($already),
# 		#     "\n"; # dia
# 	    }
# 	}
#	next if $found;
#	$successors->Subtract($delenda);
	$successors->Push(Pair->new($newconf,\%arcs));
	# print "New configuration for ", $letter->ToString, ": ",
	#   $self->StateRelationToNameString($newconf), "\n"; #dia
    }

#     if ($successors->Size) { #dia
# 	print "Successors of ", $self->StateRelationToNameString($conf);
# 	print " for ", $letter->ToString, ": {";
# 	my $separ = "";
# 	foreach my $pair (values %$successors) {
# 	    print $separ, $self->StateRelationToNameString($pair->First);
# 	    $separ = ",";
# 	}
# 	print "}\n";
#     }
    return $successors;

} # successorConfigurations


######################################################################
# Analyze a partial run to decide acceptance.  Return "" if the
# partial run is accepting (language not empty); 1 otherwise.
######################################################################
sub analyzeRun {
    my ($self,$nodes,$arcs,$stackposn) = @_;
    my $names = $$self{names};
    my $fair = $$self{fair};
    my $fairset = $fair->Pick;	# there is only one fair set
    # dia
    print "===== stack dump =====\n";
    for (my $i=0; $i < @$nodes; $i++) {
	my $conf = $$nodes[$i];
	foreach my $state (values %$conf) {
	    my $dest = $$arcs[$i]{$state};
	    print $$names{$state}, " -> ";
	    print $self->StateRelationToNameString($dest), " ";
	}
	print $i == $stackposn ? " <-" : "", "\n";
    }
    print "=====  end dump  =====\n";
    my $bstates = Set->new;
    my %bdelta = ();
    my $binit = Set->new;
    my $bfair = Set->new;
    for (my $i=$stackposn; $i < @$nodes; $i++) {
	my $conf = $$nodes[$i];
	foreach my $state (values %$conf) {
	    my $bstate = Pair->new($state,$i);
	    unless ($bstates->IsMember($bstate)) {
		$bstates->Push($bstate);
		$bdelta{$bstate} = Set->new;
		$binit->Push($bstate) if $i == $stackposn;
		$bfair->Push($bstate) if $fairset->IsMember($state);
	    }
	    my $dest = $$arcs[$i]{$state};
	    my $nexti = $i == @$nodes - 1 ? $stackposn : $i + 1;
	    foreach my $dstate (values %$dest) {
		$bdelta{$bstate}->Push(Pair->new($dstate,$nexti));
	    }
	}
    }
    # If the set of states of the Buechi automaton is empty, we accept
    # beacuse all paths end in "true."
    if ($bstates->Size == 0) {
	print ">>> found accepting run <<<\n"; # dia
	return "";
    }
    my $buechi = Buechi->new(
			     states => $bstates,
			     init   => $binit,
			     delta  => \%bdelta,
			     fair   => Set->new($bfair)
			    );
    # print $buechi->ToString; # dia
    # The run segment is accepting if the language of this Buechi automaton
    # is empty.  If we were to check this efficiently, we would implement the
    # double DFS procedure.  For now, we limit ourselves to calling the
    # existing implementation of Tarjan's algorithm to find all SCCs.  Then,
    # we build the complete quotient graph.  It's wasteful, but only takes a
    # few lines of code.
#     my $quotient = $buechi->Quotient($buechi->SCC);
#     # print $quotient->ToString; # dia
#     my $qfair = $$quotient{fair};
#     if ($qfair->Size == 1) {
# 	my $qfairset = $qfair->Pick;
# 	if ($qfairset->Size == 0) {
# 	    print ">>> found accepting run <<<\n"; # dia
# 	    return "";
# 	}
#     }
    if ($buechi->IsEmpty) {
	print ">>> found accepting run <<<\n"; # dia
	return "";
    }
    return 1;

} # analyzeRun


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
    my $vars = LabelToStringSet($atoms);
    # print "Inputs: ", $vars->ToString, "\n"; # dia
    return $vars;

} # ExtractInputs


######################################################################
# Return a unique signature string for a set of states.
######################################################################
sub hashConf {
    my ($states,$map) = @_;
    my @states = map $$map{$_}, values %$states;
    my $string = join('.', sort {$a <=> $b} @states);
    return $string;

} # hashConf

# Required return value.
1;
