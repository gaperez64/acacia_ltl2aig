# $Id: Decomp.pm,v 1.2 2005/09/26 11:44:23 bjobst Exp $

######################################################################
# Functions to disjunctively decompose Buechi automata.
#
# Author: Chao Wang <Wangc@Colorado.EDU>
#
######################################################################
package Buechi;

use strict;


#######################################################################
# Disjunctive Decomposition of Buechi automaton:
#     (1) Generating one sub-automaton for each "Fair SCC"
#
# For example:
#             my $aut = Buechi->New(...);
#             my $sub_auts = $aut->DDecByFairscc;
#######################################################################
sub DDecByFairscc {

    # Original Buechi Automaton
    my $self = shift;
    my $states=$$self{states};
    my $init  =$$self{init};
    my $delta =$$self{delta};
    my $names =$$self{names};
    my $labels=$$self{labels};
    my $fair  =$$self{fair};

    # SCC quotient grpah
    my $quotient= $self->Quotient($self->SCC);

    my $Qstates =$$quotient{states};
    my $Qinit   =$$quotient{init};
    my $Qdelta  =$$quotient{delta};
    my $Qnames  =$$quotient{names};
    my $Qlabels =$$quotient{labels};
    my $Qfair   =$$quotient{fair};
    # Create a generic set to store "sub-automata to be generated"
    my $SubAuto = Set->new;

    # There is only 1 Qfairset in Qfair (of SCC quotient graph)
    # Each element of this Qfairset is a "fair SCC"
    foreach my $Qfairset (values %{$Qfair}) {
	foreach my $Qfair_scc (values %{$Qfairset}) {

	    # Build a sub-aut for this specific "Qfair_scc"
	    my $Sstates =$states->Clone;
	    my $Sinit   =$init->Clone;

	    # Generate new "fair"
	    my $Sfair = Set->new;
	    foreach my $fairset (values %{$fair}) {
		my $tempfairset = $fairset->Clone;
		foreach my $fair_st (values %{$fairset}) {
		    if (!$Qfair_scc->IsMember($fair_st)) {
			$tempfairset->Delete($fair_st);
		    }
		}
		$Sfair->Push($tempfairset);
	    }

	    # Generate new "delta","labels","names"
	    my %Sdelta =();
	    my %Slabels=();
	    my %Snames =();
	    foreach my $st (values %{$Sstates}) {
		$Sdelta{$st}= $$delta{$st}->Clone;
		$Slabels{$st}=$$labels{$st}->Clone;
		$Snames{$st} =$$names{$st};

		$Sdelta{$st}=Set->new unless defined($Sdelta{$st});
		$Slabels{$st}=Set->new unless defined($Slabels{$st});
		$Snames{$st}=newName("m") unless defined($Snames{$st});
	    }

	    # Assemble the sub-aut
	    my $subaut = Buechi->new(
				     states => $Sstates,
				     init   => $Sinit,
				     delta  => \%Sdelta,
				     names  => \%Snames,
				     labels => \%Slabels,
				     fair   => $Sfair
				     );

	    $subaut->Prune;

	    # Insert it into the generic Set
	    $SubAuto->Push($subaut);
	}
    }

  return $SubAuto;

} # DDecByFairscc


#######################################################################
# Disjunctive Decomposition of Buechi automaton:
# (2)  Generating one sub-automaton for each "Possible run"
#
# For example:
#             my $aut = Buechi->New(...);
#             my $sub_auts = $aut->DDecByRunscc;
#######################################################################
sub DDecByRunscc {

    # Original Buechi Automaton
    my $self = shift;
    my $states=$$self{states};
    my $init  =$$self{init};
    my $delta =$$self{delta};
    my $names =$$self{names};
    my $labels=$$self{labels};
    my $fair  =$$self{fair};

    # SCC quotient grpah
    my $quotient= $self->Quotient($self->SCC);

    my $Qstates =$$quotient{states};
    my $Qinit   =$$quotient{init};
    my $Qdelta  =$$quotient{delta};
    my $Qnames  =$$quotient{names};
    my $Qlabels =$$quotient{labels};
    my $Qfair   =$$quotient{fair};

    # Create the Set "Number of Runs at each scc node"
    my $NumOfRun= $quotient->NumberOfRuns;

    # Create the set "color at each scc node"
    my $color = Set->new;
    foreach my $st (values %{$Qstates}) {
	$$color{$st} = 0;
    }

    # Recursive call to FindRuns, return a generic Set "sub-quotients"
    my $SubQuot = Set->new;
    my $runstack= Set->new;
    foreach my $Qfairset (values %{$Qfair}) {
	foreach my $Qfair_scc(values %{$Qfairset}) {
	    #There should be only 1 such $Qfair_scc
            $quotient->FindRuns($Qfair_scc, $NumOfRun, $color, $runstack, $SubQuot);
	}
    }

    # Create a generic Set to store " to be generated"
    my $SubAuto = Set->new;

    # Merge Runs, if they contain the same states
    my $MergeQuot2 = $SubQuot->Clone;
    my $MergeQuot  = $SubQuot->Clone;
    foreach my $Aquot (values %{$MergeQuot2}) {
	foreach my $Bquot (values %{$SubQuot}) {
	    # If one run is included in another, delete it
	    if ($Aquot->IsIncluded($Bquot) ) {
		if (!($Bquot->IsIncluded($Aquot))) {
		    $MergeQuot->Delete($Aquot);
		}
	    }
	}
    }

    # Generate sub-auto from the original Buechi automaton, by
    # using sub-quotient graphs as constraints.
    foreach my $subqg (values %{$MergeQuot}) {
	my $subauto = $self->Confine($subqg);
	$SubAuto->Push($subauto);
    }

    return $SubAuto;

} # DDecByRunscc


############################################################################
# Generate a new Beuchi automaton from $self(original automaton),
# Only retain those states in the Set of sccs
#
# for example:
#             my $aut= BUECHI->new;
#             my $quot       is a Set of SCC;
#             my $newaut=$aut->Confine($quot);
############################################################################
sub Confine {
    my $self = shift;
    my $states=$$self{states};
    my $init  =$$self{init};
    my $delta =$$self{delta};
    my $names =$$self{names};
    my $labels=$$self{labels};
    my $fair  =$$self{fair};

    my ($Qstates)= @_;

    # Generate new "states", by discarding those states not in qg
    my $newStates =$states->Clone;
    my $notstates =$states->Clone;
    foreach my $qscc (values %{$Qstates}) {
	$notstates->Subtract($qscc);
    }
    $newStates->Subtract($notstates);

    # Generate new "init"
    my $newInit =$init->Clone;
    $newInit->Subtract($notstates);

    # Generate new "fair"
    my $newFair = Set->new;
    foreach my $fairset (values %{$fair}) {
	$newFair->Push($fairset->Clone);
    }

    # Generate new "delta","labels","names"
    my %newDelta=();
    my %newLabels=();
    my %newNames=();
    foreach my $st (values %{$newStates}) {
	$newDelta{$st}=	$$delta{$st}->Clone;
	$newDelta{$st}->Subtract($notstates);
	$newLabels{$st}=$$labels{$st}->Clone;
	$newNames{$st} =$$names{$st};

	$newDelta{$st}=Set->new unless defined($newDelta{$st});
	$newLabels{$st}=Set->new unless defined($newLabels{$st});
	$newNames{$st}=newName("m") unless defined($newNames{$st});
    }

    my $newauto = Buechi->new(
			      states => $newStates,
			      init   => $newInit,
			      delta  => \%newDelta,
			      names  => \%newNames,
			      labels => \%newLabels,
			      fair   => $newFair
			      );
    return $newauto;

} # Confine


#############################################################################
# Enumerate the Number of different Runs in the DAG
#  Return a hashtable {eachnode}{numOfRun}
#  for example:
#              my $NumOfRun = quotient_graph->NumberOfRuns;
#############################################################################
sub NumberOfRuns {

    # Scc quotient graph
    my $self = shift;
    my $states=$$self{states};
    my $init  =$$self{init};
    my $fair  =$$self{fair};
    my $delta =$$self{delta};
    my $invdelta=InvertDelta($states,$delta);

    # The hash table{sccnode}{numOfRun}
    my %numofrun = ();

    # The topological sequence, leftmost is the first
    my $tseq = $self->TopoSort;

    # Initialize NumberOfRuns at each node
    foreach my $mstate (values %{$states}) {
	$numofrun{$mstate}=0;
    }
    foreach my $myfairset (values %{$fair}) {
	foreach my $fstate (values %{$myfairset}) {
	    $numofrun{$fstate}=1;
        }
    }

    # Calculate NumOfRun at each node, by adding the NumOfRun of all the
    # fan-outs
    while (my $mpstate = pop(@{$tseq}) ) {

        my $preimage = $$invdelta{$mpstate};
        foreach my $nstate (values %{$preimage}) {

	    if ($nstate != $mpstate) {
		$numofrun{$nstate} = $numofrun{$nstate} + $numofrun{$mpstate};
	    }
        }
    }

    return (\%numofrun);

} # NumberOfRuns


#######################################################################
# Find the number of runs at each node within SCC quotient graph
# !!! the SCC quotient graph should have only 1 fair SCC
#
# For example:
#             my $aut = Buechi->New(...);
#             my $sub_auts = $aut->FindRuns($cur-node,$NumOfRun,$color);
#######################################################################
sub FindRuns {

    # SCC quotient graph, on which to find runs
    my $sccqg = shift;
    my $Qstates=$$sccqg{states};
    my $Qinit  =$$sccqg{init};
    my $Qnames =$$sccqg{names};
    my $Qlabels=$$sccqg{labels};
    my $Qdelta =$$sccqg{delta};
    my $Qinvdelta =InvertDelta($Qstates,$Qdelta);
    my $Qfair  =$$sccqg{fair};

    # Parameters (current node, color,runstack,subquot)
    my ($qg_st, $NoR, $color, $runstack, $subquot) = @_;

    # Mark current qg_st, as visited
    $$color{$qg_st} = 1;

    # Runstack hold set of states from fairscc to cur-node
    $runstack->Push($qg_st);

    # Run FindRuns on each fan-ins of current qg_st
    my $preimage = $$Qinvdelta{$qg_st};
    foreach my $v (values %{$preimage}) {
	if ($$color{$v}==0) {
	    $sccqg->FindRuns ($v,$NoR,$color,$runstack,$subquot);
	}
    }

    # If qg_st is initial state, find a run!
    # push this "run"(set of states) into $subquot
    if ($Qinit->IsMember($qg_st)) {
        $subquot->Push($runstack->Clone);
    }

    # The number of run at cur-node dec 1
    $$NoR{$qg_st} =$$NoR{$qg_st} -1;

    # If still have runs at cur-node, white its color to enable further search
    if ($$NoR{$qg_st}!=0) {
	$$color{$qg_st} = 0;
    }

    # Pop cur-node before backtracking
    $runstack->Delete($qg_st);

} # FindRuns


##################################################################
# Topological Sorting of the SCC quotient graph, or acyclic auto
#    A variation of standard Depth-First-Search
#
#    for example:
#                my $sccq=$Buechi->Quotien($Buechi->SCC);
#                my $topoS=sccq->TopoSort;
#
# Return: Set of nodes with the first item leftmost
##################################################################
sub TopoSort {
    my $self = shift;
    my $init = $$self{init};
    my $states=$$self{states};
    my %color=();
     my @tsequence = ();

    # Initize color, du, and fu
    foreach my $state (values %{$states}) {
	$color{$state} = 0;
    }


    foreach my $initial (values %{$init}) {
	if ($color{$initial}==0) {
	    $self->Topo_visit($initial,\%color,\@tsequence);
	}
    }

    return (\@tsequence);

} # TopoSort


##################################################################
# Used inside TopoSort
##################################################################
sub Topo_visit {
    my $self = shift;
    my ($state,$color,$tsequence) = @_;
    my $delta = $$self{delta};

    # Mark this node as "visited"
    $$color{$state} = 1;

    # Depth first tranverse its fan-outs
    foreach my $state2 (values %{$$delta{$state}}) {
	if ($$color{$state2} == 0) {
	    $self->Topo_visit($state2,$color,$tsequence );
	}
    }

    # Put cur-node at the head of the sequence
    unshift(@{$tsequence}, $state);

} # Topo_visit

# Required return value.
1;
