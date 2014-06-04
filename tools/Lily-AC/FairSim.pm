# $Id: FairSim.pm,v 1.2 2005/09/26 11:44:23 bjobst Exp $

######################################################################
# Functions to simplify Buechi automata by fair simulation minimization.
#
# Authors: Fabio Somenzi <Fabio@Colorado.EDU>
#          Sankar Gurumurthy <gurumurt@colorado.edu>
#
######################################################################
package Buechi;

use Game;
use strict;

use vars qw($DEBUG);
$DEBUG = 1;


######################################################################
# Apply fair simulation minimization to an automaton.
######################################################################
sub FairSimulationMinimization {
    my $self = shift;

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
    my ($game,$Wa) = $self->BuildGameAutomaton($safety);
    my $gstates = $$game{states};
    if ($DEBUG > 0) {
	print "Game automaton\n", $game->ToString, "End game automaton\n";
	print "Wa: ", $game->StateRelationToNameString($Wa), "\n";
	if ($DEBUG > 2) {
	    print $game->ToDot("game automaton");
	    my $Wp = $gstates->Difference($Wa);
	    print "Wp: ", $game->StateRelationToNameString($Wp), "\n";
	}
    }
    my $gdelta = $$game{delta};
    my $ginverse = InvertDelta($gstates,$gdelta);
    my $winningstatesstreett = $game->StreettGame($ginverse,$Wa);
    print "Winning states through the Streett game approach: ",
      $game->StateRelationToNameString($winningstatesstreett), "\n"
	if $DEBUG > 1;
    my $winningstatesparity = $game->lift($ginverse);
    print "Winning states through the parity game approach: ",
      $game->StateRelationToNameString($winningstatesparity), "\n"
	if $DEBUG > 1;
    unless ($winningstatesstreett->IsEqual($winningstatesparity)) {
	print "The winning states through the two approaches differ\n",
	  "Winning states through the Streett game approach: ",
	    $game->StateRelationToNameString($winningstatesstreett), "\n",
	      "Winning states through the parity game approach: ",
		$game->StateRelationToNameString($winningstatesparity), "\n";
    }
    my $fairsim = Set->new;
    foreach my $winnings (values %{$winningstatesparity}) {
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
    my $closure = $self->TransitiveClosure;
    # Find fair-simulation equivalent states.
    foreach my $pair (values %{$fairsim}) {
	next unless $fairsim->IsMember($pair);
	my ($p,$q) = ($pair->First,$pair->Second);
	# Make sure neither state has been removed yet.
	next unless $states->IsMember($p) and $states->IsMember($q);
	my $qclosure = $$closure{$q};
	next if $qclosure->IsMember($p);
	my $swapped = Pair->new($q,$p);
	next unless $fairsim->IsMember($swapped);
	# Theorem applies.
	# $fairsim->Delete($swapped);
	# Throw away p and connect its predecessors to q.
	if ($DEBUG > 2) {
	    print "$$names{$p} is direct-fair-simulation" .
	      " equivalent to $$names{$q}\n";
	}
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
	    if ($fairset->IsMember($p)) {
		$fairset->Delete($p);
	    }
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
    # Remove arcs to fair-simulated states.
    foreach my $pair (values %{$fairsim}) {
	my ($p,$q) = ($pair->First,$pair->Second);
	# Make sure neither state has been removed because of
	# simulation equivalence.
	next unless $states->IsMember($p) and $states->IsMember($q);
	if ($DEBUG > 2) {
	    print "Dropping arcs of common parents ";
	    print "of $$names{$p} and $$names{$q}\n";
	}
	my $qclosure = $$closure{$q};
	foreach my $s (values %{$$inverse{$p}}) {
	    next unless $$delta{$s}->IsMember($q);
	    next if $qclosure->IsMember($s);
	    # Theorem applies.  Drop arcs to p from parents of both p and q.
	    if ($DEBUG > 2) {
		print "Dropping arc from $$names{$s} to $$names{$p}\n";
	    }
	    $$delta{$s}->Delete($p);
	    $$inverse{$p}->Delete($s);
	}
	# Remove state p from initial states if q is initial.
	$init->Delete($p) if $init->IsMember($q);
    }
    if ($DEBUG > 0) {
	print $self->ToString;
    }

} # FairSimulationMinimization


######################################################################
# Build the game automaton for fair simulation minimization.
######################################################################
sub BuildGameAutomaton {
    my ($self,$safety) = @_;
    my $sstates = $$self{states};
    my $sinit = $$self{init};
    my $sdelta = $$self{delta};
    my $slabels = $$self{labels};
    my $snames = $$self{names};
    my $sfair = $$self{fair};
    my %delta = ();
    my %labels = ();
    my %names = ();
    my %priority = ();
    my $oddcount = 0;
    # Build the set of initial states.  An initial state of the game
    # automaton is a state (a,(i,s)) such that (i,s) is in the safety
    # relation.  We have to keep in mind that the identity relation is
    # not explicitly stored in $safety.
    my $states = Set->new;
#     foreach my $first (values %{$sstates}) {
# 	foreach my $second (values %{$sstates}) {
# 	    my $pair = Pair->new($first,$second);
# 	    if ($first eq $second or $safety->IsMember($pair)) {
# 		my $state = Pair->new("a",$pair);
# 		$labels{$state} = $$slabels{$first}->Union($$slabels{$second});
# 		$names{$state} =
# 		  Pair->new("a",Pair->new($$snames{$first},$$snames{$second})
# 			   )->ToString;
# 		$states->Push($state);
# 	    }
# 	}
#     }

    foreach my $pair (values %{$safety},
		      map {Pair->new($_,$_)} values %{$sstates}) {
	my $state = Pair->new("a",$pair);
	my ($anti, $proto) = ($pair->First, $pair->Second);
	$labels{$state} = $$slabels{$anti}->Union($$slabels{$proto});
	$names{$state} =
	  Pair->new("a",Pair->new($$snames{$anti},$$snames{$proto}))->ToString;
	$states->Push($state);
	$priority{$state} = 2;
    }

    # Build the reachable part of the game automaton.
    my $unexpanded = $states->Clone;
    my $init = Set->new; # was $states->Clone;
    my $astates = $states->Clone;
    while ($unexpanded->Size > 0) {
	my $state = $unexpanded->Pop;
	my $flag = $state->First;
	my $pair = $state->Second;
	my $antagonist  = $pair->First;
	my $protagonist = $pair->Second;
	my $image;
	my $newflag;
	if ($flag eq "a") {
	    # Antagonist state.
	    my $simage = $$sdelta{$antagonist};
	    $image = Cartesian($simage,Set->new($protagonist));
	    $image = Cartesian(Set->new("p"),$image);
	    $newflag = "p";
	} else {
	    # Protagonist state.
	    my $simage = $$sdelta{$protagonist};
	    $image = Cartesian(Set->new($antagonist),$simage);
	    foreach my $ipair (values %{$image}) {
		my $ianti  = $ipair->First;
		my $iproto = $ipair->Second;
		unless (($ianti eq $iproto) or $safety->IsMember($ipair)) {
		    $image->Delete($ipair);
		}
	    }
	    $image = Cartesian(Set->new("a"),$image);
	    $newflag = "a";
	}
	my $new = $image->Difference($states);
	foreach my $newstate (values %{$new}) {
	    my $newpair = $newstate->Second;
	    my $newanti  = $newpair->First;
	    my $newproto = $newpair->Second;
	    my $label;
	    if ($newflag eq "a") {
		$label = $$slabels{$newanti}->Union($$slabels{$newproto});
	    } else {
		$label = Set->new;
	    }
	    $labels{$newstate} = $label;
	    $names{$newstate} =
	      Pair->new($newflag,
			Pair->new($$snames{$newanti},$$snames{$newproto})
		       )->ToString;
	}
	$delta{$state} = $image;
	$priority{$state} = 2;
	$unexpanded->Add($new);
	$states->Add($new);
	$astates->Add($new) if $newflag eq "a";
    }

    # Build antagonist and protagonist fair sets.
    my $fair = Set->new;
    foreach my $sfairset (values %{$sfair}) {
	my $afairset = Set->new;
	my $pfairset = Set->new;
	foreach my $state (values %{$states}) {
	    my $flag = $state->First;
	    my $pair = $state->Second;
	    my $anti = $pair->First;
	    if ($sfairset->IsMember($anti)) {
		$afairset->Push($state);
		$priority{$state} = 1 if $flag eq "a";
	    }
	    my $proto = $pair->Second;
	    if ($sfairset->IsMember($proto)) {
		$pfairset->Push($state);
		$priority{$state} = 0;
	    }
	}
	$fair->Push(Pair->new($afairset,$pfairset));
    }

    foreach my $state (values %{$states}) {
	if ($priority{$state} ==1) {
	    $oddcount++;
	}
    }
    my $game = Buechi->new(
			   states   => $states,
			   init     => $init,
			   priority => \%priority,
			   delta    => \%delta,
			   names    => \%names,
			   labels   => \%labels,
			   fair     => $fair,
			   oddcount => $oddcount
			  );
    return ($game,$astates);

} # BuildGameAutomaton


######################################################################
# Converts a parity game graph to dot format.
# The label of each node consists of two lines:
#  1. antagonist and protagonist components, possibly followed by
#     delayed simulation flag;
#  2. priority and measure.  The measure may be undefined (if undef is
#     passed as argument), in which case a dash is printed.
# Each state is assumed to be a pair.  The second component is the pair
# (antagonist,protagonist).  The first component of the pair is the pair
# (a/p,b) for delayed simulation; otherwise it is just a/p.
# Antagonist states are drawn as boxes, while protagonist states are
# drawn as ellipses.  Nodes with priority 1 are shaded.
######################################################################
sub ParityGameToDot {
    my ($self,$measure,$graphname) = @_;
    my $nodes = $$self{states};
    my $names = $$self{names};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $priority = $$self{priority};
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
	$name =~ tr/\{\}\[\]//d;
	if ($delayflag ne "") {
	    $name .= ",$delayflag";
	}
	my $style = $type eq "a" ? ",shape=box" : "";
	$style .= ",style=filled,color=lightgray" if $$priority{$node} == 1;
	my $rho = defined $measure ? $$measure{$node} : "-";
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


######################################################################
# Compute satisfying set of BG invariant.
######################################################################
sub ComputeBG {
    my ($game,$invariant,$inverse) = @_;
    my $fair = $$game{fair};

    my $Z = $invariant->Clone;
    my $zeta = Set->new;
    while (not $Z->IsEqual($zeta)) {
	$zeta = $Z->Clone;
	$Z = $game->ComputeBX($Z,$inverse);
	# print "BG iterate is ",
	#   $game->StateRelationToNameString($Z), "\n";
	$Z->Restrict($zeta);
    }
    return $Z;

} # ComputeBG


######################################################################
# Compute satisfying set of BG_fair invariant.
######################################################################
sub ComputeBGfair {
    my ($game,$invariant,$inverse) = @_;
    my $fair = $$game{fair};

    my $Z = $invariant->Clone;
    my $zeta = Set->new;
    while (not $Z->IsEqual($zeta)) {
	$zeta = $Z->Clone;
	foreach my $fairset (values %{$fair}) {
	    my $target = $Z->Intersection($fairset);
	    my $BU = $game->ComputeBU($Z,$target,$inverse);
	    $Z = $game->ComputeBX($BU,$inverse);
	    $Z->Restrict($zeta);
	}
    }
    return $Z;

} # ComputeBGfair


######################################################################
# Compute satisfying set of B invariant U target.
######################################################################
sub ComputeBU {
    my ($game,$invariant,$target,$inverse) = @_;
    my $Z = $target->Clone;
    my $zeta = $target->Clone;
    # print "Target is ", $target->ToString, "\n";
    # print "Invariant is ", $invariant->ToString, "\n";
    while ($zeta->Size > 0) {
	my $BX = $game->ComputeBX($zeta,$inverse);
	# print "BX before restrict is ", $BX->ToString, "\n";
	$BX->Restrict($invariant);
        # print "BX after restrict is ", $BX->ToString, "\n";
	$zeta = $BX->Difference($Z);
	$Z->Add($zeta);
    }
   return $Z;

} # ComputeBU


######################################################################
# Compute satisfying set of BX target.
######################################################################
sub ComputeBX {
    my ($game,$target,$inverse) = @_;

    my $delta = $$game{delta};
    my $EX = Set->new;
    foreach my $state (values %{$target}) {
	$EX->Add($$inverse{$state});
    }
    # print "EX inside BX:", $EX->ToString, "\n";
    my $BX = Set->new;
    foreach my $state (values %{$EX}) {
	my $pre = $$inverse{$state};
	foreach my $pred (values %{$pre}) {
	    my $img = $$delta{$pred};
	    if ($img->IsIncluded($EX)) {
		$BX->Push($pred);
	    }
	}
    }
    return $BX;

} # ComputeBX


######################################################################
# Compute satisfying set of MX target.
######################################################################
sub ComputeMX {
    my ($game,$target,$inverse,$Wp,$Wa) = @_;

    my $delta = $$game{delta};
    my $AX = Set->new;
    foreach my $state (values %{$target}) {
	my $pre = $$inverse{$state};
	foreach my $pred (values %{$pre}) {
	    my $img = $$delta{$pred};
	    if ($img->IsIncluded($target)) {
		$AX->Push($pred);
	    }
	}
    }
    my $MAX = $AX->Intersection($Wa);
    my $EX = Set->new;
    foreach my $state (values %{$target}){
        $EX->Add($$inverse{$state});
    }
    my $MEX = $EX->Intersection($Wp);
    my $MX = $MAX->Union($MEX);
    return $MX;

} # ComputeMX


######################################################################
# Compute satisfying set of EY source.
######################################################################
sub ComputeEY {
    my ($game,$source) = @_;
    my $delta = $$game{delta};
    my $EY = Set->new;

    foreach my $state (values %{$source}){
	$EY->Add($$delta{$state});
    }
    return $EY;

} # ComputeEY


######################################################################
# Compute satisfying set of EP predicate.
######################################################################
sub ComputeEP {
    my ($game,$predicate) = @_;
    my $delta = $$game{delta};
    my $Z = $predicate->Clone;
    my $zeta = $predicate->Clone;
    while ($zeta->Size > 0) {
	my $EY = $game->ComputeEY($zeta);
	$zeta = $EY->Difference($Z);
	$Z->Add($zeta);
    }
    return $Z;

} # ComputeEP


######################################################################
# Compute the winning positions of a bipartite Streett Game.
######################################################################
sub StreettGame {
    my ($game,$inverse,$Wa) = @_;
    my $fair = $$game{fair};
    my $D = Set->new;
    foreach my $StreettConstraint (values %{$fair}) {
	my $afairset = $StreettConstraint->First;
	my $pfairset = $StreettConstraint->Second;
	$D->Add($afairset->Difference($pfairset));
    }
    # This is the general approach, but we know in advance that all
    # states in $Wa are reachable.
    # my $initialstates = $$game{init};
    # print "Initial States ", $initialstates->ToString, "\n";;
    # my $Z = $game->ComputeEP($$game{init});
    # $Z->Restrict($Wa);
    my $Z = $Wa->Clone;
    # print "Z is ", $game->StateRelationToNameString($Z), "\n";
    my $zeta = Set->new;
    while (not $Z->IsEqual($zeta)) {
	$zeta = $Z->Clone;
	foreach my $StreettConstraint (values %{$fair}) {
	    my $afairset = $StreettConstraint->First;
	    my $pfairset = $StreettConstraint->Second;
	    my $invariant = $Z->Difference($D);
	    # print "invariant is ",
	    #   $game->StateRelationToNameString($invariant), "\n";
	    my $target = $game->ComputeBG($invariant, $inverse);
	    $target->Add($Z->Intersection($pfairset));
	    # print "target is ",
	    #   $game->StateRelationToNameString($target), "\n";
	    my $ztemp = $Z->Difference($afairset);
	    # print "Z and not a fair is ",
	    #   $game->StateRelationToNameString($ztemp), "\n";
	    $Z = $game->ComputeBU($Z, $target, $inverse);
	    # print "Result of BU computation is ",
	    #   $game->StateRelationToNameString($Z), "\n";
	    $Z->Add($ztemp);
	    # print "Z is ", $game->StateRelationToNameString($Z), "\n";
	}
	while (1) {
	    my $theta = $Z->Intersection($game->ComputeBX($Z,$inverse));
	    # print "Z and BX Z is ",
	    #   $game->StateRelationToNameString($theta), "\n";
	    last if $Z->IsEqual($theta);
	    $Z = $theta;
	}
    }
    my $result = $game->ComputeBU($Wa, $Z, $inverse);
    # print "the result is ", $game->StateRelationToNameString($result), "\n";
    return $result;

} # StreettGame


#####################################################################
# Compute the angular brackets function.
#####################################################################
sub ang {
    my ($game,$x,$state) = @_;
    my $priority = $$game{priority};
    my $p = $$priority{$state};
    my $oddcount = $$game{oddcount};
    if ($p == 0 && $x <= $oddcount) {
	return 0;
    } else {
	return $x;
    }

} # ang


######################################################################
# Compute the val function.
######################################################################
sub val {
    my ($game,$measure,$state,$Wa) = @_;

    my $delta = $$game{delta};
    my $oddcount = $$game{oddcount};
    my $succ = $$delta{$state};
    if ($Wa->IsMember($state)) {
	my $max = 0;
	foreach my $succs (values %{$succ}) {
	    if ($$measure{$succs} > $max) {
		$max = $$measure{$succs};
	    }
	}
        return $game->ang($max,$state);
    } else {
	my $min = $oddcount + 1;
	foreach my $succs (values %{$succ}) {
	    if ($$measure{$succs} < $min) {
		$min = $$measure{$succs};
	    }
	}
        return $game->ang($min,$state);
    }

} # val


######################################################################
#  To compute the incr function
######################################################################
sub incr {
    my ($game,$x,$priority) = @_;
    my $oddcount = $$game{oddcount};
    my $ret = 0;
    if (($priority == 0) || ($priority == 2)) {
	$ret = $x;
    } else {
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
    my ($game,$measure,$state,$Wa) = @_;
    my $priority = $$game{priority};
    my $prioritycur = $$priority{$state};
    my $delta = $$game{delta};
    my $value = $game->val($measure,$state,$Wa);
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
    my ($game,$inverse,$Wa) = @_;

    my $delta = $$game{delta};
    my $priority = $$game{priority};
    my $gstates = $$game{states};
    my %B = ();
    my %C = ();
    my %measurehash = ();
    my $L = Set->new;
    my $measure = \%measurehash;
    foreach my $state (values %{$gstates}){
	$B{$state} = 0;
	my $succ = $$delta{$state};
	$C{$state} = $succ->Size unless $Wa->IsMember($state);
	$$measure{$state} = 0;
	if ($$priority{$state} == 1) {
	    $L->Push($state);
	}
    }
    while ($L->Size > 0) {
	my $state = $L->Pop;
	my $t = $$measure{$state};
	$B{$state} = $game->val($measure,$state,$Wa);
       	$C{$state} = $game->cnt($measure,$state,$Wa);
	$$measure{$state} = $game->incr($B{$state},$$priority{$state});
	if ($$measure{$state} > $t) {
	    my $P = $$inverse{$state};
	    foreach my $w (values %{$P}) {
		if (not $L->IsMember($w)) {
		    if (not $Wa->IsMember($w)) {
			if (($t == $B{$w}) && ($C{$w} == 1)) {$L->Push($w);}
			if (($t == $B{$w}) && ($C{$w} > 1)) {$C{$w}--;}
		    } else {
			if ($$measure{$state} > $B{$w}) {$L->Push($w);}
		    }
		}
	    }
	}
    }
    my $oddcount = $$game{oddcount};
    my $winningstates = Set->new;
    foreach my $state (values %{$Wa}){
	if ($$measure{$state} <= $oddcount) { $winningstates->Push($state); }
    }
    print $game->ParityGameToDot($measure,"parity game") if $DEBUG > 0;
    return $winningstates;

} # lift

# Required return value.
1;
