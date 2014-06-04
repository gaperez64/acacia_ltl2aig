# $Id: LTL2AUT.pm 2389 2008-06-19 09:09:53Z jobstman $

######################################################################
# Functions to create a Buechi automaton from a LTL parse tree.
#
# The algorithms are descibed in: M. Daniele, F. Giunchiglia, and
# M. Y. Vardi, "Improved Automata Generation for Linear Time
# Temporal Logic," in CAV 1999.
#
# Author: Fabio Somenzi <Fabio@Colorado.EDU>
#
######################################################################
package LTL2AUT;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK $hasToBeStored
$contradiction $redundant $satisfy $computeFairRecur);
@ISA       = qw(Exporter Buechi);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
use strict;
use LTL;
use Buechi;
use Set;


######################################################################
# Creates a new automaton from an LTL formula.
######################################################################
sub new {
    my $class = shift;
    my %params = @_;
    # Read parameters.
    my $formula;
    if (defined($params{formula})) {
	$formula = $params{formula};
    }
    my $method = "LTL2AUT";
    if (defined($params{method})) {
	die "invalid method\n" unless $params{method} eq "GPVW" ||
	  $params{method} eq "GPVW+" || $params{method} eq "LTL2AUT" ||
	     $params{method} eq "Boolean";
	$method = $params{method};
    }
    my $optimize = $method eq "Boolean";
    setMethod($method,$formula);
    # Build the automaton.
    my ($states,$init,$delta) = createAutomatonStructure($formula,$optimize);
    my $self = Buechi->new(
			   states    => $states,
			   init      => $init,
			   delta     => $delta,
			   labels    => AddLabels($states),
			   fair      => ComputeFair($states,$formula)
			  );
    return bless $self, $class;

} # new


######################################################################
# Sets up the function pointers for the chosen method.
######################################################################
sub setMethod {
    my ($method,$formula) = @_;
    if ($method eq "GPVW") {
	$hasToBeStored = \&hasToBeStoredGPVW;
	$contradiction = \&contradictionGPVW;
	$redundant = \&redundantGPVW;
	$satisfy = \&satisfyGPVW;
	$computeFairRecur = \&computeFairRecurSynt;
    } elsif ($method eq "GPVW+") {
	$hasToBeStored = \&hasToBeStoredGPVWplus;
	$contradiction = \&contradictionGPVWplus;
	$redundant = \&redundantGPVWplus;
	$satisfy = \&satisfyGPVWplus;
	$computeFairRecur = \&computeFairRecurSynt;
	$formula->MarkUright;
    } elsif ($method eq "LTL2AUT") {
	$hasToBeStored = \&hasToBeStoredLTL2AUT;
	$contradiction = \&contradictionLTL2AUT;
	$redundant = \&redundantLTL2AUT;
	$satisfy = \&satisfyLTL2AUT;
	$computeFairRecur = \&computeFairRecurSynt;
    } elsif ($method eq "Boolean") {
	$hasToBeStored = \&hasToBeStoredLTL2AUT;
	$contradiction = \&contradictionLTL2AUT;
	$redundant = \&redundantLTL2AUT;
	$satisfy = \&satisfyLTL2AUT;
	$computeFairRecur = \&computeFairRecurBool;
    } else {
	die "unexpected method\n";
    }

} # setMethod


######################################################################
# Generates a cover for a formula.
# Arguments:
#   toCover: the set of formulae to be covered but not processed yet;
#   current: the element of the cover currently being computed;
#   covered: the formuale already processed and covered by current;
#   cover  : the cover computed so far.
######################################################################
sub cover {
    my ($toCover,$current,$covered,$cover) = @_;
    if ($toCover->Size == 0) {
	my $newcover = $cover->Clone($current);
	# print "cover: ", $newcover->ToString, "\n";
	return $newcover;
    } else {
	my $mu = $toCover->Pop;
	$covered = $covered->Clone($mu);
	if (&$hasToBeStored($mu)) {
	    $current = $current->Clone($mu);
	}
	if (&$contradiction($mu,$toCover,$current,$covered)) {
	    return $cover;
	} elsif (&$redundant($mu, $toCover, $current, $covered)) {
	    return cover($toCover, $current, $covered, $cover);
	} elsif (isElementary($mu)) {
	    return cover($toCover, $current->Clone($mu), $covered, $cover);
	} else {
	    my ($alpha1,$alpha2) = tableauRules($mu);
	    my $toCover2 = $toCover->Union($alpha2->Difference($current));
	    my $cover2 = cover($toCover2,$current,$covered,$cover);
	    my $toCover1 = $toCover->Union($alpha1->Difference($current));
	    return cover($toCover1,$current,$covered,$cover2);
	}
    }

} # cover


######################################################################
#
######################################################################
sub hasToBeStoredGPVW {
    return 1;

} # hasToBeStoredGPVW


######################################################################
#
######################################################################
sub contradictionGPVW {
    my ($mu,$toCover,$current,$covered) = @_;
    my $type = $mu->Type;
    return "" if ($type ne "atom");
    my $value = $mu->Value;
    if ($value eq "FALSE") {
	return 1;
    } elsif ($value =~ /=1/) {
	$value =~ s/=1/=0/;
    } elsif ($value =~ /=0/) {
	$value =~ s/=0/=1/;
    } elsif ($value eq "TRUE") {
	$value = "FALSE";	# should never be found in $old
    } else {
	die "unexpected atom\n";
    }
    my ($key,$oldformula);
    while (($key,$oldformula) = each %{$current}) {
	my $oldvalue = $oldformula->Value;
	if ($oldvalue eq $value) {
	    scalar keys %{$current}; # reset generator
	    return 1;
	}
    }
    return "";

} # contradictionGPVW


######################################################################
#
######################################################################
sub redundantGPVW {
    my ($mu, $toCover, $current, $covered) = @_;
    return "";

} # redundantGPVW


######################################################################
#
######################################################################
sub satisfyGPVW {
    my ($state,$formula) = @_;
    return $state->IsMember($formula);

} # satisfyGPVW


######################################################################
#
######################################################################
sub hasToBeStoredGPVWplus {
    my $formula = shift;
    return $formula->Type eq 'binaryop' && $formula->Value eq 'U' ||
      $formula->IsMarked;

} # hasToBeStoredGPVWplus


######################################################################
#
######################################################################
sub contradictionGPVWplus {
    my ($mu,$toCover,$current,$covered) = @_;
    my $type = $mu->Type;
    my $value = $mu->Value;
    return 1 if ($type eq "atom" && $value eq "FALSE");
    my $neg = $mu->Not->PushNegations;
    return $covered->IsMember($neg);

} # contradictionGPVWplus


######################################################################
#
######################################################################
sub redundantGPVWplus {
    my ($mu, $toCover, $current, $covered) = @_;
    return "" unless $mu->Type eq 'binaryop';
    my $value = $mu->Value;
    if ($value eq 'U') {
	my $right = $mu->Right;
	return $toCover->IsMember($right) || $current->IsMember($right);
    } elsif ($value eq 'R' || $value eq 'V') {
	my $left = $mu->Left;
	my $right = $mu->Right;
	return ($toCover->IsMember($left) || $current->IsMember($left)) &&
	  ($toCover->IsMember($right) || $current->IsMember($right));
    }
    return "";

} # redundantGPVWplus


######################################################################
#
######################################################################
sub satisfyGPVWplus {
    my ($state,$formula) = @_;
    return $state->IsMember($formula);

} # satisfyGPVWplus


######################################################################
#
######################################################################
sub hasToBeStoredLTL2AUT {
    return "";

} # hasToBeStoredLTL2AUT


######################################################################
#
######################################################################
sub contradictionLTL2AUT {
    my ($mu,$toCover,$current,$covered) = @_;
    my $neg = $mu->Not->PushNegations;
    return syntacticallyImplied($neg,$toCover->Union($current));

} # contradictionLTL2AUT


######################################################################
#
######################################################################
sub redundantLTL2AUT {
    my ($mu, $toCover, $current, $covered) = @_;
    my $a = $toCover->Union($current);
    return 1 if syntacticallyImplied($mu,$a) &&
      ($mu->Type ne 'binaryop' || $mu->Value ne 'U' ||
      syntacticallyImplied($mu->Right,$a));
    return "";

} # redundantLTL2AUT


######################################################################
#
######################################################################
sub satisfyLTL2AUT {
    my ($set,$formula) = @_;
    return syntacticallyImplied($formula,$set);

} # satisfyLTL2AUT


######################################################################
# Returns 1 if mu is syntactically implied by set.
######################################################################
sub syntacticallyImplied {
    my ($mu,$set) = @_;
    my $type = $mu->Type;
    my $value = $mu->Value;
    return 1 if $type eq 'atom' && $value eq 'TRUE';
    return 1 if $set->IsMember($mu);
    return "" if isElementary($mu);
    my ($alpha1,$alpha2) = tableauRules($mu);
    my $ok = 1;
    foreach my $formula (values %{$alpha1}) {
	$ok = syntacticallyImplied($formula,$set);
	last unless $ok;
    }
    return 1 if $ok;
    $ok = 1;
    foreach my $formula (values %{$alpha2}) {
	$ok = syntacticallyImplied($formula,$set);
	last unless $ok;
    }
    return $ok;

} # syntacticallyImplied


######################################################################
# Generate the sets that cover mu by applying the tableau rules.
######################################################################
sub tableauRules {
    my $mu = shift;
    my $type = $mu->Type;
    die "unexpected node type\n" unless $type eq "binaryop";
    my $value = $mu->Value;
    my ($alpha1,$alpha2);
    if ($value eq "*") {
	$alpha1 = Set->new($mu->Left, $mu->Right);
	$alpha2 = Set->new(LTL->new("FALSE"));
    } elsif ($value eq "+") {
	$alpha1 = Set->new($mu->Left);
	$alpha2 = Set->new($mu->Right);
    } elsif ($value eq "U") {
	$alpha1 = Set->new($mu->Right);
	$alpha2 = Set->new($mu->Left, $mu->X);
    } elsif ($value eq "R" || $value eq "V") {
	$alpha1 = Set->new($mu->Left, $mu->Right);
	$alpha2 = Set->new($mu->Right, $mu->X);
    } else {
	die "unexpected binary operator\n";
    }
    return ($alpha1,$alpha2);

} # tableauRules


######################################################################
# Returns 1 if a formula is elementary; "" otherwise.
######################################################################
sub isElementary {
    my $formula = shift;
    my $type = $formula->Type;
    return $type eq "atom" ||
      $type eq "temporalop" && $formula->Value eq "X";

} # isElementary


######################################################################
# Creates a (possibly) optimized cover for an LTL formula.
# The covers returned by buildCover cannot be modified; otherwise
# the cache and the state-to-covers map may be corrupted.
######################################################################
sub buildCover {
    my ($formulae,$cache,$optimize,$otherStates,$stateToCovers) = @_;
#     print "Cover cached formulae: ", $cache->First->ToString, "\n"; # diag
    my $cachedF = $cache->First->FindEqual($formulae);
    my $cachedS = $cache->Second;
    if (defined $cachedF) {
# 	print "Cache hit for ", $formulae->ToString, "\n"; # diag
# 	print "Returning ", $$cachedS{$cachedF}->ToString, "\n"; # diag
	return $$cachedS{$cachedF};
    }
#     print "Cover for ", $formulae->ToString, "\n"; # diag
    my $cover = cover($formulae->Clone, Set->new, Set->new, Cover->new);
    if ($optimize) {
	$cover = $cover->PrimeAndIrredundant;
	$cover->IncreaseSharing($otherStates,$stateToCovers);
	foreach my $state (values %{$cover}) {
	    unless (defined($$stateToCovers{$state})) {
		$$stateToCovers{$state} = Set->new($cover);
	    } else {
		$$stateToCovers{$state}->Push($cover);
	    }
	}
    }
    $cache->First->Push($formulae);
    $$cachedS{$formulae} = $cover->Clone;
    return $cover;

} # buildCover


######################################################################
# Creates the automaton from the LTL formula.
######################################################################
sub createAutomatonStructure {
    my ($formula,$optimize) = @_;
    my $stc = {};
    my $cache = Pair->new(Cover->new,{});
    my %delta = ();
    my $q = Cover->new;
    my $init = buildCover(Set->new($formula), $cache, $optimize, $q, $stc);
    my $u = $init->Clone;
    $q->Add($init);
    # print "Initial U: ", $u->ToString, "\n";
    while ($u->Size > 0) {
	my $s = $u->Pop;
	$delta{$s} = Set->new;
	# print "s: ", $s->ToString, " size of U = ", $u->Size, "\n";
	# print " size of Q = ", $q->Size, "\n";
	my $nextS = findNext($s);
	# print "nextS: ", $nextS->ToString, "\n";
	my $cover = buildCover($nextS, $cache, $optimize, $q, $stc);
#	print "cover: ", $cover,"\n";	
#	print $cover->ToString,"\n";
	foreach my $r (values %{$cover}) {
	    my $rprime = $q->FindEqual($r);
	    if (defined($rprime)) {
		# print "TA-DA ", $rprime->ToString, "\n";
		$delta{$s}->Push($rprime);
	    } else {
		# print "TA-DE ", $r->ToString, "\n";
		$q->Push($r);
		$delta{$s}->Push($r);
		$u->Push($r);
	    }
	}
    }
    return ($q,$init,\%delta);

} # createAutomatonStructure


######################################################################
# Finds the formulae mu such that X mu is in set state.
######################################################################
sub findNext {
    my $state = shift;
    my $next = Set->new;
    foreach my $formula (values %{$state}) {
	if ($formula->Type eq "temporalop" && $formula->Value eq "X") {
	    $next->Push($formula->Left);
	}
    }
    return $next;

} # findNext


######################################################################
# Add labels to states of an automaton.
######################################################################
sub AddLabels {
    my $states = shift;
    my %labels = ();
    foreach my $state (values %{$states}) {
	my $label = Set->new;
	foreach my $eta (values %{$state}) {
	    if ($eta->Type eq "atom" && $eta->Value ne "TRUE") {
		$label->Push($eta);
	    }
	}
	$labels{$state} = $label;
    }
    return \%labels;

} # AddLabels


######################################################################
# Compute the fair sets from the node set.
######################################################################
sub ComputeFair {
    my ($nodes,$formula) = @_;
    my $fair = Set->new;
    my $visited = Set->new;
    &$computeFairRecur($nodes,$formula,$visited,$fair);
    return $fair;

} # ComputeFair


######################################################################
# Recursive procedure that computes the fair sets from the state set.
######################################################################
sub computeFairRecurSynt {
    my ($nodes,$formula,$visited,$fair) = @_;
    return if $visited->IsMember($formula);
    $visited->Push($formula);
    if ($formula->Type eq "binaryop" && $formula->Value eq "U" &&
       ($formula->Right->Type ne "atom" ||
	$formula->Right->Value ne "TRUE")) {
	# Build fair set for this Until formula.
	my $fairset = Set->new;
	foreach my $node (values %{$nodes}) {
	    if (! &$satisfy($node,$formula) ||
		&$satisfy($node,$formula->Right)) {
		$fairset->Push($node);
	    }
	}
	$fair->Push($fairset);
    }
    # Recursively examine children if they exist.
    computeFairRecurSynt($nodes,$formula->Left,$visited,$fair)
      if exists($formula->{left});
    computeFairRecurSynt($nodes,$formula->Right,$visited,$fair)
      if exists($formula->{right});

} # computeFairRecurSynt


######################################################################
# Recursive procedure that computes the fair sets from the state set.
######################################################################
sub computeFairRecurBool {
    my ($nodes,$formula,$visited,$fair) = @_;
    return if $visited->IsMember($formula);
    $visited->Push($formula);
    if ($formula->Type eq "binaryop" && $formula->Value eq "U" &&
       ($formula->Right->Type ne "atom" ||
	$formula->Right->Value ne "TRUE")) {
	# Build fair set for this Until formula.
	my $fairset = Set->new;
	my $cover = cover(Set->new($formula), Set->new,
			  Set->new, Cover->new);
	my $coverR = cover(Set->new($formula->Right), Set->new,
			   Set->new, Cover->new);
	foreach my $node (values %{$nodes}) {
	    if (! $cover->IsImplied($node) || $coverR->IsImplied($node)) {
		$fairset->Push($node);
	    }
	}
	$fair->Push($fairset);
    }
    # Recursively examine children if they exist.
    computeFairRecurBool($nodes,$formula->Left,$visited,$fair)
      if exists($formula->{left});
    computeFairRecurBool($nodes,$formula->Right,$visited,$fair)
      if exists($formula->{right});

} # computeFairRecurBool


######################################################################
# Returns 1 if there are no Untils in the formula; returns "" otherwise.
######################################################################
sub NoUntil {
    my $formula = shift;
    my $visited = Set->new;
    return noUntilRecur($formula,$visited);

} # NoUntil


######################################################################
# Recursive procedure that finds Untils in a formula.
######################################################################
sub noUntilRecur {
    my ($formula,$visited) = @_;
    return if $visited->IsMember($formula);
    $visited->Push($formula);
    if ($formula->Type eq "binaryop" && $formula->Value eq "U" &&
       ($formula->Right->Type ne "atom" ||
	$formula->Right->Value ne "TRUE")) {
	return "";
    }
    # Recursively examine children if they exist.
    if (exists($formula->{left})) {
	return "" unless noUntilRecur($formula->Left,$visited);
    }
    if (exists($formula->{right})) {
	return noUntilRecur($formula->Right,$visited);
    }
    return 1;

} # noUntilRecur
