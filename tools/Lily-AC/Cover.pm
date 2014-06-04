# $Id: Cover.pm,v 1.3 2006/03/15 14:04:39 bjobst Exp $

######################################################################
# Functions to manipulate covers.
#
# Covers are sets of sets.  Each set in a cover is a product term.
# An empty product term is a tautology.  An empty cover is a contradiction.
# The elements of a product term are the literals.  They are supposed
# to be objects providing a Negate method.
#
# Author: Fabio Somenzi <Fabio@Colorado.EDU>
#
######################################################################
package Cover;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK);
@ISA       = qw(Exporter Set);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
use strict;
use Set;


######################################################################
# Finds the complete sum of a cover by iterated consensus.
######################################################################
sub CompleteSum {
    my $self = shift;
    # Sort terms by increasing number of literals.
    my @list = sort {$a->Size <=> $b->Size} values %{$self};
    # If we have a tautologous term, the cover is tautologous.
    if (@list > 0 && $list[0]->Size == 0) {
	return Cover->new($list[0]);
    }
    my $i;
    # Check terms for single-cube containment.  Rely on ordering for
    # efficiency.  A term can only be contained by another term with
    # fewer literals.
    for ($i = @list - 1; $i > 0; $i--) {
	my $j;
	for ($j = 0; $j < $i; $j++) {
	    if ($list[$j]->Size == $list[$i]->Size) {
		last;
	    } elsif ($list[$j]->IsIncluded($list[$i])) {
		splice(@list, $i, 1);
		last;
	    }
	}
    }
    # Now do iterated consensus.
    for ($i = 1; $i < @list; $i++) {
	my $j;
      LOOP: for ($j = 0; $j < $i; $j++) {
	    my $consensus = Consensus($list[$i],$list[$j]);
	    if (defined($consensus)) {
		my $k;
		for ($k = 0; $k < @list; $k++) {
		    if ($list[$k]->IsIncluded($consensus)) {
			next LOOP;
		    } elsif ($consensus->IsIncluded($list[$k])) {
			splice(@list, $k, 1);
			$i-- if $k <= $i;
			$j-- if $k <= $j;
			$k--;
		    }
		}
		push(@list,$consensus);
	    }
	}
    }
    my $complete = Cover->new(@list);
    return $complete;

} # CompleteSum


######################################################################
# Returns the consensus of two product terms given as sets of
# atomic propositions.  Returns undef if the consensus is not defined.
######################################################################
sub Consensus {
    my ($first,$second) = @_;
    my $consensus = Set->new;
    my $pivot = undef;
    foreach my $literal (values %{$first}) {
	my $complement = $literal->Negate;
	if ($second->IsMember($complement)) {
	    if (defined($pivot)) {
		return undef;
	    } else {
		$pivot = $complement;
	    }
	} else {
	    $consensus->Push($literal);
	}
    }
    return undef unless defined($pivot);
    foreach my $literal (values %{$second}) {
	$consensus->Push($literal) unless $literal == $pivot;
    }
    return $consensus;

} # Consensus


######################################################################
# Returns the cofactor of a cover with respect of a product term c.
######################################################################
sub Cofactor {
    my ($self,$c) = @_;
    my $cofactor = Cover->new;
    my $negations = Set->new;
    foreach my $literal (values %{$c}) {
	my $complement = $literal->Negate;
	$negations->Push($complement);
    }
    foreach my $term (values %{$self}) {
	if ($term->IsDisjoint($negations)) {
	    my $newTerm = $term->Clone;
	    $newTerm->Subtract($c);
	    $cofactor->Push($newTerm);
	}
    }
    return $cofactor;

} # Cofactor


######################################################################
# Returns 1 if a cover is tautologous.
######################################################################
sub IsTautology {
    my $self = shift;
    my $complete = $self->CompleteSum;
    return "" if $complete->Size != 1;
    my $term = $complete->Pick;
    return $term->Size == 0;

} # IsTautology


######################################################################
# Returns a prime and irredundant version of a cover.
# No minimality guaranteed.
######################################################################
sub PrimeAndIrredundant {
    my $self = shift;
    my $pai = $self->CompleteSum;
    # Try to drop each term in turn.
    foreach my $term (sort {$b->Size <=> $a->Size} values %{$pai}) {
	$pai->Delete($term);
	unless ($pai->IsImplied($term)) {
	    $pai->Push($term);
	}
    }
    return $pai;

} # PrimeAndIrredundant


######################################################################
# Returns 1 if a cover is implied by a term.
######################################################################
sub IsImplied {
    my ($self,$term) = @_;
    my $cofactor = $self->Cofactor($term);
    return $cofactor->IsTautology;

} # IsImplied


######################################################################
# Returns the supercube of a cover.
######################################################################
sub Supercube {
    my $self = shift;
    my $supercube = Set->new;
    my $unate = Set->new;
    my $binate = Set->new;
    foreach my $term (values %{$self}) {
	foreach my $lit (values %{$term}) {
	    next if $binate->IsMember($lit) or $unate->IsMember($lit);
	    my $neg = $lit->Negate;
	    if ($unate->IsMember($neg)) {
		$unate->Delete($neg);
		$binate->Push($lit,$neg);
	    } else {
		$unate->Push($lit);
	    }
	}
    }
    return $unate;

} # Supercube


######################################################################
# Returns the set of literals of a cover.
# Positive and negative literals are returned in two sets.  Both
# literals are returned as long as at least one appears in the cover.
# For each variable appearing in the cover, the literal that is found
# first (or the only one found) is considered the positive literal.
######################################################################
sub Literals {
    my $self = shift;
    my $positive = Set->new;
    my $negative = Set->new;
    foreach my $term (values %{$self}) {
	foreach my $lit (values %{$term}) {
	    unless ($positive->IsMember($lit) or $negative->IsMember($lit)) {
		$positive->Push($lit);
		$negative->Push($lit->Negate);
	    }
	}
    }

    return ($positive,$negative);

} # Literals


######################################################################
# Reduces a cover to increase term sharing with another cover.
######################################################################
sub IncreaseSharing {
    my ($self,$other,$stateToCovers) = @_;
    # We sort the terms of the other cover so as to consider those
    # with fewer literals first.  The rationale is that we want to minimize
    # the amount of reduction required.
#    print "IncreaseSharing: ", $self->ToString, "\n";
    sub bysize {$a->Size <=> $b->Size};
    foreach my $term (values %{$self}) {
	next if $other->FindEqual($term);
	my $rest = undef;	# the other terms of the cover
      TARGET: foreach my $target (sort bysize values %{$other}) {
	    next TARGET unless $term->IsIncluded($target);
	    my $extra = $target->Difference($term);
	    unless (defined $rest) {
		$rest = $self->Clone;
		$rest->Delete($term);
	    }
	    my $reduced = $term->Clone;
	    foreach my $lit (values %{$extra}) {
		my $test = $reduced->Clone($lit->Negate);
		next TARGET unless $rest->IsImplied($test);
		$reduced->Push($lit);
	    }
	    die "Internal error in IncreaseSharing\n"
	      unless $target->IsEqual($reduced);
	    $self->Delete($term);
	    $self->Push($reduced);
	    last TARGET;
	}
    }
    # Check whether we can find existing states that can be reduced
    # to the new states.
    foreach my $term (values %{$self}) {
	next if $other->FindEqual($term);
      TARGET: foreach my $target (values %{$other}) {
	    next TARGET unless $target->IsIncluded($term);
	    # Make sure the literals to be added are atomic
	    # propositions, so that the next state cover is unaffected.
	    my $extra = $term->Difference($target);
	    foreach my $lit (values %{$extra}) {
		next TARGET unless $lit->Type eq 'atom';
	    }
	    # Check whether the reduction of the existing state is legal
	    # in all the covers in which it appears.
	    my $covers = $$stateToCovers{$target};
	    foreach my $cover (values %{$covers}) {
		my $reduced = $target->Clone;
		my $rest = $cover->Clone;
		$rest->Delete($target);
		foreach my $lit (values %{$extra}) {
		    my $test = $reduced->Clone($lit->Negate);
		    next TARGET unless $rest->IsImplied($test);
		    $reduced->Push($lit);
		}
		die "Internal error in IncreaseSharing\n"
		  unless $term->IsEqual($reduced);
	    }
	    # Reduction succeeded.  Change the covers.
	    $target->Add($extra);
	    last TARGET;
	}
    }
#     print "On exit:         ", $self->ToString, "\n\n";	# diag
} # IncreaseSharing


######################################################################
# Finds a term in a cover of states if it is there.  Returns the term
# if successful; undef otherwise.
######################################################################
sub FindEqual {
    my ($self,$r) = @_;
    foreach my $state (values %{$self}) {
	return $state if $r->IsEqual($state);
    }
    return undef;

} # findEqual

######################################################################
# Returns 1 if every set in the first cover is included in a set of
# the second cover, otherwise returns "".
######################################################################
sub IsIncluded {
#    print "call Cover::IsIncluded\n";
    my ($self,$other) = @_;
  S: foreach my $s(values %$self) {
	foreach my $o (values %$other) {
	    if ($s->IsIncluded($o)) {
		next S;
	    }
	}
	return "";
    }
    return 1;
}
