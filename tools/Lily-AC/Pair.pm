# $Id: Pair.pm,v 1.6 2007/05/31 16:53:18 bjobst Exp $

######################################################################
# Functions to manipulate ordered pairs of references and scalars.
#
# Pairs are unique: the same reference is returned every time the same
# elements are passed to "new."  This makes it easy to work with sets
# of pairs.
#
# When creating pairs of objects, it is a good idea to provide a ToString
# method for those objects.
#
# Author: Fabio Somenzi <Fabio@Colorado.EDU>
#
######################################################################
package Pair;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK %unique);
@ISA       = qw(Exporter);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
use strict;


######################################################################
# Create a new ordered pair from a list of arguments.
######################################################################
sub new {
    my ($class,$first,$second) = @_;
    my $key = join(',', $first, $second);
    return $unique{$key} if exists $unique{$key};
    my $new = [$first,$second];
    $unique{$key} = $new;
    return bless $new, $class;

} # new



######################################################################
# Returns the first element of a pair.
######################################################################
sub First {
    return $_[0][0];

} # First


######################################################################
# Return the second element of a pair.
######################################################################
sub Second {
    return $_[0][1];

} # Second


######################################################################
# Delete a pair from the unique table and then destroy it.
# Nothing is done to the pair's components.
######################################################################
sub Delete {
    my $self = shift;
    my $key = join(',', $$self[0], $$self[1]);
    delete $unique{$key};
    undef $self;

} # Delete

######################################################################
# Returns 1 if two pairs are equal; "" otherwise.
######################################################################
sub IsEqual {
    my ($self,$other) = @_;
    my $first1 = $self->First;
    my $first2 = $other->First;
    my $second1 = $self->Second;
    my $second2 = $other->Second;
    
    return "" if (ref($first1) ne ref($first2));
    return "" if (ref($second1) ne ref($second2));

	my $method = ref($first1)."::IsEqual";
	if (defined &$method) {
		if (not $first1->IsEqual($first2)) {
			return "";
		}
	} else {
		if ($first1 ne $first2) {
			return "";
		}
	}

	$method = ref($second1)."::IsEqual";
	if (defined &$method) {
		if (not $second1->IsEqual($second2)) {
			return "";
		}
	} else {
		if ($second1 ne $second2) {
			return "";
		}
	}

    return 1;

} # IsEqual

######################################################################
# Takes a Pair (S,O) of two Sets of Pair and an instance of the first 
# component D and returns a Pair (S',O') of two Sets with
# S'={s|(d,s) in S and (d == D)}
# O'= {o|(d,o) in O and (d == D)}.
######################################################################
sub IsIncludedFirst {
    my ($self,$direction) = @_;
    my $first = $self->First;
    my $second = $self->Second;
    
    return Pair->new($first->IsIncludedFirst($direction),
    			     $second->IsIncludedFirst($direction));
} # IsIncludedFirst

######################################################################
# Converts the elements of a pair to a comma-separated list enclosed in
# brackets.  Works for pairs of scalars and references.  The references
# must be to objects of classes that provide a "ToString" method;
# otherwise the references themselves will be interpolated in the
# string.
######################################################################
sub ToString {
    my ($self,$names) = @_;
    my $delim = "";
    if (defined $$names{$self}) {
    	return $$names{$self};
    }
    my $string = "[";
    foreach (@{$self}) {
	$string .= $delim;
	# We try to locate the ToString method in the class of $_.
	# If we fail, we assume that $_ is a scalar, and rely on
	# Perl's built-in conversion.
	my $method = ref($_) . "::ToString";	
	if (defined &$method) {
	    $string .= $_->ToString($names);
	} else {
	    $string .= $_;
	}
	$delim = ",";
    }
    $string .= "]";
    return $string;

} # ToString

sub Size {
    my $self = shift;
    my $size = $self->First->Size + $self->Second->Size;
    return $size;
}
1;
