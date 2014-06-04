# $Id: List.pm,v 1.2 2005/09/26 11:44:23 bjobst Exp $

######################################################################
# Functions to manipulate lists of references and scalars.
#
# When creating listss of objects, it is a good idea to provide a ToString
# method for those objects.
#
# Author: Fabio Somenzi <Fabio@Colorado.EDU>
#
######################################################################
package List;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK);
@ISA       = qw(Exporter);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
use strict;



######################################################################
# Create a new list from a list of arguments.
# The list can be empty.
######################################################################
sub new {
    my $class = shift;
    my @self = ();
    foreach (@_) {
	push(@self, $_);
    }
    return bless \@self, $class;

} # new


######################################################################
# Make a copy of a list.  If arguments are passed to the method,
# they are interpreted as new elements to be added to the copy.
######################################################################
sub Clone {
    my $self = shift;
    my @clone = @{$self};
    foreach (@_) {
	push(@clone, $_);
    }
    return bless \@clone, ref $self;

} # Clone


######################################################################
# Add elements to a set.
######################################################################
sub Push {
    my $self = shift;
    foreach (@_) {
	push(@$self,$_);
    }

} # Push


######################################################################
# Add elements to a list from another list.
######################################################################
sub Append {
    my ($self,$other) = @_;
    foreach (@$other) {
	push(@$self,$_);
    }

} # Append


######################################################################
# Extract first element from a list and return it.
######################################################################
sub Pop {
    my $self = shift;
    return pop(@$self);

} # Pop


######################################################################
# Return first element of a list without removing it.
######################################################################
sub Head {
    my $self = shift;
    if (@{$self} > 0) {
	return $$self[0];
    } else {
	return undef;
    }

} # Head


######################################################################
# Returns the cardinality of a list.
######################################################################
sub Size {
    my $self = shift;
    return scalar @{$self};

} # Size


######################################################################
# Converts the elements of a list to a comma-separated list enclosed in
# brackets.  Works for lists of scalars and references.  The references
# must be to objects of classes that provide a "ToString" method;
# otherwise the references themselves will be interpolated in the
# string.
######################################################################
sub ToString {
    my $self = shift;
    my $delim = "";
    my $string = "[";
    foreach (@{$self}) {
	$string .= $delim;
	# We try to locate the ToString method in the class of $_.
	# If we fail, we assume that $_ is a scalar, and rely on
	# Perl's built-in conversion.
	my $method = "defined &" . ref($_) . "::ToString";
	if (eval $method) {
	    $string .= $_->ToString;
	} else {
	    $string .= $_;
	}
	$delim = ",";
    }
    $string .= "]";
    return $string;

} # ToString
