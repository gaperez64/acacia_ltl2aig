# $Id: Heap.pm,v 1.2 2005/09/26 11:44:23 bjobst Exp $

######################################################################
# Functions to manipulate a heap-based priority queue.
#
#
# Author: Fabio Somenzi <Fabio@Colorado.EDU>
#
######################################################################
package Heap;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK);
@ISA       = qw(Exporter);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
use strict;


######################################################################
# Create a new heap from a list.
######################################################################
sub new {
    my ($class, $list) = @_;
    my $self = [];
    if (defined $list) {
	push @$self, @$list;
	for (my $i = (@$self >> 1) - 1; $i >= 0; $i--) {
	    heapify($self, $i);
	}
    }
    return bless $self, $class;

} # new


######################################################################
# Make a copy of a priority queue.
######################################################################
sub Clone {
    my $self = shift;
    my $clone = [];
    foreach my $slot (@$self) {
	push @$clone, [$$slot[0], $$slot[1]];
    }
    return bless $clone, ref $self;

} # Clone


######################################################################
# Push an item in a priority queue.
######################################################################
sub Push {
    my ($self, $key, $item) = @_;
    my $i = @$self;
    while ($i > 0 and $$self[($i - 1) >> 1][0] > $key) {
	$$self[$i] = $$self[($i - 1) >> 1];
	$i = ($i - 1) >> 1;
    }
    $$self[$i] = [$key, $item];

} # Push


######################################################################
# Extract the element with the minimum key from a priority queue.
######################################################################
sub Pop {
    my $self = shift;
    my $first = $$self[0];
    my $last = pop @$self;
    if (@$self > 0) {
	$$self[0] = $last;
	$self->heapify(0);
    }
    return ($$first[0], $$first[1]);

} # Pop


######################################################################
# Return the number of items in the priority queue.
######################################################################
sub Size {
    my $self = shift;
    return scalar @$self;

} # Size


######################################################################
# Test the heap property of a priority queue.
# Returns 1 if successful; 0 otherwise.
######################################################################
sub Test {
    my $self = shift;
    my $size = @$self;
    for (my $i = 1; $i < $size; $i++) {
	return 0 if $$self[$i][0] < $$self[($i - 1) >> 1][0];
    }
    return 1;

} # Test


######################################################################
# Maintain the heap property of a priority queue.
######################################################################
sub heapify {
    my ($self, $i) = @_;
    my $size = @$self;
    my $smallest = $i;
    my $save = $$self[$i];
    my $key = $$save[$i];
    while (1) {
	my $left  = ($i << 1) + 1;
	my $right = ($i + 1) << 1;
	my $minkey;
	if ($left < $size and ($minkey = $$self[$left][0]) < $key) {
	    $smallest = $left;
	} else {
	    $minkey = $key;
	}
	if ($right < $size and $$self[$right][0] < $minkey) {
	    $smallest = $right;
	}
	last if $smallest == $i;
	$$self[$i] = $$self[$smallest];
	$i = $smallest;
    }
    $$self[$i] = $save;

} # heapify


######################################################################
# Returns the parent of the i-th element in a heap.
######################################################################
sub parent {
    my $i = shift;
    return ($i - 1) >> 1;

} # parent


######################################################################
# Returns the left child of the i-th element in a heap.
######################################################################
sub left {
    my $i = shift;
    return ($i << 1) + 1;

} # left


######################################################################
# Returns the right child of the i-th element in a heap.
######################################################################
sub right {
    my $i = shift;
    return ($i + 1) << 1;

} # right


######################################################################
# Returns the item stored in the i-th element in a heap.
######################################################################
sub item {
    my ($self,$i) = @_;
    return $$self[$i][1];

} # item


######################################################################
# Returns the key of the i-th element in a heap.
######################################################################
sub key {
    my ($self,$i) = @_;
    return $$self[$i][0];

} # key


######################################################################
# Converts the elements of a pair to a comma-separated list enclosed in
# brackets.  Works for pairs of scalars and references.  The references
# must be to objects of classes that provide a "ToString" method;
# otherwise the references themselves will be interpolated in the
# string.
######################################################################
sub ToString {
    my $self = shift;
    my $delim = "";
    my $string = "[";
    foreach my $slot (@$self) {
	my $key = $$slot[0];
	my $item = $$slot[1];
	$string .= $delim;
	# We try to locate the ToString method in the class of $item.
	# If we fail, we assume that $item is a scalar, and rely on
	# Perl's built-in conversion.
	my $method = "defined &" . ref($_) . "::ToString";
	if (eval $method) {
	    $string .= $item->ToString;
	} else {
	    $string .= $item;
	}
	$string .= "($key)";
	$delim = ",";
    }
    $string .= "]";
    return $string;

} # ToString
