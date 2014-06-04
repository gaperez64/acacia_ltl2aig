# $Id: Set.pm,v 1.9 2006/04/25 16:02:30 bjobst Exp $

######################################################################
# Functions to manipulate sets of references and scalars.
#
# The functions is this package manipulate sets of references
# and scalars.  Both types of sets are implemented as hash
# tables in which the entries are used as both keys and values.
# This is so because references cannot be dereferenced once they have
# been stored as keys in a hash table.  (They are turned into strings in
# the process.)  For scalars we would not need this trick, but we use
# it nonetheless so that we can use a common set of procedures to
# manipulate all sets.
#
# To enumerate all the elements of a set, use code like this:
#
#   foreach my $element ($set->List) {
#       use($element);
#   }
#
# When creating sets of objects, it is a good idea to provide a ToString
# method for those objects.
#
# Author: Fabio Somenzi <Fabio@Colorado.EDU>
#
######################################################################
package Set;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK);
@ISA       = qw(Exporter);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.01;
use strict;
#use Tie::InsertOrderHash;

# Overloading seems to work, but is horribly inefficient.  Hence it is
# commented out.
# use overload
#   '""' => "ToString",
#   'fallback' => 1;

######################################################################
# Create a new set from a list of arguments.
# The list can be empty.
######################################################################
sub new {
    my $class = shift;
#    tie my %hash => 'Tie::InsertOrderHash';
#    my $self = \%hash;
    my $self = {};
    foreach (@_) {
	$$self{$_} = $_;
    }
    return bless $self, $class;

} # new


######################################################################
# Make a copy of a set.  If arguments are passed to the method,
# they are interpreted as new elements to be added to the copy.
######################################################################
sub Clone {
    my $self = shift;
    my %clone = %{$self};
    foreach (@_) {
	$clone{$_} = $_;
    }
    return bless \%clone, ref $self;

} # Clone


######################################################################
# Take the union of two sets.
######################################################################
sub Union {
    my ($self,$other) = @_;
    my %union = %{$self};
    foreach (keys %{$other}) {
	$union{$_} = $$other{$_} unless exists $union{$_};
    }
    return bless \%union, ref $self;

} # Union


######################################################################
# Take the intersection of two sets.
######################################################################
sub Intersection {
    my ($self,$other) = @_;
    my %intersection = ();
    foreach (keys %{$other}) {
	$intersection{$_} = $$other{$_} if exists $$self{$_};
    }
    return bless \%intersection, ref $self;

} # Intersection


######################################################################
# Take the difference of two sets.
# This is also used for complementation.
######################################################################
sub Difference {
    my ($self,$other) = @_;
    my %diff = ();
    foreach (keys %{$self}) {
	$diff{$_} = $$self{$_} unless exists $$other{$_};
    }
    return bless \%diff, ref $self;

} # Difference


######################################################################
# Take the symmetric difference of two sets.
######################################################################
sub SymmDifference {
    my ($self,$other) = @_;
    my %diff = ();
    foreach (keys %{$self}) {
	$diff{$_} = $$self{$_} unless exists $$other{$_};
    }
    foreach (keys %{$other}) {
	$diff{$_} = $$other{$_} unless exists $$self{$_};
    }
    return bless \%diff, ref $self;

} # SymmDifference


######################################################################
# Add elements to a set.
######################################################################
sub Push {
    my $self = shift;
    foreach (@_) {
	$$self{$_} = $_;
    }

} # Push


######################################################################
# Add elements to a set from another set.
######################################################################
sub Add {
    my ($self,$other) = @_;
    foreach (keys %{$other}) {
	$$self{$_} = $$other{$_};
    }

} # Add


######################################################################
# Subtract elements from a set if they are in another set.
######################################################################
sub Subtract {
    my ($self,$other) = @_;
    foreach (keys %{$other}) {
	delete $$self{$_};
    }

} # Subtract


######################################################################
# Extract one element at random from a set and return it.
######################################################################
sub Pop {
    my $self = shift;
    if (scalar keys(%{$self}) > 0) {
	my ($key,$value) = each %{$self};
	delete $$self{$key};
	return $value;
    } else {
	return undef;
    }

} # Pop


######################################################################
# Return one element at random from a set without removing it.
######################################################################
sub Pick {
    my $self = shift;
    if (scalar keys(%{$self}) > 0) {
	my ($key,$value) = each %{$self};
	return $value;
    } else {
	return undef;
    }

} # Pick


######################################################################
# Delete elements from a set.
######################################################################
sub Delete {
    my $self = shift;
    foreach (@_) {
	delete($$self{$_});
    }

} # Delete


######################################################################
# Remove from a set all elements that are not in another set.
######################################################################
sub Restrict {
    my ($self,$other) = @_;
    foreach (keys %{$self}) {
	delete($$self{$_}) unless exists($$other{$_});
    }

} # Restrict


######################################################################
# Returns the cardinality of a set.
######################################################################
sub Size {
    return scalar keys(%{shift()});

} # Size


######################################################################
# Check an element for containment in a set.
######################################################################
sub IsMember {
    return exists $_[0]->{$_[1]};

} # IsMember


######################################################################
# Returns 1 if two sets are equal; "" otherwise.
######################################################################
sub IsEqual {
    my ($self,$other) = @_;
    return "" if $self->Size != $other->Size;
    foreach (keys %{$other}) {
	return "" unless exists $$self{$_};
    }
    return 1;

} # IsEqual

sub IsEqualDeep {
    my ($self,$other) = @_;
    return "" if $self->Size != $other->Size;
  P: foreach my $o (values %$other) {
	foreach my $s (values %$self) {
	    next P if $s->IsEqual($o);
	}
	return "";
    }
    return 1;
} # IsEqual

######################################################################
# Returns 1 if the set on which the method is called is included in
# the argument; "" otherwise.
######################################################################
sub IsIncluded {
    my ($self,$other) = @_;
    return 1 if ($self eq $other); #sets are the same
    foreach (keys %{$self}) {
	unless (exists $$other{$_}) {
	    return "";
	}
    }
    return 1;

} # IsIncluded


######################################################################
# Returns 1 if the set on which the method is called is disjoint from
# the argument; "" otherwise.
######################################################################
sub IsDisjoint {
    my ($self,$other) = @_;
    foreach (keys %{$self}) {
	if (exists $$other{$_}) {
	    return "";
	}
    }
    return 1;

} # IsDisjoint


######################################################################
# Returns a list of the elements of the set.
######################################################################
sub List {
    my $self = shift;
    return values %{$self};

} # List


######################################################################
# Returns a sorted list of the elements of the set.
# The comparison function is an optional argument.
# The default is lexicographical ordering.  To get numerical ordering
# invoke like this:  $myset->Sort(sub{$Set::a <=> $Set::b}).
######################################################################
sub Sort {
    my ($self,$cmp) = @_;
    if (defined $cmp) {
	return sort $cmp values %{$self};
    } else {
	return sort values %{$self};
    }

} # Sort


######################################################################
# Converts the elements of a set to a comma-separated list enclosed in
# braces.  Works for sets of scalars and references.  The references
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
    my $string = "{";
    foreach (values %{$self}) {
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
    $string .= "}";
    return $string;

} # ToString


######################################################################
# Takes a list of lists and disjoins the lists to a single list.
######################################################################
sub DisjoinElements {
    my $self = shift;
    my $set = Set->new;
    foreach (values %$self) {
	die if (ref ne "Set");
	$set = $set->Union($_);
    }
    return $set;
} # DisjoinElements


######################################################################
# The following fct are for special lists consisting of Pairs.

######################################################################
# Takes a Set of Pair S and an instance of the first component D and 
# returns a Set S'={s|(d,s) in S and (d is included in D)}.
######################################################################
use Pair;
sub IsIncludedFirst {
    my ($self,$direction) = @_;
    my $retSet = Set->new;
    
    foreach ( values %$self) {
    	my $dir = $_->First;
    	my $states = $_->Second;
	if (($dir eq $direction) ||
	    $dir->IsIncluded($direction)) {
    		$retSet->Push($states);
    	}
    }
    return $retSet;
} # IsIncludedFirst


sub First {
    my $self = shift;
    my $retSet = Set->new;
    foreach ( values %$self) {
	next unless (ref($_) eq "Pair");
	$retSet->Push($_->First);
    }
    return $retSet;
} # First

sub Second{
    my $self = shift;
    my $retSet = Set->new;
    foreach ( values %$self) {
	next unless (ref($_) eq "Pair");
	$retSet->Push($_->Second);
    }
    return $retSet;
} # Second

sub ReplaceSecond {
    my ($self, $p, $q) = @_;
    foreach (values %$self) {
	next unless $_->Second eq $p;
	$self->Delete($_);
	$self->Push(Pair->new($_->First, $q));
    }
} # ReplaceSecond

sub FindSecond {
    my ($self,$state) = @_;
    foreach ( values %$self) {
	if ($state->IsEqual($_->Second)) {
	    return $_;
	}
    }
    return undef;
}
1;
