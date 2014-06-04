# $Id: UniqSet.pm,v 1.1 2006/06/23 12:01:26 bjobst Exp $

######################################################################
#
# Creates unique sets of objects if the objects are identified by ref.
#
#
# Author: Barbara Jobstmann
#
######################################################################
package UniqSet;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK %cache);
@ISA       = qw(Exporter);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
use Set;
use LTL2AUT;
use Pair;
use Cover;
use strict;

sub new {
    my $class = shift;
    my $new = Set->new(@_);
    my $key = computeKey($new);
    unless (exists $cache{$key}) {
	bless $new, $class;
	$cache{$key} = $new;
    }
    return $cache{$key};
}

sub newFromSet {
    my ($class, $set) = @_;
    my $key = computeKey($set);
    unless (exists $cache{key}) {
	my $new = Set::Clone($set);
	bless $new, $class;
	$cache{$key} = $new;
    }
    return $cache{$key};
}

sub computeKey {
    my $set = shift;
    my @keylst = (keys %$set);
    @keylst = sort @keylst;
    my $key = join(",",@keylst);
    return $key;
}

# sub Push {
#     my ($self, $elem) = @_;
#     return $self if (defined $$self{$elem});
#     my $new = Set::Clone($self);
#     Set::Push($new, $elem);
#     $new = UniqSet->newFromSet($new);
#     return $new;
# }

sub IsEqual {
    my ($self, $other) = @_;
    if ($self eq $other) {
	return 1;
    }
    return "";
}

sub Size {
    return Set::Size(@_);
}

sub ToString {
    return Set::ToString(@_);
}

sub IsIncluded {
    return Set::IsIncluded(@_);
}

sub IsMember {
    return Set::IsMember(@_);
}

sub IsDisjoint {
    return Set::IsDisjoint(@_);
}

#Union: used in CoBuechiTree
sub Union {
    my ($self, $other) = @_;
    my $new = Set::Union($self,$other);
    $new = UniqSet->newFromSet($new);
    return $new;
}

# sub Delete {
#     my ($self, $elem) = @_;
#     return $self unless (defined $$self{$elem});

#     my $new = Set::Clone($self);
#     delete($$new{$elem});
#     $new = UniqSet->newFromSet($new);
#     return $new;
# }


sub Set {
    my $self = shift;
    my $new = Set->new;
    foreach (values %$self) {
	$new->Push($_);
    }
    return $new;
}

sub Difference {
    return Set::Difference(@_);
}

sub Pick {
    return Set::Pick(@_);
}
