#$Id: CoBuechi.pm,v 1.2 2005/09/26 11:44:23 bjobst Exp $

################################################################
# Functions to create and manipulate Co-Buechi automata.
#
# Author: Sankar Gurumurthy <gurumurt@Colorado.edu>
#
################################################################

package CoBuechi;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK $nameIndex $DEBUG);
@ISA       = qw(Exporter Buechi);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
$DEBUG = 0;
use strict;
use Set;
use Cover;
use Pair;


######################################################################
# Construct a new automaton.
######################################################################
sub new {
    my $class = shift;
    my %params = @_;
    # If either a file handle or a string is given, it is assumed to
    # contain the description of an automaton in the format produced
    # by ToString.  The automaton is built from this description, and
    # the remaining parameters are ignored.
    if (defined $params{file}) {
	return FromString(file => $params{file});
    } elsif (defined $params{string}) {
	return FromString(string => $params{string});
    }
    # Read parameters and supply default values as needed.
    $params{states} = Set->new unless defined($params{states});
    $params{init} = Set->new unless defined($params{init});
    $params{delta} = {} unless defined($params{delta});
    $params{fair} = Set->new unless defined($params{fair});
    $params{names} = AddNames($params{states}) unless defined($params{names});
    # Build the automaton.
    my $self = {
		states    => $params{states},
		init      => $params{init},
		delta     => $params{delta},
		fair      => $params{fair},
		names     => $params{names},
	       };
    return bless $self, $class;

} # new



################################################################
# Convert the input Buechi automata with labels on arcs to
#              Co-Buechi universal automata.
################################################################
sub fromBuechi{
    my ($class,$buechiAL) = @_;
    my $bstates = $$buechiAL{states};
    my $binit = $$buechiAL{init};
    my $bdelta = $$buechiAL{delta};
    my $blabels = $$buechiAL{labels};
    my $bfair = $$buechiAL{fair};
    my $bnames = $$buechiAL{names};
    my $states = $bstates->Clone;
    my $fair = $bfair->Clone;
    my $init = $binit->Clone;
    my $names = $$buechiAL{names};
    my %delta = ();
#    my %names = ();
#    my $states = Set->new;
#    my $fair = Set->new;
#    my $init = Set->new;
    my $letters = $buechiAL->Letters($bstates);
    #print $letters->ToString," ",ref($letters->Pick->Pick),"\n";
    foreach my $cbstate (values %$states) {
	#my $cbstate = $bstate->Clone;
	#$states->Push($cbstate);
	my $bimage = $$bdelta{$cbstate};
	my $cbimage = Set->new;
	my $comp = Cover->new;
	foreach my $label (values %$letters) {
	    my $destset = Set->new;
	    foreach my $blpair (values %$bimage) {
		if ($blpair->First->IsIncluded($label)) {
		    $destset->Push($blpair->Second);
		}
	    }
	    $cbimage->Push(Pair->new($label,$destset)) if $destset->Size > 0;
	    $comp->Push($label) if $destset->Size == 0;
	}
	my %toLabels = ();
	my $destinations = Set->new;
	foreach my $pair (values %{$cbimage}) {
	    my $label = $pair->First;
	    my $dest = $pair->Second;
	    unless (defined $toLabels{$dest}) {
		$toLabels{$dest} = Cover->new;
	    }
	    $toLabels{$dest}->Push($label);
	    $destinations->Push($dest);
	}
	my $newimage = Set->new;
	foreach my $dest (values %{$destinations}) {
	   # print $toLabels{$dest}->ToString,"\n";
	    my $picover = $toLabels{$dest}->PrimeAndIrredundant;
	    #print $$bnames{$bstate}, " - ",  $picover->ToString, " -> ",
	     # $dest->ToString, "\n"; # diag
	    foreach my $label (values %{$picover}) {
		$newimage->Push(Pair->new($label,$dest));
	    }
	}
	my $rcomp = $comp->PrimeAndIrredundant;
#	print $comp->ToString,"    ",$rcomp->ToString,"\n";
# 	print "here\n";
 	foreach my $clabel (values %{$rcomp}) {
 	    $newimage->Push(Pair->new($clabel,Set->new));
 	}
	#$cbimage->Push(Pair->new($rcomp,Set->new));
	$delta{$cbstate}= $newimage;
	# if ($bfair->Pick->IsMember($bstate)) {
# 	    $fair->Push($cbstate);
# 	}
# 	if ($binit->IsMember($bstate)) {
# 	    $init->Push($cbstate);
# 	}
# 	$names{$cbstate} = $$bnames{$bstate};
	#print $$names{$cbstate}," -> ",$cbimage->ToString,"\n";
    }
    #my $completedelta = makecomplete(\%delta,$states);
    my $self = {
		states => $states,
		init      => $init,
		delta     => \%delta,
		names    => $names,
		fair      => $fair,
	       };
    return bless $self, $class;
} # new

######################################################################
# Picks the label of maximum size
#####################################################################
sub maxpick{
    my $set = shift;
    my $ret = Pair->new(Set->new,Set->new);
    my $max = 0;
    foreach my $element (values %{$set}) {
	if ($element->First->Size >= $max) {
	    $ret = $element;
	    $max = $element->First->Size;
       	}
    }
    return $ret;
} # maxpick

######################################################################
# Converts a string into an automaton.
# The string must use the format produced by ToString.
######################################################################
sub FromString {
    my %params = @_;
    my $string;
    # The input can be either a string or a file handle.  In the former
    # case, the string is the entire automaton.  In the latter case,
    # the automaton is read as a single string from the file.
    if (defined $params{file}) {
	# Read the entire file into a single string.
	my $handle = $params{file};
	my $oldfh = select $handle;
	undef $/;
	select $oldfh;
	$string = <$handle>;
    } elsif (defined $params{string}) {
	$string = $params{string}
    } else {
	die "Specify either a file handle or a string";
    }
    # Initialize automaton components.
    my $states = Set->new;
    my $init = Set->new;
    my %delta = ();
    my %names = ();
    my %statemap = ();
    my $fair = Set->new;
    # my $count = 0;

    # The parser is an automaton with states "start," "states,"
    # "arcs," fair," and "end."
    my $state = "start";
    while (defined $string) {
	# Peel a line off the string and remove the trailing newline.
	my $line;
	($line,$string) = split(/^/m, $string, 2);
	# print $count++, ": ", $line;
	chop $line;
	# Remove comments and trailing spaces, and skip empty lines.
	$line =~ s/\s*\#.*//;
	$line =~ s/\s+$//;
	next if $line eq "";
	# Branch on the current state.
	if ($state eq "start") {
	    if ($line eq "States") {
		$state = "states";
	    } else {
		die "description must start with \"States\"";
	    }
	} elsif ($state eq "states") {
	    if ($line eq "Arcs") {
		$state = "arcs";
	    } else {
		unless ($line =~ s/^([\w<>\[\]\,]+):\s*//) {
		    die "missing state name";
		}
		my $name = $1;
		my $state = Buechi::BuildState($line);
		$statemap{$name} = $state;
		$names{$state} = $name;
		$states->Push($state);
		# print "State: ", $name, ": ", $state->ToString, "\n";
	    }
	} elsif ($state eq "arcs") {
	    if ($line eq "Fair Sets") {
		$state = "fair";
	    } else {
		my $initflag = 0;
		if ($line =~ s/^->//) {
		    $initflag = 1;
		}
		unless ($line =~ s/^\s*([\w<>\[\]\,]+)\s*->\s*//) {
		    die "missing state name";
		}
		my $name = $1;
		unless ($line =~ s/^{//) {
		    die "missing left brace";
		}
		unless ($line =~ s/}$//) {
		    die "missing right brace";
		}
		my @successors = SplitTransitionList($line);
		my $img = Set->new;
		foreach my $succ (@successors) {
		    unless ($succ =~ s/^\[//) {
			die "missing left bracket";
		    }
		    unless ($succ =~ s/\]$//) {
			die "missing right bracket";
		    }
		    unless ($succ =~ s/,([\w<>\[\]\{\},]+)$//) {
			die "missing succesor list";
		    }
		    my $succlist = $1;
		    my $label = Buechi::BuildState($succ);
		    unless ($succlist =~ s/^{//) {
			die "missing left brace in transition list";
		    }
		    unless ($succlist =~ s/}$//) {
			die "missing right brace in transition list";
		    }
		    my @successornames = SplitTransitionList($succlist);
		    my $succset = Set->new;
		    foreach my $succname (@successornames) {
			my $sstate = $statemap{$succname};
			$succset->Push($sstate);
		    }
		    $img->Push(Pair->new($label,$succset));
		}
		my $state = $statemap{$name};
		$delta{$state} = $img;
		$init->Push($state) if $initflag;
	    }
	} elsif ($state eq "fair") {
	    if ($line eq "End") {
		$state = "end";
	    } else {
		unless ($line =~ s/^{//) {
		    die "missing left brace";
		}
		unless ($line =~ s/}$//) {
		    die "missing right brace";
		}
		my @fairstates = Buechi::SplitStateList($line);
		my $fairset = Set->new;
		foreach my $fairs (@fairstates) {
		    my $fstate = $statemap{$fairs};
		    $fairset->Push($fstate);
		}
		$fair->Push($fairset);
	    }
	} else {
	    die "spurious trailing characters";
	}
    }
    my $self = CoBuechi->new(
			   states => $states,
			   init   => $init,
			   delta  => \%delta,
			   names  => \%names,
			   fair   => $fair);
    # print $self->ToString;
    return $self;

} # FromString

######################################################################
# Split a comma-separated list of transtions into a list.  The state
# names may also contain commas as in [a,[b,c]].  Hence we count the
# left brackets and the commas to know when a name finishes.
######################################################################
sub SplitTransitionList {
    my $string = shift;
    my @list = ();
    while ($string ne "") {
	my $leftbrackets = 0;
	my $commas = 0;
	my $openbraces = 0;
	my $i;
	for ($i = 0; $i < length($string); $i++) {
	    my $first = substr($string,$i,1);
	    if ($first eq "[") {
		$leftbrackets++;
	    } elsif ($first eq "{") {
		$openbraces++;
	    } elsif ($first eq "}") {
		$openbraces--;
	    } elsif ($openbraces == 0 and $first eq ",") {
		$commas++;
		last if $commas > $leftbrackets;
	    }
	}
	push(@list,substr($string,0,$i));
	if ($i < length($string)) {
	    $string = substr($string,$i+1);
	} else {
	    $string = "";
	}
    }
    return @list;

} # SplitTransitionList

######################################################################
# Returns the labels of the transition to 'TRUE' which are needed
# to make the transition relation of the Co-Buechi automaton complete
######################################################################
sub makecomplete {
    my ($delta,$states) = @_;
#    my $bimagenew = $bimage->Clone;
    my %compdelta = ();
    foreach my $state (values %{$states}) {
	my $image = $$delta{$state}->Clone;
	my $labelCover = Cover->new;
	foreach my $labeledpair (values %{$image}) {
	    $labelCover->Push($labeledpair->First);
	}
	my $reducedCover = $labelCover->PrimeAndIrredundant;
	#print $reducedCover->ToString," reduced\n";
	my $comp = complement($reducedCover);
	foreach my $label (values %{$comp}) {
	    $image->Push(Pair->new($label,Set->new))
	}
	$compdelta{$state}=$image
    }
   
    # foreach my $label (values %{$comp}) {
# 	$bimagenew->Push(Pair->new($label,Set->new));
#     }
       return \%compdelta;
}

######################################################################
# To find the complement of a cover
######################################################################
sub complement {
    my $cover = shift;
    my $cnfset = Set->new;
    foreach my $labelset (values %{$cover}) {
	if ($labelset->Size ==  0) {
	    return Cover->new;
	}
	my $sopterm = Set->new;
	foreach my $label (values %{$labelset}) {
	    my $value = $label->Value;
	    if ($value =~ /=1/) {
	       $value =~ s/=1/=0/;
	   }
	   else {
	       $value =~ s/=0/=1/;
	   }
	   my $newltl = LTL->new($value);
	   my $newlabel = Set->new($newltl);
	   $sopterm->Push($newlabel);
	}
	$cnfset->Push($sopterm);
    }
    my $retCover = Cover->new;
    my $satset = Set->new;
    my $flag = 1;
    foreach my $sopterm (values %{$cnfset}) {
	if ($flag) {
	    $satset = $sopterm;
	}
	else {
	    $satset = expproduct($satset,$sopterm)
	}
    }
    foreach my $newls (values %{$satset}) {
	$retCover->Push($newls);
    }
    return $retCover;
}

#####################################################################
# To compute the product of two sets
#####################################################################
sub expproduct{
    my ($first,$second) = @_;
    if ($first->Size == 0) {
	return $first;
    }
    if ($second->Size == 0) {
	return $second;
    }
    my $retset = Set->new;
    foreach my $sset (values %{$second}) {
	foreach my $fset (values %{$first}) {
	    $retset->Push($fset->Union($sset));
	}
    }
    return $retset;
} #expproduct

##################################################################
# To Check if a TRUE transiton exists
#################################################################
sub TrueTranExists{
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    foreach my $state (values %{$states}) {
	my $image = $$delta{$state};
	foreach my $lpair (values %{$image}) {
	    if ($lpair->Second->Size ==0 ) {
		return 1;
	    }
	}
    }
    return "";
}
1;

