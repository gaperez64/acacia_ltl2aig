# $Id: Alternating.pm,v 1.2 2005/09/26 11:44:23 bjobst Exp $

######################################################################
# Functions to create and manipulate Alternating automata.
#
# Author: Fabio Somenzi <Fabio@Colorado.EDU>
#         Sankar Gurumurthy <gurumurt@Colorado.EDU>
#
######################################################################
package Alternating;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK $nameIndex $DEBUG);
@ISA       = qw(Exporter CoBuechi);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
$DEBUG = 0;
use strict;
use Set;
use Cover;
use Pair;
use BuechiAL;
use AAemptiness;

# Remove all #*'s if you progress indicator

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

sub fromBuechi{
    my ($class,$cobuechi,$weak,%params) = @_;
    my $cbstates = $$cobuechi{states};
    my $cbinit = $$cobuechi{init};
    my $cbdelta = $$cobuechi{delta};
    my $cbfair = $$cobuechi{fair};
    my $cbnames = $$cobuechi{names};
    my $n = $cbstates->Size;
    my $alpha = $cbfair->Pick->Size;
    my $i=1;
    my $init = Set->new;
    my $unexpanded = Set->new;
    my $states = Set->new;
    my %delta = ();
    my %names = ();
    my $fair = Set->new;
    my $finalfair = Set->new;
    my %new = ();
    my $self = \%new;
    my $max= (2 * $n) +1;
    my $WAA2n;
    if (defined $params{WAA2n}) {
	$WAA2n = $params{WAA2n};
	# open(FP,">WAA2n.dot");
# 	print FP $WAA2n->ToDot("WAA2n");
# 	close(FP);
    }
    else {
	$WAA2n = undef;
    }
    if (!$weak) {
	while ($i<= ($n-$alpha)) {
	    # print "$i\n";
	    my $newstate = Pair->new($cbinit->Pick,2*$i);
	    $states->Push($newstate);
	    $unexpanded->Push($newstate);
	    $init->Push($newstate);
	    Create2layers($cobuechi,$states,\%delta,\%names,$unexpanded,$fair);
	    $finalfair->Push($fair);
	    $self = {
			states => $states,
			init   => $init,
			delta  => \%delta,
			names  => \%names,
			fair   => $finalfair,
		       };
	    #$check->MergeTransitions;
	    $i++;
	    next unless (defined $WAA2n);
	    my $check = Alternating->CompDualaltbuechi($self);
	    #print "This is the composition of CoBuechi automaton with",
	     # "alternating automaton at ",2*($i-1)," layers \n";
	    #print $check->ToString,"\n";
	    $check->MergeTransitions;
	    # print $check->ToDot("checkb4");
# 	    print $check->ToString,"\n";
#	    $check->DirectSimulationMinimization;
	#    print $check->ToDot("checkafter");
	    #print $coalt->ToString,"\n";
	    my $bl = $check->ToBuechi(nocons => 1);
	    #$bl->MergeTransitions;
	   #  open(FP,">bl$i.dot");
# 	    print FP $bl->ToDot("bl$i");
# 	    close(FP);
	    #print $bl->ToDot("bl");
	    #print $WAA2n->ToDot("waa");
	    last if $bl->IsIntersectionEmpty($WAA2n);
	    if ($i > ($n-$alpha)) {
		print "2* $n - $alpha layer notempty\n";
	    }
	}
    }
    else {
	foreach my $bstate (values %{$cbstates}) {
	    my $newstate = Pair->new($bstate,1);
	    $states->Push($newstate);
	    foreach my $fairset (values %{$cbfair}) {
		if (not($fairset->IsMember($bstate))) {
		    $fair->Push($newstate);
		}
	    }
	    my $bimageset = $$cbdelta{$bstate};
	    my $newimageset = Set->new;
	    foreach my $labeledpair (values %{$bimageset}) {
		my $slabel = $labeledpair->First;
		my $dest = $labeledpair->Second;
		my $newimagestateset = Set->new;
		foreach my $destelement (values %{$dest}) {
		    $newimagestateset->Push(Pair->new($destelement,1));
		}
		my $newdest = Set->new($newimagestateset);
		$newimageset->Push(Pair->new($slabel,$newdest));
	    }
	    $init->Push($newstate) if $cbinit->IsMember($bstate);
	    $delta{$newstate}=$newimageset;
	    $names{$newstate}=$$cbnames{$bstate}."_1";
	}
	$finalfair->Push($fair);
	$self = {
		     states => $states,
		     init   => $init,
		     delta  => \%delta,
		     names  => \%names,
		     fair   => $finalfair,
		    };
    }
    if ($$self{init}->Size > 1) {
	my $max = 0;
	my $left ;
	foreach my $st (values %{$$self{init}}) {
	    if ($st->Second > $max) {
		$max = $st->Second;
		$left = Set->new($st);
	    }
	}
	$$self{init}->Restrict($left);
    }
    return bless $self, $class;
}

################################################################
# Convert the input Co-Buechi automata with labels on arcs to
#              alternating automata.
################################################################

sub Create2layers{
    my ($cobuechi,$states,$delta,$names,$unexpanded,$fair) = @_;
    my $cbstates = $$cobuechi{states};
    my $cbinit = $$cobuechi{init};
    my $cbdelta = $$cobuechi{delta};
    my $cbfair = $$cobuechi{fair};
    my $cbnames = $$cobuechi{names};
    my $trex = $cobuechi->TrueTranExists;
    #my $states = Set->new;
    #my $fair = Set->new;
    #my $finalfair = Set->new;
    #my $init = Set->new;
    #my %delta = ();
    #my %names = ();
    my $n = $cbstates->Size;
    #my $initialstate = Pair->new($cbinit->Pick,2*$n);
    #$init->Push($initialstate);
    #$states->Push($initialstate);
    #my $unexpanded = $states->Clone;
    #my $unexpanded = Set->new(Pair->new($cbinit->Pick,2));
    #my $states = $unexpanded->Clone;
    while ($unexpanded->Size > 0) {
	my $weakstate = $unexpanded->Pop;
	my $index = $weakstate->Second;
	my $state = $weakstate->First;
	my $cbimage = $$cbdelta{$state};
	my $image = Set->new;
	if (not(($cbfair->Pick)->IsMember($state)) || (($index % 2) == 0)) {
	    foreach my $labelpair (values %{$cbimage}) {
		my $label = $labelpair->First;
		my $destset = $labelpair->Second;
		my $newdestset = Set->new;
		my $Pickedset = Set->new;
		my $interset = Set->new;
		my $setsize = $destset->Size;
		if ($setsize == 0) {
		    $newdestset->Push(Set->new);
		}
		else {
		    $newdestset = release($destset,$index,$trex);
		}
		my $new = Set->new;
		foreach my $stateset (values %{$newdestset}) {
		    $new->Add($stateset->Difference($states));
		}
		$unexpanded->Add($new);
		$states->Add($new);
		$image->Push(Pair->new($label,$newdestset));
	    }
	    if (($index % 2) != 0) {
		$fair->Push($weakstate);
	    }
	}
	$$delta{$weakstate} = $image;
	$$names{$weakstate} = $$cbnames{$state}."_$index";
    }
    # Some cleanup
    while (1) {
	my $remove = Set->new;
	foreach my $state (values %{$states}) {
	   # my $index = $state->Second;
	    #if ($index % 2 == 1) {
		#foreach my $fairset (values %{$cbfair}) {
		 #   if ($fairset->IsMember($state->First)) {
			#$remove->Push($state);
		  #  }
	#	}
	 #   }
	    if ($$delta{$state}->Size ==0) {
		$remove->Push($state);
	    }
	}
	last unless ($remove->Size > 0);
	foreach my $state (values %{$states}) {
	    my $image = $$delta{$state};
	    my $newimage = Set->new;
	    foreach my $lpair (values %{$image}) {
		my $destset = $lpair->Second;
		my $removalset = Set->new;
		foreach my $stateset (values %{$destset}) {
		    if (($stateset->Intersection($remove))->Size != 0 ) {
			$removalset->Push($stateset);
		    }
		}
		my $newdestset = $destset->Difference($removalset);
		if ($newdestset->Size > 0 ) {
		    $newimage->Push(Pair->new($lpair->First,$newdestset));
		}
	    }
	    $$delta{$state} = $newimage;
	}
	$states->Subtract($remove);
	foreach my $state (values %{$remove}) {
	    delete $$delta{$state};
	    delete $$names{$state};
	}
    }
} # Create2layers

sub Composealtcobuechi{
    my ($class,$self,$cobuechi,%params) = @_;
    my $astates = $$self{states};
    my $ainit = $$self{init};
    my $adelta = $$self{delta};
    my $afair = $$self{fair};
    my $anames = $$self{names};
    my $cbstates = $$cobuechi{states};
    my $cbinit = $$cobuechi{init};
    my $cbdelta = $$cobuechi{delta};
    my $cbfair = $$cobuechi{fair};
    my $cbnames = $$cobuechi{names};
    my $newcbst = Set->new;
    my %newdelta = ();
    my %newnames = ();
    my $incob;
    my $newcbfair = Set->new;
    my $li = 2 * ($cbstates->Size) +1;
    my $forbidden;
    if (defined $params{forbidden}) {
	$forbidden = $params{forbidden};
    } else {
	$forbidden = {};
    }
    foreach my $state (values %{$cbstates}) {
	my $newstate = Pair->new($state,$li);
	$newcbst->Push($newstate);
	my $oimage = $$cbdelta{$state};
	$newdelta{$newstate} = Set->new;
	foreach my $lpair (values %{$oimage}) {
	    my $label = $lpair->First;
	    my $destset = $lpair->Second;
	    my $newdestset = Set->new;
	    foreach my $succ (values %{$destset}) {
		$newdestset->Push(Pair->new($succ,$li));
	    }
	    $newdelta{$newstate}->Push(Pair->new($label,Set->new($newdestset)));
	}
	$newnames{$newstate}=$$cbnames{$state}."_$li";
	if ($cbinit->IsMember($state)) {
	    $incob = $newstate;
	}
	if ($cbfair->Pick->IsMember($state)) {
	    $newcbfair->Push($newstate);
	}
    }
    my $newafair = Set->new;
    foreach my $state (values %{$astates}) {
	#my $newstate = $state->Clone;
	#my $aimage = $$adelta{$state}->Clone;
	my $aimage = Set->new;
	foreach my $lpair (values %{$$adelta{$state}}) {
	    my $destset = $lpair->Second;
	    my $newdestset = Set->new;
	    if (defined $$forbidden{$state}) {
		$newdestset = $lpair->Second->Difference($$forbidden{$state});
		#print $state->ToString,"  ",$destset->ToString,"  ",$newdestset->ToString,"\n";
	    }
	    else {
		$newdestset = $lpair->Second;
	    }
	    $aimage->Push(Pair->new($lpair->First,$newdestset)) if $newdestset->Size > 0;
	}
	my $lcover = Cover->new;
	my $remset = Set->new;
	foreach my $lpair (values %{$aimage}) {
	    #next if $$forbidden{$state}->IsMember($lpair);
	    $lcover->Push($lpair->First);
	    my $setofstateset = $lpair->Second;
	    if ($setofstateset->Size == 1) {
		if ($setofstateset->Pick->Size == 0) {
		    $remset->Push($lpair);
		}
	    }
	}
	if ($lcover->Size > 0) {
	    my $reducedCover = $lcover->PrimeAndIrredundant;
	    my $comp = CoBuechi::complement($reducedCover);
	    #print "complement for state ",$state->ToString,"is ",$comp->ToString,"\n";
	    foreach my $label (values %{$comp}) {
		$aimage->Push(Pair->new($label,Set->new(Set->new)));
	    }
	}
	else {
	    $aimage->Push(Pair->new(Set->new,Set->new(Set->new)));
	}
	$aimage->Subtract($remset);
	#print "image b4 ",$aimage->ToString,"\n";
	my $newaimage = Set->new;
	foreach my $lpair (values %{$aimage}) {
	   # next if $$forbidden{$state}->IsMember($lpair);
	    my $label = $lpair->First;
	    my $destset = $lpair->Second;
	    my $newdest = Set->new;
	    my $flag = 1;
	    foreach my $succset (values %{$destset}) {
		#next if $$forbidden{$state}->IsMember($succset);
		if ($flag) {
		    $newdest = Decompose($succset);
		    $flag = 0;
		}
		else {
		    $newdest = expproduct(Decompose($succset),$newdest);
		}
	    }
	    my $red = Set->new;
	    foreach my $sset (values %$newdest) {
		foreach my $tset (values %$newdest) {
		    next if $sset eq $tset;
		    if ($sset->IsIncluded($tset)) {
			$red->Push($tset);
		    }
		}
	    }
	    $newdest->Subtract($red);
	    $newaimage->Push(Pair->new($label,$newdest));
	}
	#print "image after ",$newaimage->ToString,"\n";
	$newdelta{$state} = $newaimage;
	$newnames{$state} = $$anames{$state};
	$newcbst->Push($state);
	$newafair->Push($state) if ($afair->Pick->IsMember($state));
    }
    my $finalfair = Set->new($newcbfair->Union($newafair));
    #print $finalfair->ToString,"\n";
    #my $finalstates = $astates->Union($newcbst);
        #print "here1\n";
    my $newinitialstate = Pair->new(Set->new,0);
    my $init = Set->new($newinitialstate);
    my $inlabel = Set->new();
    #print "here2\n";
    my $i = 0;
    my $inalt;
    foreach my $ainitstate (values %{$ainit}) {
	if ($ainitstate->Second > $i) {
	    $i = $ainitstate->Second;
	    $inalt = $ainitstate;
	}
    }
    $newdelta{$newinitialstate} = Set->new(Pair->new($inlabel,Set->new(Set->new($inalt,$incob))));
    $newnames{$newinitialstate} = "init";
    $newcbst->Push($newinitialstate);
    my $coalt = {
		     states => $newcbst,
		     init   => $init,
		     delta  => \%newdelta,
		     names  => \%newnames,
		     fair   => $finalfair,
		    };
    return bless $coalt, $class;
}

sub CompDualaltbuechi{
    my ($class,$self,%params) = @_;
    my $astates = $$self{states};
    my $ainit = $$self{init};
    my $adelta = $$self{delta};
    my $afair = $$self{fair};
    my $anames = $$self{names};
    my %newdelta = ();
    my %newnames = ();
    #my $incob;
    my $forbidden;
    if (defined $params{forbidden}) {
	$forbidden = $params{forbidden};
    } else {
	$forbidden = {};
    }
    my $newafair = Set->new;
    my $states = Set->new;
    foreach my $state (values %{$astates}) {
	#my $newstate = $state->Clone;
	#my $aimage = $$adelta{$state}->Clone;
	my $aimage = Set->new;
	# Prune forbidden transitions.
	foreach my $lpair (values %{$$adelta{$state}}) {
	    my $destset = $lpair->Second;
	    my $newdestset = Set->new;
	    if (exists $$forbidden{$state}) {
		$newdestset = $lpair->Second->Difference($$forbidden{$state});
#		print $state->ToString,"  ",$destset->ToString,"  ",$newdestset->ToString,"\n";
	    }
	    else {
		$newdestset = $lpair->Second;
	    }
	    $aimage->Push(Pair->new($lpair->First,$newdestset)) if $newdestset->Size > 0;
	}
	# Find labels of false arcs as well as all labels.
	my $lcover = Cover->new;
	my $remset = Set->new;
	foreach my $lpair (values %{$aimage}) {
	    #next if $$forbidden{$state}->IsMember($lpair);
	    $lcover->Push($lpair->First);
	    my $setofstateset = $lpair->Second;
	    if ($setofstateset->Size == 1) {
		if ($setofstateset->Pick->Size == 0) {
		    $remset->Push($lpair);
		}
	    }
	}
	if ($lcover->Size > 0) {
	    # Remove true transitions.
	    $aimage->Subtract($remset);
	    my $reducedCover = $lcover->PrimeAndIrredundant;
	    my $comp = CoBuechi::complement($reducedCover);
	    #print "complement for state ",$state->ToString,"is ",$comp->ToString,"\n";
	    foreach my $label (values %{$comp}) {
		$aimage->Push(Pair->new($label,Set->new(Set->new)));
	    }
	}
	else {
	    $aimage->Push(Pair->new(Set->new,Set->new(Set->new)));
	}
	#print "image b4 ",$aimage->ToString,"\n";
	my $newaimage = Set->new;
	foreach my $lpair (values %{$aimage}) {
	   # next if $$forbidden{$state}->IsMember($lpair);
	    my $label = $lpair->First;
	    my $destset = $lpair->Second;
	    my $newdest = Set->new;
	    my $flag = 1;
	    foreach my $succset (values %{$destset}) {
		#next if $$forbidden{$state}->IsMember($succset);
		if ($flag) {
		    $newdest = Decompose($succset);
		    $flag = 0;
		}
		else {
		    $newdest = expproduct(Decompose($succset),$newdest);
		}
	    }
	    my $red = Set->new;
	    foreach my $sset (values %$newdest) {
		foreach my $tset (values %$newdest) {
		    next if $sset eq $tset;
		    if ($sset->IsIncluded($tset)) {
			$red->Push($tset);
		    }
		}
	    }
	    $newdest->Subtract($red);
	    $newaimage->Push(Pair->new($label,$newdest));
	}
	#print "image after ",$newaimage->ToString,"\n";
	$newdelta{$state} = $newaimage;
	$newnames{$state} = $$anames{$state};
	$states->Push($state);
	$newafair->Push($state) unless ($afair->Pick->IsMember($state));
    }
    my $finalfair = Set->new($newafair);
    #print $finalfair->ToString,"\n";
    #my $finalstates = $astates->Union($newcbst);
        #print "here1\n";
    #my $newinitialstate = Pair->new(Set->new,0);
    my $init = $ainit->Clone;
    my $codualt = {
		     states => $states,
		     init   => $init,
		     delta  => \%newdelta,
		     names  => \%newnames,
		     fair   => $finalfair,
		    };
    return bless $codualt, $class;
}

###########################################################################
# To derive the Buechi automaton from the weak alternating automaton using
#               Miyano and Hayashi procedure.
###########################################################################
sub ToBuechi{
    my ($self,%params) = @_;
    my $astates = $$self{states};
    my $ainit = $$self{init};
    my $adelta = $$self{delta};
    my $afair = $$self{fair};
    my $anames = $$self{names};
    my %delta = ();
    my %names = ();
    my %mem =();
    my %num = ();
    my $i=0;
    my $sum=0;
    my $states = Set->new;
    my $unexpanded = Set->new;
    my $fair = Set->new;
    my $nocons;
    if (defined $params{nocons}) {
	$nocons = $params{nocons};
    }
    else {
	$nocons = undef;
    }
    foreach my $astate (values %{$astates}) {
	$num{$astate} = $i;
	$i++;
    }
   # my $letters = $self->Letters($astates);
    my $initialstate = Pair->new($ainit,Set->new);
    $initialstate =  hashing($initialstate,$states,
					  $unexpanded,\%mem,\%num,$anames);
    my $init = Set->new($initialstate);
    #$states->Push($initialstate);
    #print "Alternating automaton has ",$astates->Size," states\n";
    #$unexpanded->Push($initialstate);
    my $f=1;
    while ($unexpanded->Size != 0) {
	my $start = times();
	my $state = $unexpanded->Pop;
	#;;print "Ananlyzing ",$state->ToString,"\n";
	my $stateset = $state->First;
	my $obligation = $state->Second;
	my $oflag = $obligation->Size == 0;
	my $image = Set->new;
	my $letters = $self->Letters($stateset);
	#print "next state: ",$stateset->ToString," ",$obligation->ToString,"\n";
      LLOOP:foreach my $label (values %$letters) {
	    #;;print "Label : ",$label->ToString,"\n";
	    my $dsatset = Set->new(Set->new);
	    my $dsflag = 1;
	    my $osflag = 1;
	    # my $eflag = 0;
	    my $osatset = Set->new(Set->new);
	    foreach my $astate (values %$stateset) {
		my $flag = $obligation->IsMember($astate);
		my $eflag2 = 0;
		my $dsattemp = Set->new;
		my $osattemp = Set->new;
		#print $astate->ToString,"  ",$flag,"\n";
		foreach my $lpair (values %{$$adelta{$astate}}) {
		    next unless $lpair->First->IsIncluded($label);
		    # $eflag = 1;
		    $eflag2 =1;
		    $dsattemp->Add($lpair->Second);
		    if ($flag) {
			$osattemp->Add($lpair->Second);
		#	print "osat: ",$osattemp->ToString,"\n";
		    }
		}
		#print $eflag2,"\n";
		next LLOOP unless $eflag2;
		if ($dsflag) {
		    $dsatset = $dsattemp->Clone;
		    $dsflag =0;
		}
		else {
		    $dsatset = expproduct($dsatset,$dsattemp);
		}
		if ($flag) {
		    if ($osflag) {
			$osatset = $osattemp->Clone;
			#print "o: ",$osatset->ToString
			$osflag =0;
		    }
		    else {
			$osatset = expproduct($osatset,$osattemp);
		    }
		}
	    }
	    #print $label->ToString," ",$dsatset->ToString," ",$osatset->ToString,"\n";
	    # next LLOOP unless $eflag;
	    # Remove redundant state sets
	   #;; print "Check 1: ",$dsatset->ToString,"  ",$osatset->ToString,"\n";
	    my $removals = Set->new;
	    # foreach my $sset (values %$dsatset) {
# 		next if $removals->IsMember($sset);
# 		foreach my $otherset (values %$dsatset) {
# 		    next if $sset eq $otherset;
# 		    if ($sset->IsIncluded($otherset)) {
# 			$removals->Push($otherset);
# 		    }
# 		}
# 	    }
# 	    $dsatset->Subtract($removals);
# 	    $removals = Set->new;
 	    foreach my $sset (values %$osatset) {
		next if $removals->IsMember($sset);
		foreach my $otherset (values %$osatset) {
		    next if $sset eq $otherset;
		    if ($sset->IsIncluded($otherset)) {
			$removals->Push($otherset);
		    }
		}
	    }
	    $osatset->Subtract($removals);
	    $removals = Set->new;
	    # Create True trap state if necessary
	    #;;print "Check 2: ",$dsatset->ToString,"  ",$osatset->ToString,"\n";
	    my $trueset = 0;
	    foreach my $dset (values %$dsatset) {
		if ($dset->Size == 0) {
		    $trueset = 1;
		}
	    }
	    if ($trueset) {
		my $newstate = Pair->new(Set->new,Set->new);
		$newstate = hashing($newstate,$states,$unexpanded,\%mem,\%num,$anames);
		$states->Push($newstate);
		$unexpanded->Delete($newstate);
		$delta{$newstate}=Set->new(Pair->new(Set->new,$newstate));
		$names{$newstate} = "fairstate".$f;
		$f++;
		$image->Push(Pair->new($label,$newstate));
		next LLOOP;
	    }
	    # Check consistency.  Not done on obligations because an
	    # inconsistent set of states cannot be a subset of a consistent
	    # one.
	   #;; print "Check 3: ",$dsatset->ToString,"  ",$osatset->ToString,"\n";
	    unless (defined $nocons) {
		foreach my $sset (values %$dsatset) {
		    foreach my $st (values %$sset) {
			foreach my $st2 (values %$sset) {
			    next if $st eq $st2;
			    if (($st->First) eq ($st2->First)) {
				#print $sset->ToString,"\n";
				$removals->Push($sset);
			    }
			}
		    }
		}
		$dsatset->Subtract($removals);
		$removals = Set->new;
	    }
	    #;;print "Check 4: ",$dsatset->ToString,"  ",$osatset->ToString,"\n";
	   # print $label->ToString," ,",$stateset->ToString," ,",$obligation->ToString," ,",$dsatset->ToString," ,",$osatset->ToString,"\n";
	    if ($oflag) {
		# Empty obligation.
		foreach my $sset (values %$dsatset){
		    my $newstate = Pair->new($sset,$sset->Difference($afair->Pick));
		    $newstate = hashing($newstate,$states,$unexpanded,\%mem,\%num,$anames);
		#;;    print "Newstate ",$newstate->ToString,"\n";
		    $image->Push(Pair->new($label,$newstate));
		}
	    }
	    else {
		my $newstates = Set->new;
	      OLOOP:foreach my $sset (values %$dsatset) {
		    #my $oset = Set->new;
		    if ($osatset->Pick->Size == 0) {
			my $newstate = Pair->new($sset,$osatset->Pick);
			$newstates->Push($newstate);
			#$newstate = hashing($newstate,$states,$unexpanded,\%mem,\%num,$anames);
			#;;print "Newstate ",$newstate->ToString,"\n";
			#$image->Push(Pair->new($label,$newstate));
			next OLOOP;
		    }
		    my $dflag = 1;
		    foreach my $oset (values %$osatset) {
			next unless $oset->IsIncluded($sset);
			my $newstate = Pair->new($sset,$oset->Difference($afair->Pick));
			$newstates->Push($newstate);
			$dflag = 0;
			#$newstate = hashing($newstate,$states,$unexpanded,\%mem,\%num,$anames);
			#;;print "Newstate ",$newstate->ToString,"\n";
			#$image->Push(Pair->new($label,$newstate));
		    }
		    die "Obligation set not found for stateset ", $sset->ToString," ",$osatset->ToString, "\n"if $dflag;
		}
		$removals = Set->new;
	      SPLOOP:foreach my $spair (values %$newstates) {
		    foreach my $opair (values %$newstates) {
			next if $spair eq $opair;
			if (($opair->First->IsIncluded($spair->First)) &&
			    ($opair->Second->IsIncluded($spair->Second))) {
			    $removals->Push($spair);
			    next SPLOOP;
			}
		    }
		}
		$newstates->Subtract($removals);
		foreach my $newstate (values %$newstates) {
		    $newstate = hashing($newstate,$states,$unexpanded,\%mem,\%num,$anames);
		    $image->Push(Pair->new($label,$newstate));
		}
	    }
	}
	# $delta{$state} = firstprune($image);
	$delta{$state} = $image;
	my $namst = "";
	foreach my $astate (values %$stateset) {
	    $namst .= $$anames{$astate};
	}
	foreach my $astate (values %$obligation) {
	    $namst .= $$anames{$astate};
	}
	if ($namst eq "") {
	    $namst = "fairstate".$f;
	    $f++;
	}
	$names{$state} = $namst;
	my $end = times();
	#*printf "this state manipulation consumed %.3f secs \n", $end - $start;
    }
    #print "original arcs ",$sum,"\n";
    my $fairset = Set->new;
    foreach my $state (values %{$states}) {
	if ($state->Second->Size == 0) {
	    $fairset->Push($state);
	}
	#print $delta{$state}->ToString,"\n";
    }
    $fair->Push($fairset);
    # Second round of pruning
    #print $states->ToString,"  ",$states->Size,"\n";
    #print $init->Pick->ToString;
#     $unexpanded->Push($init->Pick);
#     my $remain = Set->new($init->Pick);
#     #print $delta{$unexpanded->Pick}->ToString,"\n";
#     while ($unexpanded->Size > 0) {
# 	my $state = $unexpanded->Pop;
# 	my $image = $delta{$state};
# 	foreach my $lpair (values %{$image}) {
# 	    if (not ($remain->IsMember($lpair->Second))) {
# 		$remain->Push($lpair->Second);
# 		$unexpanded->Push($lpair->Second);
# 	    }
# 	}
#     }
#     #print $remain->Size,"  rem\n";
#     my $remove = $states->Difference($remain);
#     foreach my $rstate (values %{$remove}) {
# 	delete $delta{$rstate};
# 	delete $names{$rstate};
# 	$states->Delete($rstate);
# 	$fair->Pick->Delete($rstate);
#     }
    my $buechi = BuechiAL->new(
		states => $states,
		init   => $init,
		delta  => \%delta,
		names  => \%names,
		fair   => $fair,
	      );
    return $buechi;
} #ToBuechi

################################################################
#     To Compute the release function for enumerating the
#                 transistion function.
################################################################
sub release{
    my ($stateset,$index,$trex) = @_;
    my $low = 1;
    if ($index == 0) {
	$low = 0;
    }
    if ($index == 1) {
	if ($trex) {
	    $low = 1;
	}
	else {
	    $low = 0;
	}
    }
    if ($index == 2) {
	if ($trex) {
	    $low = 1;
	}
	else {
	    $low = 1;
	}
    }
    my $retset = Set->new(Set->new);
    my $flag = 1;
    foreach my $state (values %$stateset) {
	my $tempset = Set->new;
	for (my $j = $index; $j >= $index-$low; $j--) {
	    $tempset->Push(Set->new(Pair->new($state,$j)))
	}
	if ($flag) {
	    $retset = $tempset;
	    $flag = 0;
	}
	else {
	    $retset = expproduct($retset,$tempset);
	}
    }
    return $retset;
} # release


#####################################################################
# To compute the product of two formulae in DNF form used in ToBuechi
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

####################################################################
# To check whether the given state already exists and update states
#         and unexpanded sets based on that information
####################################################################
sub stcheck{
    my ($newstate,$states,$unexpanded) = @_;

    foreach my $state (values %{$states}) {
	if ($newstate->First->IsEqual($state->First)) {
	    if ($newstate->Second->IsEqual($state->Second)) {
		return $state;
	    }
	}
    }
    $states->Push($newstate);
    $unexpanded->Push($newstate);
    return $newstate;
} #stcheck

####################################################################
# Hashing Function
####################################################################
sub hashing {
    my ($newstate,$states,$unexpanded,$hashtable,$num,$anames) = @_;

    my $string = "";
    my $i = 0;
    my $temp = 0;
    my @a;
    my $stateset = $newstate->First;
    my $obligation = $newstate->Second;
    foreach my $astate(values %{$stateset}) {
	$a[$i] = $$num{$astate};
	$i++;
    }
    my @b = sort numeric @a;
    #print "\n@a | @b\n";
    $string = join(".",@b);
    $i = 0;
    if ($obligation->Size>0) {
	my @c;
	foreach my $astate (values %{$obligation}) {
	    $c[$i] = $$num{$astate};
	    $i++;
	}
	my @d = sort numeric @c;
	#print "@c | @d\n";
	$string .= "|".join(".",@d);
    }
    if (not(exists $$hashtable{$string})) {
	#print $string,"\n";
	$states->Push($newstate);
	$unexpanded->Push($newstate);
	$$hashtable{$string} = $newstate;
	return $newstate;
    }
    else {
	return $$hashtable{$string};
    }
}

###################################################################
# For comparison
###################################################################
sub numeric { $a <=> $b}

####################################################################
# On-the-fly minimization
####################################################################
sub firstprune{
    my $imagepairset = shift;
    my $remove = Set->new;
    foreach my $lpair (values %{$imagepairset}) {
	my $label = $lpair->First;
	my $dest = $lpair->Second;
	foreach my $lpair2 (values %{$imagepairset}) {
	    next if $lpair eq $lpair2;
	    if ($label->IsIncluded($lpair2->First)) {
	#	print "in\n";
		my $s = $dest->First;
		my $o = $dest->Second;
		my $sp = $lpair2->Second->First;
		my $op = $lpair2->Second->Second;
		if (($s->IsIncluded($sp) && ($o->IsIncluded($op)))) {
#		    print "in2\n";
		    $remove->Push($lpair2);
		}
	    }
	}
    }
    return $imagepairset->Difference($remove);
}

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
		    my @successorsets = SplitTransitionList($succlist);
		    my $succsets = Set->new;
		    foreach my $succsetname (@successorsets) {
			unless ($succsetname =~ s/^{//) {
			    die "missing left brace in transition list";
			}
			unless ($succsetname =~ s/}$//) {
			    die "missing right brace in transition list";
			}
			my @successornames=SplitTransitionList($succsetname);
			my $succset = Set->new;
			foreach my $succname (@successornames) {
			    my $sstate = $statemap{$succname};
			    $succset->Push($sstate);
			}
			$succsets->Push($succset);
		    }
		    $img->Push(Pair->new($label,$succsets));
		}
		my $state = $statemap{$name};
		$delta{$state} = $img;
		$init->Push($state) if $initflag;
	    }
	} elsif ($state eq "fair") {
	    if ($line eq "End") {
		$state = "end";
	    } else {
		#print $line,"\n";
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
    my $self = Alternating->new(
			   states => $states,
			   init   => $init,
			   delta  => \%delta,
			   names  => \%names,
			   fair   => $fair);
    # print $self->ToString;
    #$self->ToBuechi;
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


#####################################################################
# Converts a label set into a string set of the variables
# {p1=0,p2=1} becomes {"p1","p2"}
#####################################################################
sub LabelToStringSet {
    my ($label) = shift;
    my $retset = Set->new;
    foreach my $labelement (values %{$label}) {
	my $value = $labelement->Value;
	$value =~ s/=[10]+//;
	$retset->Push($value);
    }
    return $retset;

} # LabelToStringSet


#####################################################################
# Remove SCCs as long as the language does not change.
#####################################################################
sub PruneHeight {
    # Unpack.
    my ($self,$WAA2n) = @_;
    print "Pruning Height\n";
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $fair = $$self{fair};
    #my $Gform = Set->new();
    #$Gform->Push(LTL->new("a=1"));
    #$Gform->Push(LTL->new("b=0"));
    #print $Gform->ToString;
    #print "WAA2n \n";
    #$WAA2n->CheckWord($Gform);
    # Compute simulation relation for original automaton and
    # make all states simulated by an initial state initial.
    #my $inverse = InvertDelta($states,$delta);
    #my $simul = $self->ComputeDirectSimulationRelation(inverse => $inverse);
    #foreach my $pair (values %{$simul}) {
	#$init->Push($pair->First) if $init->IsMember($pair->Second);
    #}
    #print "augmented init ", $self->StateRelationToNameString($init), "\n";
    # Compute SCC quotient graph.
    my ($SCCs,$RSCClist) = $self->SCC;
    #my $RSCClist = reverse $SCClist;
    # print "made it here\n";
    #my $quotient = $self->Quotient($SCCs);
    #print $quotient->ToString;
    #my $qfair = $$quotient{fair}->Pick;
    # print "fair SCCs: ", $quotient->StateRelationToNameString($qfair),
    #   "\n"; #diag
    my $removals = 0;
    #my $n = $$cobuechi{states};
    my $i = 1;
    #my $max = (2 * $n) +1;
    # $RSCClist contains the SCCs in topological order from sinks to sources.
    foreach my $scc (@{$RSCClist}) {
	#next unless $qfair->IsMember($scc);
	#print "Examining fair SCC: ", $self->StateRelationToNameString($scc),
	 # "\n"; # diag
	#print "Checking SCC: ",$scc->ToString,"\n";
	# Collect transitions into the SCC.
	my $forbidden = {};
	#my $entrypoints = Set->new;
	my $fromstates = Set->new;
	my $fcount = 0;
	foreach my $state (values %{$states}) {
	    next if $scc->IsMember($state);
	    $$forbidden{$state} = Set->new;
	    my $transitions = $$delta{$state};
	    foreach my $trans (values %{$transitions}) {
		my $destsetofsets = $trans->Second;
		foreach my $destset (values %{$destsetofsets}) {
		    unless ($destset->IsDisjoint($scc)) {
			#$entrypoints->Add($destset->Intersection($scc));
			$$forbidden{$state}->Push($destset);
			$fromstates->Push($state);
			$fcount++;
		    }
		}
	    }
	}
#	print "Warning: fcount == 0!\n" unless $fcount;
	next unless $fcount > 0;
	# Diagnostic prints.
	# foreach my $state (values %{$states}) {
# 	    my $transitions = $$forbidden{$state};
# 	    foreach my $trans (values %{$transitions}) {
# 		#print "forbidden transition: ", $state->ToString, " -> ",
# 		 # $trans->ToString, "\n";
# 	    }
# 	}
	# Should we add the "forbidden" option to InvertDelta?
	#my $newsimul =
	 # $self->ComputeDirectSimulationRelation(inverse => $inverse,
		#				 forbidden => $forbidden);
	# my $check = $entrypoints->Clone;
# 	#print "Checking entry points ",$check->ToString,"\n";
#       NLOOP:foreach my $pair (values %{$newsimul}) {
# 	    if ($check->IsMember($pair->First)) {
# 		$check->Delete($pair->First);
# 		last NLOOP if $check->Size == 0;
# 	    }
# 	}
	# open(BF,">altb4$i.dot");
# 	print BF $self->ToDot("alt");
#  	close(BF);
	#print $coalt->ToString,"\n";
	#if ($check->Size == 0) {
	    #print "remove SCC\n";
	# open(BF,">WAA2n.buechi");
# 	print BF $WAA2n->ToString,"\n";
#  	close(BF);

	my $check = Alternating->CompDualaltbuechi($self,forbidden => $forbidden);

	    #print "This is the composition of CoBuechi automaton with",
	     # "alternating automaton at ",2*($i-1)," layers \n";
	    #print $check->ToString,"\n";
        # open(BF,">altdu$i.dot");
#  	print BF $check->ToDot("altdu$i");
#  	close(BF);
	$check->DirectSimulationMinimization;
	$check->MergeTransitions;
	# open(BF,">altdu$i.dot");
#   	print BF $check->ToDot("altdu$i");
#   	close(BF);
# 	open(BF,">altdu$i.buechi");
#   	print BF $check->ToString;
#   	close(BF);

	my $bl = $check->ToBuechi(nocons => 1);

	$bl->MergeTransitions;
	# open(FP,">bl$i.dot");
#  	print FP $bl->ToDot("bl$i");
#  	close(FP);
# 	open(BF,">buco$i.buechi");
#  	print BF $bl->ToString,"\n";
#  	close(BF);
	$bl->DirectSimulationMinimization;
	$bl->MergeTransitions;
#	$bl->CheckWord($Gform);
	# open(FP,">bl$i.dot");
#  	print FP $bl->ToDot("bl$i");
#  	close(FP);
	# open(BF,">buco$i.buechi");
# 	print BF $bl->ToString,"\n";
#  	close(BF);
	$i++;
	#print "Dual\n ";
	#$bl->CheckWord($Gform);
	next unless $bl->IsIntersectionEmpty($WAA2n);
	#print "Removal accepted \n";
	#my $coalt = Alternating->Composealtcobuechi($self,$cobuechi,forbidden => $forbidden);
	#print $coalt->ToString,"\n";
	#next unless $coalt->CoBuechiIsEmpty;
	#if ($check->Size == 0) {
	    #print "remove SCC\n";
	$removals++;
	#print "Removing SCC: ",$scc->ToString," ",$i-1,"\n";
	foreach my $state (values %$fromstates) {
	    my $image = $$delta{$state};
	    foreach my $lpair (values %$image) {
		foreach my $destset (values %{$$forbidden{$state}}) {
		    if ($lpair->Second->IsMember($destset)) {
			$lpair->Second->Delete($destset);
		    }
		}
	    }
	    $$delta{$state} = $image;
	}
    #}
    }
    if ($removals > 0) {
	$self->DirectSimulationMinimization;
	$self->PruneUnreachable;
	# We should not have to explicitly return to one initial state.
	# Until we prove this is indeed the case, we check.
	if ($init->Size != 1) {
	    #print "Warning: multiple initial states\n";
	}
    }

} # PruneHeight


######################################################################
# Remove unreachable states from automaton.
######################################################################
sub PruneUnreachable {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $reachable = Reachable($init,$delta);
    foreach my $state (values %{$states}) {
	delete $$delta{$state} unless $reachable->IsMember($state);
    }
    foreach my $fairset (values %{$fair}) {
	$fairset->Restrict($reachable);
    }
    $states->Restrict($reachable);

} # PruneUnreachable


######################################################################
# Computes the strongly connected components of an automaton.
# Tarjan's algorithm as described in Aho, Hopcroft, and Ullman,
# The Design and Analysis of Computer Algorithms.
######################################################################
sub SCC {
    my $self = shift;
    my @stack = ();
    my %onstack = ();
    my %dfnumber = ();
    my %lowlink = ();
    my @scclist = ();
    my $init = $$self{init};
    my $count = 0;
    foreach my $initial (values %{$init}) {
	unless (exists $dfnumber{$initial}) {
	    searchSCC($self,$initial,\@scclist,\@stack,\%onstack,
		      \%dfnumber,\%lowlink,\$count);
	}
    }
    my @rscclist = reverse @scclist;
    my $scc = Set->new(@rscclist);
    return ($scc,\@rscclist);

} # SCC


######################################################################
# DFS for the computation of the strongly connected components.
######################################################################
sub searchSCC {
    my ($self,$v,$scc,$stack,$onstack,$dfnumber,$lowlink,$countr) = @_;
    $$lowlink{$v} = $$dfnumber{$v} = $$countr;
    ${$countr}++;
    push(@{$stack},$v);
    $$onstack{$v} = 1;
    my $delta = $$self{delta};
    foreach my $transition (values %{$$delta{$v}}) {
	my $transset = $transition->Second;
	foreach my $trans (values %$transset) {
	    foreach my $w (values %$trans) {
		unless (exists $$dfnumber{$w}) {
		    searchSCC($self,$w,$scc,$stack,$onstack,
			      $dfnumber,$lowlink,$countr);
		    $$lowlink{$v} = $$lowlink{$w} if $$lowlink{$w} < $$lowlink{$v};
		} elsif ($$dfnumber{$w} < $$dfnumber{$v} and exists $$onstack{$w}) {
		    $$lowlink{$v} = $$dfnumber{$w} if $$dfnumber{$w} < $$lowlink{$v};
		}
	    }
	}
    }
    if ($$dfnumber{$v} == $$lowlink{$v}) {
	my $x;
	my $component = Set->new;
	do {
	    $x = pop(@{$stack});
	    delete $$onstack{$x};
	    $component->Push($x);
	} while ($x ne $v);
	unshift(@{$scc},$component);
    }

} # searchSCC


######################################################################
# Returns the quotient graph for a partition of the states of an
# automaton.  The quotient graph has one fair set at most.
# A state of the quotient is fair if it intersects all the fair
# sets of the original automaton and it contains a cycle.
######################################################################
sub Quotient {
    my ($self,$partition) = @_;
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $names = $$self{names};
    my $fair = $$self{fair};
    my $initQ = Set->new;
    my %deltaQ = ();
    my $namesQ = AddNames($partition,"SCC");
    my %labelsQ = ();
    my %map = ();
    foreach my $class (values %{$partition}) {
	$initQ->Push($class) unless $class->IsDisjoint($init);
	my $name = Set->new;
	foreach my $state (values %{$class}) {
	    $name->Push($$names{$state});
	    $map{$state} = $class;
	}
	$labelsQ{$class} = $name;
	$deltaQ{$class} = Set->new;
    }
    my $states = $$self{states};
    foreach my $state (values %{$states}) {
	# Skip states that have become unreachable, and hence
	# are not in any SCC.
	next unless exists $map{$state};
	my $source = $map{$state};
	my $succ = $$delta{$state};
	foreach my $transition (values %{$succ}) {
	    my $otherstate = $transition->Second;
	    my $dest = $map{$otherstate};
	    $deltaQ{$source}->Push($dest);
	}
    }
    my $fairsetQ = $partition->Clone;
    # Remove SCCs consisting of one state only unless the state has
    # a self-loop.
    foreach my $class (values %{$fairsetQ}) {
	$fairsetQ->Delete($class) unless $deltaQ{$class}->IsMember($class);
    }
    # Remove from the fair set every SCC that does not intersect all fair
    # sets of the given automaton.
    foreach my $fairset (values %{$fair}) {
	foreach my $class (values %{$fairsetQ}) {
	    $fairsetQ->Delete($class) if $class->IsDisjoint($fairset);
	}
    }
    my $fairQ = Set->new;
    $fairQ->Push($fairsetQ) unless $fairsetQ->IsEqual($partition);
    return Buechi->new(
		       states => $partition,
		       init   => $initQ,
		       delta  => \%deltaQ,
		       names  => $namesQ,
		       labels => \%labelsQ,
		       fair   => $fairQ
		      );

} # Quotient


######################################################################
# Computes the reachable states of an automaton by BFS.
######################################################################
sub Reachable {
    my ($init,$delta) = @_;
    my $reached = $init->Clone;
    my $new = $init->Clone;
    while ($new->Size > 0) {
	my $image = Set->new;
	foreach my $state (values %{$new}) {
	    my $transitions = $$delta{$state};
	    foreach my $transpair (values %{$transitions}) {
		my $transset = $transpair->Second;
		foreach my $trans (values %{$transset}) {
		    foreach my $w (values %$trans) {
			$image->Push($w);
		    }
		}
	    }
	}
	$new = $image->Difference($reached);
	$reached->Add($image);
    }
    return $reached;

} # Reachable

######################################################################
# Apply direct simulation minimization to an automaton.
######################################################################
sub DirectSimulationMinimization {
    my $self = shift;
    my $states = $$self{states};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $names = $$self{names};

    my $inverse = InvertDelta($states,$delta);
    my ($newsimul,$important) = $self->ComputeDirectSimulationRelationArcs(inverse => $inverse);
    foreach my $pair (values %{$newsimul}) {
	my $u = $pair->First;
	my $v = $pair->Second;
	foreach my $upair (values %{$$inverse{$u}}) {
	    my $ulabel = $upair->First;
	    my $upred = $upair->Second;
	    foreach my $vpair (values %{$$inverse{$v}}) {
		my $vlabel = $vpair->First;
		if ($vlabel->IsEqual($ulabel)) {
		    my $vpred = $vpair->Second;
		    if ($vpred eq $upred) {
			my $image = $$delta{$vpred};
			my $imp = $$important{Pair->new($vpred,$vlabel)};
			foreach my $lpair (values %{$image}) {
			    next unless ($lpair->First)->IsEqual($vlabel);
			    my $succsetofsets = $lpair->Second;
			    foreach my $succset (values %{$succsetofsets}) {
				if (($succset->IsMember($u))
				    && ($succset->IsMember($v))){
				    my $donts = Set->new;
				    foreach my $ip (values %$imp) {
					if ($ip->First eq $succset) {
					    $donts = $ip->Second;
					    last;
					}
				    }
				    $succset->Delete($v) unless $donts->IsMember($v);
				}
			    }
			}
		    }
		}
	    }
	}
    }
    $self->PruneUnreachable;
    $inverse = InvertDelta($states,$delta);
    my $simul = $self->ComputeDirectSimulationRelation(inverse => $inverse);
   # print $simul->ToString,"\n";
   # print $self->ToDot("self");
    # Simplify the automaton.
    # Find direct-simulation equivalent states.
    foreach my $pair (values %{$simul}) {
	next unless $simul->IsMember($pair);
	my $p = $pair->First;
	my $q = $pair->Second;
	# Make sure neither state has been removed yet.
	next unless $states->IsMember($p) and $states->IsMember($q);
	my $swapped = Pair->new($q,$p);
	next unless $simul->IsMember($swapped);
	# Theorem applies.
	# $simul->Delete($pair,$swapped);
	# Throw away p and connect its predecessors to q.
	#print "$$names{$p} is direct-simulation equivalent to $$names{$q}\n";
	# Update inverse image of successors.
	foreach my $s (values %{$$delta{$p}}) {
	    my $slabel = $s->First;
	    my $ssetofsetofstate = $s->Second;
	    foreach my $succset (values %$ssetofsetofstate) {
		foreach my $sstate (values %$succset) {
		    next if $sstate eq $p;
		    $$inverse{$sstate}->Delete(Pair->new($slabel,$p));
		}
	    }
	}
	# Update image of predecessors.
	foreach my $s (values %{$$inverse{$p}}) {
	    my $slabel = $s->First;
	    my $sstate = $s->Second;
	    next if $sstate eq $p;
	    foreach my $lpair (values %{$$delta{$sstate}}) {
		next unless $lpair->First->IsEqual($slabel);
		foreach my $succset (values %{$lpair->Second}) {
		    next unless $succset->IsMember($p);
		    $succset->Delete($p);
		    $succset->Push($q);
		}
	    }
	    $$inverse{$q}->Push($s);
	}
	# Update the fair sets.
	foreach my $fairset (values %{$fair}) {
	    $fairset->Delete($p);
	}
	# Remove state p from automaton.
	if ($init->IsMember($p)) {
	    $init->Delete($p);
	    $init->Push($q);
	}
	delete $$delta{$p};
	delete $$names{$p};
#	delete $$dontcares{$p};
	$states->Delete($p);
    }
    foreach my $pair (values %{$simul}) {
	my $u = $pair->First;
	my $v = $pair->Second;
	foreach my $upair (values %{$$inverse{$u}}) {
	    my $ulabel = $upair->First;
	    my $upred = $upair->Second;
	    foreach my $vpair (values %{$$inverse{$v}}) {
		my $vlabel = $vpair->First;
		if ($vlabel->IsEqual($ulabel)) {
		    my $vpred = $vpair->Second;
		    if ($vpred eq $upred) {
			my $image = $$delta{$vpred};
			foreach my $lpair (values %{$image}) {
			    next unless ($lpair->First)->IsEqual($vlabel);
			    my $succsetofsets = $lpair->Second;
			    foreach my $succset (values %{$succsetofsets}) {
				if (($succset->IsMember($u))
				    && ($succset->IsMember($v))){
				    $succset->Delete($v);
				}
			    }
			}
		    }
		}
	    }
	}
    }
    $self->PruneUnreachable;
    foreach my $state (values %$states) {
	my $image = $$delta{$state};
	foreach my $lpair (values %$image) {
	    my $flab = $lpair->First;
	    my $fdes = $lpair->Second;
	    my $removals = Set->new;
	    SLOOP: foreach my $stateset (values %$fdes) {
		OLOOP: foreach my $otherset (values %$fdes) {
		    next if $stateset eq $otherset;
		  FLOOP: foreach my $fs (values %$stateset) {
			foreach my $ss(values %$otherset) {
			    next FLOOP if (($fs eq $ss) or
				 ($simul->IsMember(Pair->new($ss,$fs))));
			 }
			next OLOOP;
		      }
		    $removals->Push($otherset);
		    next SLOOP;
		}
	      }
	    $fdes->Subtract($removals);
	}
    }
    #print "b4 fairness arcs ",$self->ToDot("altd1"),"\n";
    $self->MergeTransitions;
    #print "after fairness arcs ",$self->ToDot("altd2"),"\n";
    return;
}

######################################################################
# Compute the set of pairs (p,q) such that q simulates p and is
# distinct from it.
######################################################################
sub ComputeDirectSimulationRelation {
    my $self = shift;
    my %params = @_;
    my $states = $$self{states};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $names = $$self{names};
    my $inverse;
    if (defined $params{inverse}) {
	$inverse = $params{inverse};
    } else {
	$inverse = InvertDelta($states,$delta);
    }
    my $forbidden;
    if (defined $params{forbidden}) {
	$forbidden = $params{forbidden};
    } else {
	$forbidden = {};
    }
    # Initialize the direct simulation relation to all pairs (p,q)
    # that satisfy:
    # 0. p != q
    # 2. for each f in F, p in f -> q in f
    # Also, push all pairs in the simulation relation onto a queue.
    my $simul = Set->new;
    my @queue = ();
    my %enqueued = ();
  FIRST: foreach my $p (values %{$states}) {
      SECOND: foreach my $q (values %{$states}) {
	    next SECOND if $p eq $q;
	    foreach my $fairset (values %{$fair}) {
		if ($fairset->IsMember($p)) {
		    next SECOND unless $fairset->IsMember($q);
		}
	    }
	    my $pair = Pair->new($p,$q);
	    $simul->Push($pair);
	    push(@queue, $pair);
	    $enqueued{$pair} = 1;
	}
    }
#     print "Direct simulation relation initially contains ",
#       $simul->Size, " pairs\n";
#     foreach my $pair (values %{$simul}) {
# 	print $$names{$pair->First}, " is direct simulated by ",
# 	  $$names{$pair->Second}, "\n";
#     }
    # Compute the greatest fixpoint.
  PAIRS: while (@queue > 0) {
	my $pair = pop(@queue);
	delete $enqueued{$pair};
	my $p = $pair->First;
	my $q = $pair->Second;
	my $nogoodp = defined $$forbidden{$p} ? $$forbidden{$p} : Set->new;
	my $nogoodq = defined $$forbidden{$q} ? $$forbidden{$q} : Set->new;
	# print "Pair: $$names{$p} simulated by $$names{$q}"; #diag
      PLOOP: foreach my $s (values %{$$delta{$p}}) {
	    my $slabel = $s->First;
	    my $sstatesetofsets = $s->Second;
	    foreach my $t (values %{$$delta{$q}}) {
		my $tlabel = $t->First;
		my $tstatesetofsets = $t->Second;
		if ($tlabel->IsIncluded($slabel)) {
		    #next PLOOP if $sstate eq $tstate;
		    #next PLOOP if $simul->IsMember(Pair->new($sstate,$tstate));
		     my $flag = 1;
		  SLOOP:foreach my $sstateset(values %{$sstatesetofsets}) {
			next SLOOP if $nogoodp->IsMember($sstateset);
		      TLOOP:foreach my $tstateset (values %{$tstatesetofsets}) {
			    next if $nogoodq->IsMember($tstateset);
			  ILOOP:foreach my $qp (values %{$tstateset}) {
				foreach my $pp (values %{$sstateset}) {
				    next ILOOP if (($pp eq $qp) ||
					($simul->IsMember(Pair->new($pp,$qp))));
				}
				#$flag = 0;
				#last SLOOP;
				next TLOOP;
			    }
			    next SLOOP ;
			}
			$flag = 0;
			last SLOOP;
		    }
		    next PLOOP if ($flag);
		}
	    }
	    $simul->Delete($pair);
	    # Enqueue perturbed pairs.
	    foreach my $u (values %{$$inverse{$p}}) {
		my $ulabel = $u->First;
		my $ustate = $u->Second;
		foreach my $v (values %{$$inverse{$q}}) {
		    my $vlabel = $v->First;
		    next unless $vlabel->IsIncluded($ulabel);
		    my $vstate = $v->Second;
		    my $newpair = Pair->new($ustate,$vstate);
		    if ($simul->IsMember($newpair)) {
			unless (exists $enqueued{$newpair}) {
			    push(@queue,$newpair);
			    $enqueued{$newpair} = 1;
			}
		    }
		}
	    }
	    # print " removed\n"; #diag
	    next PAIRS;
	}
	# print " retained\n"; #diag
    }
    #print "Direct simulation relation contains ", $simul->Size,
#      " pairs\n"; #diag
    # return $simul unless $simul->Size > 0;
 #   print "Direct simulation sans identity: {[simulated,simulating],...}\n",
  #    $self->StateRelationToNameString($simul), "\n"; # diag

    return $simul;

} # ComputeDirectSimulationRelation

######################################################################
# Compute the set of pairs (p,q) such that q simulates p and is
# distinct from it with fairness on arcs.
######################################################################
sub ComputeDirectSimulationRelationArcs {
    my $self = shift;
    my %params = @_;
    my $states = $$self{states};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $names = $$self{names};
    my $inverse;
    if (defined $params{inverse}) {
	$inverse = $params{inverse};
    } else {
	$inverse = InvertDelta($states,$delta);
    }
#     my $forbidden;
#     if (defined $params{forbidden}) {
# 	$forbidden = $params{forbidden};
#     } else {
# 	$forbidden = {};
#     }
    # Initialize the direct simulation relation to all pairs (p,q)
    # that satisfy:
    # p != q
    # Also, push all pairs in the simulation relation onto a queue.
    my $simul = Set->new;
    my @queue = ();
    my %enqueued = ();
  FIRST: foreach my $p (values %{$states}) {
      SECOND: foreach my $q (values %{$states}) {
	    next SECOND if $p eq $q;
	    my $pair = Pair->new($p,$q);
	    $simul->Push($pair);
	    push(@queue, $pair);
	    $enqueued{$pair} = 1;
	}
    }
    my $fairset = $fair->Pick;
    # fairness arcs
    my $fairness = {};
    foreach my $state (values %{$states}) {
	my $image = $$delta{$state};
	$$fairness{$state} = Set->new;
	foreach my $lpair (values %$image) {
	    foreach my $succset (values %{$lpair->Second}) {
		if ($succset->Intersection($fair->Pick)->Size > 0) {
		    $$fairness{$state}->Push($succset);
		}
	    }
	}
    }
#     print "Direct simulation relation initially contains ",
#       $simul->Size, " pairs\n";
#     foreach my $pair (values %{$simul}) {
# 	print $$names{$pair->First}, " is direct simulated by ",
# 	  $$names{$pair->Second}, "\n";
#     }
    # Compute the greatest fixpoint.
   my  %important = ();
  PAIRS: while (@queue > 0) {
	my $pair = pop(@queue);
	delete $enqueued{$pair};
	my $p = $pair->First;
	my $q = $pair->Second;
	# print "Pair: $$names{$p} simulated by $$names{$q}"; #diag
	# For each transition out of p
      PLOOP: foreach my $s (values %{$$delta{$p}}) {
	    my $slabel = $s->First;
	    my $sstatesetofsets = $s->Second;
	    $important{Pair->new($p,$slabel)} = Set->new;
	    my $psetf= Set->new;
	    # For each transition out of q
	    foreach my $t (values %{$$delta{$q}}) {
		my $tlabel = $t->First;
		my $tstatesetofsets = $t->Second;
		$important{Pair->new($q,$tlabel)} = Set->new;
		my $qsetf = Set->new;
		next unless $tlabel->IsIncluded($slabel);
		# Transitions have compatible labels.  Check successors.
		my $flag = 1;  # flag stays at 1 as long as all Cs are matched
		# For each C in Delta(p,slabel)
	      SLOOP: foreach my $sstateset(values %{$sstatesetofsets}) {
		    my $sflag = $fairset->Intersection($sstateset)->Size;
		    # For each C' in Delta(q,tlabel)
		  TLOOP: foreach my $tstateset (values %{$tstatesetofsets}) {
			my $pset = Set->new;
			my $tflag = $fairset->Intersection($tstateset)->Size;
			next PLOOP if $tstateset->Size == 0; # true trans.
			next TLOOP if $sflag and not $tflag;
			# Check whether C' simulates C.
		      ILOOP: foreach my $qp (values %{$tstateset}) {
			    foreach my $pp (values %{$sstateset}) {
				if (($pp eq $qp) or
				  ($simul->IsMember(Pair->new($pp,$qp))
				   and ($fairset->IsMember($qp) or
					not $fairset->IsMember($pp))))
				    {
					$pset->Push($pp);
				    }
			    }
			    next TLOOP; # no, it does not
			}
			$qsetf->Push(Pair->new($tstateset,$tstateset));
			$psetf->Push(Pair->new($sstateset,$pset));
			next SLOOP;	# yes, it does, check next C
		    }
		    $flag = 0;
		    last SLOOP; # couldn't find a C' for the current C
		}
		$important{Pair->new($p,$slabel)} = $psetf;
		$important{Pair->new($q,$tlabel)} = $qsetf;
		next PLOOP if $flag; # found matching transition
	    }
	    $simul->Delete($pair);
	    # Enqueue perturbed pairs.
	    foreach my $u (values %{$$inverse{$p}}) {
		my $ulabel = $u->First;
		my $ustate = $u->Second;
		foreach my $v (values %{$$inverse{$q}}) {
		    my $vlabel = $v->First;
		    next unless $vlabel->IsIncluded($ulabel);
		    my $vstate = $v->Second;
		    my $newpair = Pair->new($ustate,$vstate);
		    if ($simul->IsMember($newpair)) {
			unless (exists $enqueued{$newpair}) {
			    push(@queue,$newpair);
			    $enqueued{$newpair} = 1;
			#    print $newpair->ToString," enqueued 'coz of ",$pair->ToString,"\n";
			}
		    }
		}
	    }
	    # print " removed\n"; #diag
	    next PAIRS;
	}
	# print " retained\n"; #diag
    }
    #print "Direct simulation relation contains ", $simul->Size,
#      " pairs\n"; #diag
    # return ($simul,\%important) unless $simul->Size > 0;
    #print "Direct simulation sans identity: {[simulated,simulating],...}\n",
 #     $self->StateRelationToNameString($simul), "\n"; # diag

    return ($simul,\%important);

} # ComputeDirectSimulationRelationArcs


######################################################################
# Computes the inverse of delta.
######################################################################
sub InvertDelta {
    my ($states,$delta) = @_;
    my %inverse = ();
    foreach my $state (keys %{$states}) {
	$inverse{$state} = Set->new;
    }
    foreach my $state (values %{$states}) {
	my $image = $$delta{$state};
	foreach my $succpair (values %{$image}) {
	    my $slabel = $succpair->First;
	    my $sstatesetofsets = $succpair->Second;
	    foreach my $sstateset (values %{$sstatesetofsets}) {
		foreach my $sstate(values %{$sstateset}) {
		    $inverse{$sstate}->Push(Pair->new($slabel,$state));
		}
	    }
	}
    }
    return \%inverse;

} # InvertDelta

#########################################################################
# Decomposes a set into set of sets
#########################################################################
sub Decompose {
    my $set = shift;
    if ($set->Size == 0) {
	return Set->new(Set->new);
    }
    my $retset = Set->new;
    foreach my $element (values %{$set}) {
	my $eset = Set->new($element);
	$retset->Push($eset);
    }
    return $retset;
}
# Required return value.

######################################################################
# Merge transitions from the same source to the same destination
# with different labels.
######################################################################
sub MergeTransitions {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $names = $$self{names};
    my $i = 1;
    my %num= ();
    foreach my $state (values %{$states}) {
	$num{$state} = $i;
	$i++;
    }
    foreach my $state (values %{$states}) {
	my $oldimg = $$delta{$state};
	my $newimg = Set->new;
	my %toLabels = ();
	my $destinations = Set->new;
	foreach my $pair (values %{$oldimg}) {
	    my $label = $pair->First;
	    my $destset = $pair->Second;
	    foreach my $dest (values %$destset) {
		#print "hhh\n";
		my $hval = hash($dest,\%num,$names);
		unless (defined $toLabels{$hval}) {
		    $toLabels{$hval} = Cover->new;
		}
		$toLabels{$hval}->Push($label);
		#print "iii\n";
		$destinations->Push($dest);
	    }
	}
	my %labeltodest = ();
	my $labels = Set->new;
	foreach my $dest (values %{$destinations}) {
	    my $hval = hash($dest,\%num,$names);
	    my $picover = $toLabels{$hval}->PrimeAndIrredundant;
	 #   print $$names{$state}, " - ",  $picover->ToString, " -> ",
	  #    $dest->ToString, "\n"; # diag
	  #  foreach my $label (values %{$picover}) {
		#$newimg->Push(Pair->new($label,$dest));
	    #}
	    foreach my $label (values %{$picover}) {
		my $l = LabelToString($label);
		unless (defined $labeltodest{$l}) {
		    $labeltodest{$l} = Set->new;
	#	    print "newlabel ",$label->ToString,"\n";
		    $labels->Push($label);
		}
		my $flag =1;
		foreach my $sset (values %{$labeltodest{$l}}) {
		    my $hval2 = hash($sset,\%num,$names);
		    if ($hval eq $hval2) {
			$flag = 0;
			last;
		    }
		}
		if ($flag) {
		    $labeltodest{$l}->Push($dest);
		}
	    }
	}
	foreach my $label (values %{$labels}) {
	    my $flag = 1;
	    my $l = LabelToString($label);
	    my $dest = $labeltodest{$l};
	   #  my $hval1 = hash($dest,\%num,$names);
# 	    foreach my $lpair (values %{$newimg}) {
# 		my $hval2 = hash($lpair->Second,\%num,$names);
# 		if (($lpair->First->IsEqual($label)) && ($hval1 eq $hval2)) {
# 		    $flag = 0;
# 		    last;
# 		}
	#    }
	    $newimg->Push(Pair->new($label,$dest)) if $flag;
	}
#	print "new image of state", $state->ToString," is ",$newimg->ToString,"\n";
	$$delta{$state} = $newimg;
    }
} # MergeTransitions


####################################################################
# Hashing Function
####################################################################
sub hash {
    my ($stateset,$num,$anames) = @_;

    my $string = "";
    my $i = 0;
    my $temp = 0;
    my @a;
    my @b;
    foreach my $astate(values %{$stateset}) {
	$a[$i] = $$num{$astate};
	$i++;
    }
    @b = sort numeric @a;
    #print "\n@a | @b\n";
    $string = join(".",@b);
    return $string;
}

#####################################################################
# Converts a label set into a string {p1=0,p2=1} becomes "p10.p21"
#####################################################################
sub LabelToString {
    my ($label) = shift;
    my $retstring = "";
    my @a;
    my $i = 0;
    foreach my $labelement (values %{$label}) {
	my $value = $labelement->Value;
	$value =~ s/=//;
	$a[$i] = $value;
	$i++;
    }
    $retstring = join(".",sort @a);
    return $retstring;
}

1;
