# $Id: AlternatingTree.pm,v 1.39 2007/05/31 16:53:18 bjobst Exp $

######################################################################
# Functions to create and manipulate Alternating Tree automata.
#
# Lily - LInear Logic sYnthesize
# Author: Barbara Jobstmann <bjobst@ist.tugraz.at>
#
# delta = Hash: state -> Set of Pair[ label, conjunctions ]
#         conjunctions = Set of Pair[ direction, state ]
# state,label,direction = Set of LTL
#
# delta(s) = {(a,{(r,s1),(r*c,s2),(!c,s1)}),(!a,{(c,s),(!c,s1)})}
#
# Some semantics
# delta(s) = {} ... FALSE
# delta(s) = {(a,{})} ...FALSE
# delta(s) not defined TRUE
# delta(s) = {...} ..not defined for a -> TRUE
# delta(s) = {(a,{(r,s1),(r*c,s2),(!c,s1)}),(!a,{(c,s),(!c,s1)})} ->
# delta for s,a,!r*c is TRUE
######################################################################

package AlternatingTree;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK $nameIndex $DEBUG);
@ISA       = qw(CoBuechiTree);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
$DEBUG     = 1;
use strict;
use Set;
use Cover;
use Pair;


################################################################
# Make a basic AlternatingTree structure by inheriting all members
# from BuechiALTree.
################################################################
sub new {
    my $class = shift;
    my $self = BuechiALTree->new(@_);
    bless $self, $class;
    return $self;
}

######################################################################
# Convert the input Co-Buechi automata with labels on arcs to
#              alternating automata.
# Note: The UCT is constructed by inverting a NBW. Since the NBW has 
# no FALSE states, the UCT has no TRUE states. If a state s in an NBW
# has no transition (delta(s) is not defined) then delta(s) is false.
# Since the UCT is the invert of an NBW missing transitions are the 
# opposite meaning: delta(s) is not defined means delta(s) is true.
# (We have no restrictions on delta(s)).
# Analogous, since the NBW constructed here has no special transition 
# representing true (delta(s)=true), we don't get delta(s)=false in 
# the UCT.
######################################################################
sub fromBuechi {
	my ( $class, $cobuechi, $weak, $rank, $orelease, $verb) = @_;
	$verb = 1 if (not defined $verb);
	my $cbstates   = $$cobuechi{states};
	my $cbinit     = $$cobuechi{init};
	my $cbdelta    = $$cobuechi{delta};
	my $cbdirections = $$cobuechi{directions};
	my $cbfair     = $$cobuechi{fair};
	my $cbnames    = $$cobuechi{names};
	my $n          = $cbstates->Size;
	my $alpha      = $cbfair->Pick->Size;
	my $k          = 0;
	my $init       = Set->new;
	my $unexpanded = Set->new;
	my $states     = Set->new;
	my %delta      = ();
	my %names      = ();
	my $fair       = Set->new;
	my $finalfair  = Set->new;
	my %new        = ();
	my $self       = \%new;
	print "-- from CoBuechiTree to AlternatingTree --\n" if $verb > 1;

	if (not defined $cbinit->Pick) {
	    print "No initial state found\n";
	    return "";
	}

	#we do not expand alpha states in odd ranks
	if ($cbfair->Pick->IsMember($cbinit->Pick) && ($rank % 2)==1 ) {
	    #If the initial state is an alpha state, we have to start
	    #at an even rank
	    $rank = $rank + 1;
	    print "We do not expand alpha states in odd ranks -> ";
	    print "rank encreased to $rank.\n";
#	    return "";
	}

	if ( !$weak ) {
	    print "UCT is not weak - Start translation with rank $rank\n";
	    #$rank = 2*($n-1); # n*2^n
	    my $newstate = Pair->new( $cbinit->Pick, $rank );
	    $states->Push($newstate);
	    $unexpanded->Push($newstate);
	    $init->Push($newstate);
	    Create2layers( $cobuechi, $states, \%delta, \%names, $unexpanded, $fair,  $orelease, $verb );
	    $finalfair->Push($fair);
	    $self = {
		     states => $states,
		     init   => $init,
		     delta  => \%delta,
		     names  => \%names,
		     directions => $cbdirections,
		     fair   => $finalfair,
		    }
	} else {
	    print "UCT is weak.\n";
	    my $false = Set->new;
	    foreach my $bstate ( values %{$cbstates} ) {
		my $newstate = Pair->new( $bstate, 1 );
		$states->Push( $newstate );
		foreach my $fairset ( values %{$cbfair} ) {
		    if ( not( $fairset->IsMember($bstate) ) ) {
			$fair->Push($newstate);
		    }
		}
		my $bimageset   = $$cbdelta{$bstate};
		my $newimageset = Set->new;

		print "-- state: ", $$cbnames{$bstate}, "\n" if ($DEBUG == 4);
		print "-- image: ", $bimageset->ToString($cbnames) , "\n" if ($DEBUG == 4);
		foreach my $labeledpair ( values %{$bimageset} ) {
		    my $slabel = $labeledpair->First;
		    my $dest   = $labeledpair->Second;
				
		    print "---- label: ", $slabel->ToString($cbnames), "\n" if ($DEBUG == 4);
		    print "---- dest: ", $dest->ToString($cbnames), "\n" if ($DEBUG == 4);
		    my $newimagestateset = Set->new;
		    if ($dest->Size == 0) { #tr is FALSE
			$newimageset->Push( Pair->new( $slabel, $false ) );
			next;
		    }
		    foreach my $destelement ( values %{$dest} ) {
			my $direction = $destelement->First;
			my $state     = $destelement->Second;
			my $destState = $false;  #tr to FALSE
			$destState = Pair->new( $state, 1 ) if ($cbstates->IsMember($state));
			$newimagestateset->Push( Pair->new( $direction, $destState ) );
		    }
		    $newimageset->Push( Pair->new( $slabel, $newimagestateset ) );
		}
		$init->Push($newstate) if $cbinit->IsMember($bstate);
		$delta{$newstate} = $newimageset;
		$names{$newstate} = $$cbnames{$bstate} . "_1";
	    }
	    $finalfair->Push($fair);
	    $self = {
		     states => $states,
		     init   => $init,
		     delta  => \%delta,
		     names  => \%names,
		     directions => $cbdirections,
		     fair   => $finalfair,
		    }
	}
	if ( $$self{init}->Size > 1 ) {
	    my $max = 0;
	    my $left;
	    foreach my $st ( values %{ $$self{init} } ) {
		if ( $st->Second > $max ) {
		    $max  = $st->Second;
		    $left = Set->new($st);
		}
	    }
	    $$self{init}->Restrict($left);
	}

	return bless $self, $class;
}

	
################################################################
# Convert the input Co-Buechi automata with labels on arcs to
# alternating automata.
################################################################
sub Create2layers {
    print "-- Create2layers --\n";
    my ( $cobuechi, $states, $delta, $names, $unexpanded, $fair, $orelease, $verb ) = @_;
    $verb = 3 if (not defined $verb);
    my $cbstates = $$cobuechi{states};
    my $cbinit   = $$cobuechi{init};
    my $cbdelta  = $$cobuechi{delta};
    my $cbfair   = $$cobuechi{fair};
    my $cbdirections = $$cobuechi{directions};
    my $cbnames  = $$cobuechi{names};
    
    my $n = $cbstates->Size;
   
    while ( $unexpanded->Size > 0 ) {
	print "Expand state: (" if $verb eq 4;
	my $weakstate = $unexpanded->Pop;
	my $index     = $weakstate->Second;
	my $state     = $weakstate->First;
	my $cbimage   = $$cbdelta{$state};
	my $image     = Set->new;
	my $false     = Set->new;

	print $state->ToString($cbnames).",".$index.")\n" if $verb eq 4;
	$$names{$weakstate} = $$cbnames{$state} . "_$index";
	$fair->Push($weakstate) if ( ( $index % 2 ) != 0 );

	next unless (defined $cbimage);  # tr is TRUE, we don't have to expand TRUE-tr
	#state is either no alpha-state or even
	if (not(($cbfair->Pick)->IsMember($state)) ||
	    (($index % 2) == 0)) {
	    foreach my $labelpair ( values %{$cbimage} ) {
		my $label = $labelpair->First;
		die if ref($label) ne "UniqSet";
		my $dirdestset    = $labelpair->Second;
		my $newdestset = Set->new;
		my $setsize    = $dirdestset->Size;
		print "LABEL ", $label->ToString, "\n" if $verb eq 4;
		if ( $setsize == 0 ) {# {} represents FALSE?
		    $image->Push(Pair->new($label, $false));
		    print "TR is FALSE\n" if $verb eq 4;
		} else {
		    print "RELEASE : ", $dirdestset->ToString($cbnames), " Index:",
		      $index, "\n" if $verb eq 4;
		    $newdestset = releasewithfair( $dirdestset, $index, 1, $cbnames, $cbfair, $orelease);
		    print "RELEASED: ", $newdestset->ToString($cbnames),"\n" if $verb eq 4;
		}#fi $setsize
		
		#$image->Push( Pair->new( $label, $newdestset ) );
		foreach my $destSet (values %$newdestset) {
		    $image->Push( Pair->new( $label, $destSet ) );
		    print "PUSH TR:". $destSet->ToString($cbnames)."\n" if $verb eq 4;
		    foreach my $dpair (values %$destSet) {
			if ($states->IsMember($dpair->Second) == 0) {
			    $unexpanded->Push($dpair->Second);
			    $states->Push($dpair->Second);
			    print "Add state:", $dpair->Second->ToString($cbnames),"\n"
			       if $verb eq 4;
			}#fi member
		    }#foreach $dpair
		}#foreach $destSet
		print "\n" if $verb eq 4;
	    }#foreach $labelpair
	} else {
	    #fi not fair or even
	    #this is the only way to get delta(state)=FALSE
	    #because the release-fct can't make result in FALSE as long as the input fct is not FALSE
	    print "TR of $$cbnames{$state}_$index is FALSE\n" if $verb eq 4;
	    die "alpha states in odd ranges shouldn't be expanded ";
	}
	#Note: if state fair and odd, delta(state)={}(false)
	#      delta(state)={{}} corresponds to true
	print "\n" if $verb eq 4;
	
	#default image is FALSE
	$$delta{$weakstate} = $image;
	#print "Set delta of ".$weakstate->ToString($names)."\n";
    }#while unexpand not empty
    
    # Some cleanup:
    # Remove states with delta{state}={} (false)
    # and all references to these states
    # be careful: we may end up with delta{state}={{a=1,...},{a=0,FALSE}}
    # how to we store that? e.g. {a=0,{}}
    # delta(s) = {}     ... FALSE (empty disjunction)
    # delta(s,a) = {}   ... FALSE (empty disjunction)
    # delta(s,a) = {{}} ... TRUE  (empty conjunction)
    # delta(s,a) not defined ..TRUE (no restriction on delta(s,a))
    # delta(s) not defined.....TRUE (no restriction on delta(s))
    my $false = Set->new;
    while (1) {
	my $remove = Set->new;
	foreach my $state ( values %{$states} ) {
	    next unless defined $$delta{$state}; #delta is TRUE
	    if ( $$delta{$state}->Size == 0 ) {
		$remove->Push($state);
		print "REMOVE STATE ", $state->ToString($names), "\n";
	    }
	}#foreach $state
	last unless ( $remove->Size > 0 );
	
	foreach my $state ( values %{$states} ) {
	    my $image    = $$delta{$state};
	    next unless defined $image; #delta is TRUE
	    my $newimage = Set->new;
	    my $label2false = Cover->new;
	    my $covered = Cover->new;
	  C: foreach my $lpair ( values %{$image} ) {
		my $label = $lpair->First;
		my $destset    = $lpair->Second;
		my $removalset = Set->new;
		foreach my $dirPair ( values %{$destset} ) {
		    my $nextState = $dirPair->Second;
		    if ($remove->IsMember($nextState)) {
			#remove stateset
			print "Remove: ".$destset->ToString($names)."\n" if $verb eq 4;
			$image->Delete($destset);
			$label2false->Push($label);
			next C;
		    }
		}
		$covered->Push($label);
	    }#foreach $lpair
	    #Add tr to FALSE if necessary
	    $label2false = $label2false->PrimeAndIrredundant;
	    if ($image->Size == 0) { #no valid transition left
		if (($label2false->Size == 1) &&
		    ($label2false->Pick->Size == 0)) { #tr leads to FALSE
		    $$delta{$state} = $false;
		    print "TR of " . $state->ToString($names) . " leads to false.\n";
		} else {
		    foreach my $l (values %$label2false) {
			$image->Push(Pair->new($l, $false));
		    }
		}
	    } else {
		#since we have nondeterminism, we don't have to add tr to FALSE for
		#labels that are already covered by another transition
		$covered = $covered->PrimeAndIrredundant;
	      L: foreach my $l (values %$label2false) {
		    foreach my $c (values %$covered) {
			next L if ($c->IsIncluded($l));
		    }
		    $image->Push(Pair->new($l, $false));
		    #print "Add false image for ".$$names{$state}." and ". $l->ToString."\n";
		}
	    }
	}#foreach $state
	$states->Subtract($remove);
	$fair->Subtract($remove); #we have only a single fairness condition
	foreach my $state ( values %{$remove} ) {
	    delete $$delta{$state};
	    delete $$names{$state};
	}#foreach $state
    }#while(1)
}    # Create2layers

################################################################
#     To Compute the release function for enumerating the
#                 transistion function.
################################################################
sub release {
	my ( $dirstateset, $index, $trex,$names ) = @_;
	my $low = 1;
	if ( $index == 0 ) {
		$low = 0;
	}
	if ( $index == 1 ) {
		if ($trex) {
			$low = 1;
		}
		else {
			$low = 0;
		}
	}
	if ( $index == 2 ) {
		if ($trex) {
			$low = 1;
		}
		else {
			$low = 1;
		}
	}
	my $retset = Set->new( Set->new );
	my $flag   = 1;
	my $cover = Set->new(LTL->new("TRUE")); #necessary?
	
	foreach my $dirstate ( values %$dirstateset ) {
		my $tempset = Set->new;
		my $direction = $dirstate->First;
		my $state = $dirstate->Second;
		
		if ($state->IsEqual($cover)) {
			print $direction->ToString."-".$state->ToString."\n";
			my $newstate = Pair->new( $state, 1);
			$tempset->Push( Set->new( Pair->new( $direction, $newstate ) ) );
		} else {
			for ( my $j = $index ; $j >= $index - $low ; $j-- ) {			
				my $newstate = Pair->new( $state, $j);
				$tempset->Push( Set->new( Pair->new( $direction, $newstate ) ) ); # (1,n1_1) + (2,n2_1) +..
			}
		}
			if ($flag) {
				$retset = $tempset;
				$flag   = 0;
#				print "EXPANDED:", $retset->ToString($names),"\n";
			} else {
				$retset = expproduct( $retset, $tempset );
#				print "EXPAND  :", $tempset->ToString($names),"\n";
#				print "EXPANDED:", $retset->ToString($names),"\n";
			}
	}
	return $retset;
}    # release

################################################################
#    To Compute the release function for enumerating the
#    transistion function. Edges to deadend states are ignored.
################################################################
sub releasewithfair {
	my ( $dirstateset, $index, $trex, $names, $fair, $orelease ) = @_;
	my $low = 1;
	if ( $index == 0 ) {
		$low = 0;
	}
	if ( $index == 1 ) {
		if ($trex) {
			$low = 1;
		}
		else {
			$low = 0;
		}
	}
	if ( $index == 2 ) {
		if ($trex) {
			$low = 1;
		}
		else {
			$low = 1;
		}
	}
	my $retset = Set->new( Set->new );
	my $flag   = 1;
	my $cover = Set->new(LTL->new("TRUE"));
	
	foreach my $dirstate ( values %$dirstateset ) {
		my $tempset = Set->new;
		my $direction = $dirstate->First;
		my $state = $dirstate->Second;
	
		#state is either no alpha-state or even
		my $alphastate = ( $fair->Pick )->IsMember($state);

		if ($state->IsEqual($cover)) {
			print $direction->ToString."-".$state->ToString."\n";
			my $newstate = Pair->new( $state, 1);
			$tempset->Push( Set->new( Pair->new( $direction, $newstate ) ) );
			die; #shouldn't be reached anymore
		} else {
			for ( my $j = $index ; $j >= $index - $low ; $j-- ) {
				next if ($alphastate and ( ($j % 2 ) == 1 ) ); #skip because delta(s)=false
				next if ( $orelease and
					  (($index % 2) == 1) and
					  (not $alphastate) and
					  $j != $index); #stay in accepting layer if possible
				my $newstate = Pair->new( $state, $j);
				$tempset->Push( Set->new( Pair->new( $direction, $newstate ) ) ); # (1,n1_1) + (2,n2_1) +..
			}
			#TODO: think about possible empty $tempset? what does it mean?
		}
			if ($flag) {
				$retset = $tempset;
				$flag   = 0;
#				print "EXPANDED:", $retset->ToString($names),"\n";
			} else {
				$retset = expproduct( $retset, $tempset );
#				print "EXPAND  :", $tempset->ToString($names),"\n";
#				print "EXPANDED:", $retset->ToString($names),"\n";
			}
	}
	return $retset;
}    # release


################################################################################
# Computes all satisfying assignments of /\ delta(s,l) with s in $stateset
################################################################################
sub SatisfyingSets {
    my ($self, $stateset, $label, $mem) = @_;
    #build hashkey
    my @a = $stateset->Sort(sub{$Set::a <=> $Set::b});
#    my @b = $label->Sort(sub{$Set::a <=> $Set::b});
    my $setkey = join(".",@a);
#    my $labelkey = join(".",@b);
    my $labelkey = $label;
    $setkey .= ".".$labelkey;
    my $set = 1;
    if (defined $$mem{$setkey}) {
	$set = 0;
	return $$mem{$setkey};
    }
    my $ssatset = Set->new();
    my $ssflag = 1;

  NSTATE: foreach my $astate ( values %$stateset ) {
	#---------Satisfy($self, $astate, $label, $sat)----
	#print $astate->ToString($$self{names})."\n";
	my $ssattemp = Set->new;
	my $key = $astate.".".$labelkey;
	my $false = 0;
	if (defined $$mem{$key}) {
	    $ssattemp = $$mem{$key};
	} else {
	    my $delta = $$self{delta};
	    # ssattemp = \/ delta($astate, l) s.t. l subset of $label
	    # e.g. ssattemp = (1,s1) + (2,s2)*(1,s1) + (2,s4)*(1,s3)*(2,s3)
	    my $image = $$delta{$astate};
	    my $false = 0;
	    foreach my $lpair ( values %{$image} ) {
		if ( ref($lpair) eq ref(Set->new) ) { #$lpair->Size has to be 0
		    die if ($lpair->Size != 0);
		    $ssattemp->Push(Set->new);
		    next;
		}
		next unless $lpair->First->IsIncluded($label); #label matches
		if ($lpair->Second->Size == 0) {
		    $false = 1;
		} else {
		    $ssattemp->Push( $lpair->Second );
		}
	    }
	    $ssattemp->Push(Set->new) if ($ssattemp->Size == 0 && $false == 1);
	    $$mem{$key} = $ssattemp->Clone;
	}
	#---------Satisfy($self, $astate, $label, $sat)----
	
	next NSTATE unless ($ssattemp->Size != 0);
	if ($ssflag) {
	    $ssatset = $ssattemp->Clone;
	    $ssflag  = 0;
	} else {
	    # compute /\ s in S: ssattemp(s, label)
	    $ssatset = expproductwithfalse( $ssatset, $ssattemp );
	}
    }			#foreach $astate

    #remove redundant entries (superset)
    # e.g. (1,s1)*(2,s2) + (1,s1)*(2,s2)*(3,s3) -> remove the second -> bring nix
    if ($set == 1) {
	$$mem{$setkey} = $ssatset;
    } else {
	unless ($$mem{$setkey}->IsEqualDeep($ssatset)) {
	    print "M:".$$mem{$setkey}->ToString($$self{names})."\n";
	    print "S:".$ssatset->ToString($$self{names})."\n";
	    die;
	}
    }
    return $ssatset;
}

################################################################################
#
################################################################################
sub CreateMHLevel {
    my $startTime = (times)[0];
    my ($self, $verb, $nbt, $expand, $mem, $num, $sat, $simul) = @_;
    die unless ref($expand) eq 'Set';
    die unless ref($mem) eq 'HASH';
    die unless ref($num) eq 'HASH';
    die unless ref($sat) eq 'HASH';
    my $states = $$nbt{states};
    my $delta = $$nbt{delta};
    my $init =  $$nbt{init};
    my $fair = $$nbt{fair}->Pick;
    my $names = $$nbt{names};
    my $letters = $$nbt{directions}->Second;
    my $directions = $$nbt{directions}->First;

    my $astates    = $$self{states};
    my $ainit      = $$self{init};
    my $adelta     = $$self{delta};
    my $adirections= $$self{directions}->First;
    my $aletters   = $$self{directions}->Second;
    my $afair      = $$self{fair};
    my $anames     = $$self{names};

    print "\n";
    my $trueset = 0;
    my $truestate = undef;
    my $newExpand = Set->new;
    my $stateCnt = $states->Size;
    while ( $expand->Size != 0 ) {
	#print "No of states:",$states->Size."\n";
	#print "No of expand:",$expand->Size."\n";
 	my $start = times();
 	my $state = $expand->Pop;
 	my $stateset   = $state->First; #S
 	my $obligation = $state->Second; #O
 	my $oflag      = $obligation->Size == 0;
 	my $image      = Set->new;
	$fair->Push($state) if $oflag; #all states without obligations are fair
   	print "-- Analyzing state ".$$names{$state}.": S=", $stateset->ToString($anames),
	  " O=",$obligation->ToString($anames),"\n" if ($DEBUG == 3);

        #FORALL LABELS of state (S,O) calculate PAIR_SAT((S,O),label)
        # SAT(S,label) = {x in 2^DxQ | forall all q in S: x satisfies delta(q,label)}
      LLOOP: foreach my $label ( values %$letters ) {
            my $ssatset = SatisfyingSets($self, $stateset, $label, $sat);
            my $osatset = SatisfyingSets($self, $obligation, $label, $sat);
           print "L ".$label->ToString."\n" if ($DEBUG == 3);
           print "S ".$ssatset->ToString($$self{names})."\n" if ($DEBUG == 3);
           print "O ".$osatset->ToString($$self{names})."\n" if ($DEBUG == 3);
            #Check if True trap is necessary
            my $trueset = 0;
            if ($ssatset->Size == 0) {
                $trueset = 1;
#               print "SSet is TRUE\n";
            } else {
                if ($ssatset->Pick->Size == 0) { #delta(s,l) = {{}} = FALSE
                    next LLOOP; #compute delta for the next label
                }
            }
            #Create True trap state if necessary
            if ($trueset) {
                my $newstate = Pair->new( Set->new, Set->new );
                $newstate = hashing($newstate,$states,$newExpand,$mem,$num,$simul,$anames);
                print "NEWSTATE: " . $newstate->ToString($anames) ."\n" if ($DEBUG == 3);
                $newExpand->Delete($newstate);
                $$delta{$newstate} = Set->new( Pair->new( Set->new, Set->new(Pair->new(Set->new,$newstate)) ) );
                $$names{$newstate} = "fairstate";
                $fair->Push($newstate);
                $image->Push( Pair->new( $label, Set->new(Pair->new(Set->new,$newstate)) ) );
                next LLOOP;     #compute delta for the next label
            }
            
            #add consistancy check if necessary
            if ($oflag) {       # Obligation was empty
                foreach my $dsset ( values %$ssatset ) {
		    my $dirstates = Set->new;
                    foreach my $direction ( values %$directions) {
                        my $sset = $dsset->IsIncludedFirst($direction); # S
                        #what if ($sset->Size == 0)? 
                        #=> $newstate = Pair->new( Set->new, Set->new ) TRUESTATE
                        my $newstate =  Pair->new( $sset, $sset->Difference( $afair->Pick ) );
			$newstate = hashing($newstate,$states,$newExpand,$mem,$num,$simul,$anames);
			if (defined $newstate) { #state is consistent
			    unless (defined $$names{$newstate}) {
				#add a temporary name
				$$names{$newstate} = "toexpand$stateCnt";
				$stateCnt++;
				print "NEWSTATE: " . $newstate->ToString($anames) ."\n" if ($DEBUG == 3);
			    }
			    $dirstates->Push( Pair->new( $direction, $newstate ) );
			} else {
			    print "INCONSISTANT STATE: " . $newstate->ToString($anames) ."\n" if $verb > 2;
			}
                    }           #foreach $direction
                    #simplify representation of $dirstates
		    $dirstates = SimplifyConjunct($dirstates);
                    $image->Push( Pair->new( $label, $dirstates ) ) unless ($dirstates->Size < 1);
#                   print "PUSH: " . $label->ToString . "->" . $dirstates->ToString($anames) . "\n";
                }   #foreach $sset
            } else {
                my $newdestsets = Set->new;
                #combine S and O sets; Note: S,O in (D x Q) !
              OLOOP: foreach my $sset ( values %$ssatset ) {
                    if ( $osatset->Size == 0 ) {
                        #print "Obligation is true\n" if $verb > 2;
                        my $newdest = Pair->new( $sset, $osatset );
                        $newdestsets->Push($newdest);
                        next OLOOP;
                    }
                    if ( $osatset->Pick->Size == 0 ) {
                        #print "Obligation is false\n";
                        die;
                    }
                    my $dflag = 1;
                    foreach my $oset ( values %$osatset ) {
                        next unless $oset->IsIncluded($sset);
                        my $newdest = Pair->new( $sset, $oset );
                        $newdestsets->Push($newdest);
                        $dflag = 0;
                    }           #foreach $oset
                    die "Obligation set not found for stateset ", $sset->ToString, " ", $osatset->ToString, "\n" if $dflag;
                }               #foreach $sset
                
                foreach my $newdest ( values %$newdestsets ) {
                    my $dirstates = Set->new;
                    foreach my $direction ( values %$directions ) {
                        my $newstate = $newdest->IsIncludedFirst($direction); #(S,O)
			my $oset = $newstate->Second->Difference( $afair->Pick );
			$newstate = Pair->new( $newstate->First , $oset );
			my $tmp = $newstate;
			$newstate = hashing($newstate,$states,$newExpand,$mem,$num,$simul,$anames);
			if (defined $newstate) { #state is consistent
			    unless (defined $$names{$newstate}) {
				$$names{$newstate} = "toexpand$stateCnt";
				$stateCnt++;
			    }
			    print "NEWSTATE: " . $newstate . " " . $newstate->ToString($anames)
			      ."\n" if ($DEBUG == 3);
			    $dirstates->Push( Pair->new( $direction, $newstate ) );
			} else {
			    print "INCONSISTANT STATE: " .
			      $tmp->ToString($anames) ."\n" if ($DEBUG == 3);
			}
                    }           #foreach $direction
                    #simplify representation of $dirstates
		    $dirstates = SimplifyConjunct($dirstates);
                    $image->Push( Pair->new( $label, $dirstates ) ) unless ($dirstates->Size < 1);
                }               #foreach $newdest
            }                   #endelse obligation not empty
        } #foreach $label

        #simplify image
#        $image = CoBuechiTree::SimplifyLabelDestinationSet($image);
        #add transition relation
        $$delta{$state} = $image;
                
        #add name for the new state (S,O)
        my $namst = "";
        foreach my $astate ( values %$stateset ) {
            $namst .= $$anames{$astate} if defined($$anames{$astate});
            if ($namst eq "") {
                #print "NO NAME: " .$astate->ToString;
            }
        }
        if ($obligation->Size > 0) {
            $namst .= "-";
        }
        foreach my $astate ( values %$obligation ) {
            $namst .= $$anames{$astate} if defined($$anames{$astate});
        }
        if ( $namst eq "" ) {
            $namst = "fairstate";
        }
        $$names{$state} = $namst;
                
        #print "-- Add TR of: " . $namst . "->" . $image->ToString($anames) . "\n" if $verb > 2;
                
        my $end = times();
    }#  while ( $expand->Size != 0 )

    foreach (values %$newExpand) {
        $expand->Push($_);
    }
    my $endTime = (times)[0];
    printf "MH time: %.2f seconds\n", $endTime - $startTime;
    return (($expand->Size == 0)?1:0);
} #CreateMHLevel


sub SimplifyConjunct {
    my $conjunct = shift;
    my %todest = ();
    my $dests = Set->new;
    
    foreach my $ddpair (values %$conjunct) {
	my $dir = $ddpair->First;
	my $dest = $ddpair->Second;
	unless (exists $todest{$dest}) {
	    $todest{$dest} = Cover->new;
	}
#	print $dir->ToString,"\n";
#	$todest{$dest}->Push($dir->Set);
	$todest{$dest}->Push($dir);
	$dests->Push($dest);
    }

    my $newconjunct = Set->new;
    foreach my $dest (values %$dests) {
	my $dirs = $todest{$dest}->PrimeAndIrredundant;
	foreach my $dir (values %$dirs) {
	    $dir = UniqSet->newFromSet($dir);
	    $newconjunct->Push(Pair->new($dir,$dest));
	}
    }
    return $newconjunct;
}

###########################################################################
# To derive the Buechi automaton from the weak alternating tree automaton
#	using an algorithm of KV based on Miyano and Hayashi procedure.
###########################################################################
sub ToBuechi {
    #Todo: reuse of lower ranks
    my ($self, $verb, $num, $simul) = @_;
    die unless ref($num) eq 'HASH';
    $verb = 1 unless defined $verb;
    my $astates    = $$self{states};
    my $ainit      = $$self{init};
    my $anames     = $$self{names};
    
    print "-- from AlternatingTree to BuechiALTree --\n" if $verb > 1;
    die "No initial states found\n" if ($ainit->Size == 0);
    
    my %names = ();
    my %mem = ();
    my %sat = ();
    my $fair = Set->new(Set->new); #we have a single fairness constraint
    my $unexpanded = Set->new;	#set of states that need to be expanded
    my $initialstate = Pair->new( $ainit, Set->new ); # ({init},{})
    $names{$initialstate} = "toexpand\n";
    my $states = Set->new;
    my $init = Set->new;
    #make a new states and add it to unexpanded
    $initialstate = hashing( $initialstate, $states, $unexpanded, \%mem, $num);
    $init->Push($initialstate);
    my $buechi = BuechiALTree->new(states => $states,
				   directions => $$self{directions},
				   init => $init,
				   fair => $fair,
				   names  => \%names);

    while ( $unexpanded->Size != 0 ) {
	
	$self->CreateMHLevel($verb, $buechi, $unexpanded, \%mem, $num,
			     \%sat, $simul);
    }
    return $buechi;
}

#####################################################################
# To check the consistancy of an NBT-state (S,O).
# (S,O) is conistent if forall (q,i),(q',i') in S: 
# if (q == q') then (i == i')
# If the state is inconsistent (e.g. i < i') and (q',i') simulate 
# (q,i) we remove (q',i'). This means we are allowed to just to lower
# ranks other certain conditions.
# If (q',i') does not simulate (q,i) the state is stays inconsistent.
# Returns 0 is the state is inconsistent,
# 1 if the state is consistent, and
# 2 if the state was made consistent.
#####################################################################
sub checkAndMakeConsistent {
	my ($state,$simul,$names) = @_;
	my $sset = $state->First;
	my $oset = $state->Second;
	my $ssize = $sset->Size;
	my $osize = $oset->Size;
	$simul = Set->new unless defined $simul;

# 	print "STATE:".$state->ToString($names)."\n";
	my $toSubtract = Set->new;
	foreach my $pair0 ( values %{$sset} ) {
		my $q0 = $pair0->First;
		my $i0 = $pair0->Second;
		foreach my $pair1 (values %{$sset}) {
			my $q1 = $pair1->First;
			my $i1 = $pair1->Second;
			if ( $q0->IsEqual($q1) and ($i0 ne $i1)) {
			    #make state consistent!!
			    if ($i0 < $i1) {
				$toSubtract->Push($pair1);
			    } else { #($i0 > $i1)
				$toSubtract->Push($pair0);
			    }
			} else {
			    #produces unrealiability?
			    if ($simul->IsMember(Pair->new($pair0,$pair1)) &&
				($oset->Size == 0 ||
				 (not $oset->IsMember($pair1)) ||
				 $oset->IsMember($pair0))) {
				#$pair0 is simulated by $pair1 -> delete $pair1
				$toSubtract->Push($pair1);
# 				print "RemoveS:".$pair1->ToString($names)." by ";
# 				print $pair0->ToString($names)."\n";

			    }
			}
		    }
	}
	if ($toSubtract->Size > 0) {
	    $sset->Subtract($toSubtract);
	    $oset->Subtract($toSubtract);
# 	    print "NEWSTATE:".$state->ToString($names)."\n";
	    die "newstate is empty" if (($ssize != 0) &&($sset->Size == 0));
#	    die "new obligation is empty" if (($osize != 0) && ($oset->Size == 0));
	    return 2;
	}
	return 1;
}

#####################################################################
# To compute the product of two formulae in DNF form used in ToBuechi
#####################################################################
sub expproduct {
	my ( $first, $second ) = @_;
	if ( $first->Size == 0 ) {
	    die "TODO: inconsistency in DNF interpretation\n";
	    return $first;
	}
	if ( $second->Size == 0 ) {
	    die "TODO: inconsistency in DNF interpretation\n";
	    return $second;
	}
	my $retset = Set->new;
	foreach my $sset ( values %{$second} ) {
		foreach my $fset ( values %{$first} ) {
			$retset->Push( $fset->Union($sset) );
		}
	}
	return $retset;
}    #expproduct

#####################################################################
# To compute the product of two formulae in DNF form used in ToBuechi
# DNF = Set of Set of atom 
# {}....TRUE
# {{}}..FALSE
# {{a},{b},{c}} = a + b + c
# {{a,b,c}}     = a * b * c
#  e.g. {{a,b},{c}} x {{a},{b},{}} = {{a,b},{a,c},{b,c}}
#####################################################################
sub expproductwithfalse {
	my ( $first, $second ) = @_;
	if ( $first->Size == 0 ) { #true
		return $second;
	}
	if ( $second->Size == 0 ) { #true
		return $first;
	}
	my $retset = Set->new;
	foreach my $sset ( values %{$second} ) {
		foreach my $fset ( values %{$first} ) {
			if ( $fset->Size == 0 ) {
				$retset->Push( $fset );
			} elsif ( $sset->Size == 0 ) {
				$retset->Push( $sset );
			} else {
				$retset->Push( $fset->Union($sset) );
			}
		}
	}
	return $retset;
}    #expproduct



######################################################################
# Calculate a game between the environment and the system. The env
# controlls the universality and the directions. The system controlls
# the nondeterminism and the transition labeling.
# The aim of the env is too force circle visiting not accepting states
# infinitely often, or to end in a FALSE transition (empty set).
# If the env wins the game the formula is unrealizable, otherwise we
# don't know. However all states in the winning region of env can be
# removed from the automaton, since the env can force from those
# states a path in all runs that avoid all accepting states.
######################################################################
sub Winning {
    my $self = shift;
    my %params = @_;
    my $oldWinning =  Set->new;
    $oldWinning = $params{oldwin} if defined $params{oldwin};
    my $states = $$self{states};
    my $fair   = $$self{fair}->Pick;
    my $notfair = $states->Difference($fair);

    # MG (not fair) = nu Z. notFair * MX(Z) is too strong
    # not (MpG true under fairness) is sufficient with 
    # MpX = X forced by the protagonist (system)
    # MaX = X forced by the antagnoist (environment)
    # MpG true under fairness = nu Y.MpX( mu Z. Y * (fair + MpX Z) )
    # not (MpG true under fairness) =
    # not (nu Y.MpX( mu Z. Y * (fair + MpX Z))) =
    # mu Y. MaX( nu Z. Y + (notFair * MaX Z))

    my $nY = $oldWinning->Clone;
    my $Y = $states->Clone;
    while (not $Y->IsEqual($nY)) {
	$Y = $nY;
	my $nZ = $states->Clone;
	my $Z = Set->new;
	while (not $Z->IsEqual($nZ)) {
	    $Z = $nZ;
	    my $mx = $self->MX($Z);
	    $nZ = $mx->Intersection($notfair);
	    $nZ = $nZ->Union($Y);
	}
	$nY = $self->MX($Z);
    }
    return $Y;
#     # MG (not fair) = nu Z. notFair * MX(Z)
#     my $nZ = $states->Clone;
#     my $Z = Set->new;
#     while (not $Z->IsEqual($nZ)) {
# 	$Z = $nZ;
# 	my $mx = $self->MX($Z);
# 	#print "-- MX:".$mx->ToString($$self{names})."\n";
# 	$nZ = $mx->Intersection($notfair);
# 	#print "-- nZ:".$nZ->ToString($$self{names})."\n";
#     }

#     # winning MF MG(not fair)
#     $Z = Set->new;
#     while (not $Z->IsEqual($nZ)) {
# 	$Z = $nZ;
# 	$nZ = $self->MX($Z);
#     }
#     #print "-- nZ:".$nZ->ToString($$self{names})."\n";
#    return $nZ;
}

######################################################################
# Computes MX(target), which are all states that can be forced by the
# protagonist (environment) to reach in the next step one of the
# target states or a FALSE transition.
# Note: The antagonist chooses the transition and the protagonist
# chooses the direction. The universality belongs to the protagonist.
# The nondeterminism to the antagonist.
#
# All unmentioned labels leave the automaton, so states with
# unmentioned labels cannot be force to visit the target states.
######################################################################
sub MX {
    my ($self, $targetStates) = @_;
    my $states = $$self{states};
    my $init   = $$self{init};
    my $delta  = $$self{delta};
    my $names  = $$self{names};
    
    my $mxStates = Set->new;
  ST: foreach my $state (values %$states) {
 	my $image = $$delta{$state};
 	my $covered = Cover->new;
	if ($image->Size == 0) { #FALSE tr
	    $mxStates->Push($state);
	    next;
	}
      LP: foreach my $labeledPair (values %$image) {
 	    $covered->Push($labeledPair->First);
 	    my $transitions = $labeledPair->Second;
	    next LP if ($transitions->Size == 0); #FALSE tr
	  C: foreach my $pair (values %$transitions) {
		next LP if ($targetStates->IsMember($pair->Second));
	    }
	    #this transition cannot be force to the target
	    next ST;
	}
 	#state can be forced to $targetStates forall mentioned labels
 	$covered = $covered->PrimeAndIrredundant;
 	if (($covered->Size > 0) &&
	    ($covered->Pick->Size == 0)) { #all labels are covered
 	    $mxStates->Push($state);
 	}	
    }
    return $mxStates;
}

#####################################################################
# Takes a set of states and remove those states from the automaton.
# All transition leading to one of those states are redirected to
# false.
#####################################################################
sub Subtract {
    my ($self, $subtract) = @_;
    my $states = $$self{states};
    my $delta  = $$self{delta};
    my $names  = $$self{names};
    my $init   = $$self{init};
    my $fair   = $$self{fair};
    my $false = Set->new;
    
    return if ($subtract->Size == 0);
    
    $states->Subtract($subtract);
    $init->Subtract($subtract);
    foreach my $state (values %$subtract) {
	delete $$delta{$state};
	delete $$names{$state};
    }
    foreach (values %$fair) {
	$_->Subtract($subtract);
    }

    foreach my $state (values %$states) {
	#print "S:".$$names{$state}."\n";
	next unless defined $$delta{$state}; #image = true
	my $image = $$delta{$state};
	next if $image->Size eq 0; #image = false
	my $label2false = Cover->new;
	my $covered = Cover->new;
      T: foreach my $lpair (values %$image) {
	    my $label = $lpair->First;
	    my $transitions = $lpair->Second;
	    #Note: if tr is false ($transitions->Size eq 0)
	    #we skip the following loop
	  C: foreach my $dspair (values %$transitions) {
		#since we have a conjunct of dir-state-pairs, the transition
		#leads to FALSE as soon as one direction leads to FALSE
		if ($subtract->IsMember($dspair->Second)) {
		    $image->Delete($lpair);
		    $label2false->Push($label);
		    next T;
		}
	    } #C
	    $covered->Push($label);#add only labels that still exist
	}#lpair
	
#	$label2false = $label2false->PrimeAndIrredundant;
	#print "L:".$label2false->ToString($names)."\n";
	#print "C:".$covered->ToString($names)."\n";
	if ($image->Size == 0) { #no valid transition left
	    if (($label2false->Size == 1) &&
		($label2false->Pick->Size == 0)) { #tr leads to FALSE
		$$delta{$state} = $false;
		print "TR of " . $state->ToString($names) . " leads to false.\n";
	    } else {
		foreach my $l (values %$label2false) {
		    $image->Push(Pair->new($l, $false));
		}
	    }
	} else {
	    #since we have nondeterminism, we don't have to add tr to FALSE for
	    #labels that are already covered by another transition
#	    $covered = $covered->PrimeAndIrredundant;
	  L: foreach my $l (values %$label2false) {
		foreach my $c (values %$covered) {
		    next L if ($c->IsIncluded($l));
		}
		$image->Push(Pair->new($l, $false));
		#print "Add false image for ".$$names{$state}." and ". $l->ToString."\n";
	    }
	}
    }#state
}
#####################################################################
# Minimizes the automaton by removing states from which the
# environment can force a path that avoids all accepting states.
# Those states fulfill MG(not fair).
#####################################################################
sub LostStatesMinimization {
        my $self = shift;
	my %params = @_;
	my $verb = 1;
	my $lostStates = Set->new;
	my $rank = 1; #default
	$verb = $params{verbose} if defined $params{verbose};
	$lostStates = $params{lost} if defined $params{lost};
	$rank = $params{rank} if defined $params{rank};
	
	my $states = $$self{states};
	my $init  = $$self{init};
	my $delta = $$self{delta};
	my $names = $$self{names};
	my $directions = $$self{directions};
	my $labels = $directions->Second;
	my $fair = $$self{fair};
	print "-- Minimize Alternating Tree Automaton --\n" if $verb > 1;

	my $win = $self->Winning(oldwin => $lostStates);
	
	if ($init->IsIncluded($win)) {
	    print "Language of this AWT (rank $rank) is empty\n";
	    print "Remove lost states in the AWT..\n";
	    print $win->ToString($names)."\n";
	    $self->Subtract($win);
	    return "";
	} else {
	    print "Remove lost states in the AWT..\n";
	    print $win->ToString($names)."\n";
	    $self->Subtract($win);
	    print "Stats AWT: ", $self->Stats, "\n";
	    print "Remove lost states done\n";
	}

	return 1;
} #Minimization

######################################################################
# Removes simulation requivalent states
######################################################################
sub RemoveSimulationEquivalentStates {
    my $self = shift;
    my %params = @_;
    my $states = $$self{states};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $names = $$self{names};
    my $inverse;
    my $simul;
    if (defined $params{inverse}) {
	$inverse = $params{inverse};
    } else {
	$inverse = InvertDelta($states, $delta);
    }
    if (defined $params{simul}) {
	$simul = $params{simul};
    } else {
	$simul = $self->ComputeDirectSimulationRelation( inverse => $inverse );
	die "ok";
    }
    print $simul->ToString($names)."\n";

    # Simplify the automaton.
    # Find direct-simulation equivalent states.
    foreach my $pair (values %{$simul}) {
	my $p = $pair->First;
	my $q = $pair->Second;
	# Make sure neither state has been removed yet.
	next unless $states->IsMember($p) and $states->IsMember($q);
	my $swapped = Pair->new($q,$p);
	next unless $simul->IsMember($swapped);
	# Theorem applies.
	#don't delete entries here because we loop over them
	#$simul->Delete($pair,$swapped);
	
	#Throw away p and connect its predecessors to q.
	#if the states are Pairs of UCT-state and rank, throw away the state
	#with the higher rank
	if ((ref($p) eq 'Pair') &&
	    (ref($q) eq 'Pair') &&
	    ($p->Second < $q->Second)) { #flip p and q
	    my $tmp = $p;
	    $p = $q;
	    $q = $tmp;
	}

	print "$$names{$p} is direct-simulation equivalent to $$names{$q}\n"
	  if $DEBUG > 0;
	# Update inverse image of successors.
	my $pimage = $$delta{$p};
	foreach my $s (values %$pimage) {
	    my $slabel = $s->First;
	    my $succset = $s->Second;
	    foreach my $sdirstate (values %$succset) {
		my $sstate = $sdirstate->Second;
		next if $sstate eq $p;
		if (not defined $$inverse{$sstate}) {
		    print $sstate->ToString($names)."\n";
		    die;
		}
		$$inverse{$sstate}->Delete(Pair->new($slabel,$p));
	    }
	}
	delete $$delta{$p};
	
	# Update image of predecessors.
	#print "PI:".$$inverse{$p}->ToString($names)."\n";
 	foreach my $s (values %{$$inverse{$p}}) {
 	    my $slabel = $s->First;
 	    my $sstate = $s->Second;
 	    next if $sstate eq $p;
	    #print "STATE:".$sstate->ToString($names)."\n";
	    my $simage = $$delta{$sstate};
 	    foreach my $lpair (values %$simage) {
 		next unless $lpair->First->IsEqual($slabel);
		my $succset =  $lpair->Second;
		my $succstates = $succset->Second;
		next unless $succstates->IsMember($p);
		$simage->Delete($lpair); #delete pair from image
#		print "SUCCO:". $succset->ToString($names)."\n";
		$succset = ReplaceStateInConjunct($succset, $p, $q);
#		print "SUCCN:". $succset->ToString($names)."\n";
		$simage->Push(Pair->new($lpair->First, $succset));
		#$succset->Delete($p); #for the word-case
		#$succset->Push($q);   #for the word-case
 	    }
 	    $$inverse{$q}->Push($s);
 	}
	delete $$inverse{$p};
	
  	# Update the fair sets.
  	foreach my $fairset (values %{$fair}) {
  	    $fairset->Delete($p);
  	}
  	# Remove state p from automaton.
  	if ($init->IsMember($p)) {
  	    $init->Delete($p);
  	    $init->Push($q);
  	}
#  	delete $$names{$p};
  	$states->Delete($p);
    }#foreach my $pair (values %{$simul})

    #remove pairs including removed states - not necessary
    foreach (values %$simul) {
	my $u = $_->First;
	my $v = $_->Second;
	unless ($states->IsMember($u) and $states->IsMember($v)) {
	    $simul->Delete($_);
	}
    }    
}

######################################################################
# Takes a set of direction-state-pairs and two states p and q, and
# replaces all p's by q.
######################################################################
sub ReplaceStateInConjunct {
    my ($conjunct, $p, $q) = @_;
    my $cover = Cover->new;
    my $newconjunct = Set->new;
    
    foreach my $dspair (values %$conjunct) {
	if (($dspair->Second == $p) ||
	    ($dspair->Second == $q)) {
	    $cover->Push($dspair->First->Set);
	} else {
	    $newconjunct->Push($dspair);
	}
    }
    if ($cover->Size > 1) {
	$cover = $cover->PrimeAndIrredundant;
    }
    foreach my $dir (values %$cover) {
	$dir = UniqSet->newFromSet($dir);
	$newconjunct->Push(Pair->new($dir, $q));
    }
    return $newconjunct;
}

######################################################################
# Apply direct simulation minimization to an automaton.
######################################################################
sub DirectSimulationMinimization {
    my $self = shift;
    my %params = @_;
    my $oldSim = $params{oldSim};
    $oldSim = Set->new unless defined $oldSim;
    
    my $states = $$self{states};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $names = $$self{names};
    my $directions = $$self{directions}->First;
    my $inverse = InvertDelta($states,$delta);
    my $simul = $self->ComputeDirectSimulationRelation(inverse => $inverse,
						       oldSim => $oldSim);
    print "SIMULATION:\n" if $DEBUG > 0;
    print $simul->ToString($names)." ".$simul->Size."\n" if $DEBUG > 0;

    #remove direct-simulation equivalent states
    $self->RemoveSimulationEquivalentStates(simul => $simul,
					    inverse => $inverse);

    #Apply Theorem 4
    #If p is simulated by q, we can remove (d,q) in all conjuncts
    #in which (d,p) appears. We can change (d1,q), if there exists
    #a (d2,p) with d1->d2 (e.g. d1={r=1} and d2={}=true), to (d3,q)
    #with d3=d1*!d2. Since we store only conjuncts of directions we
    #could probably increase the number of disjuncts in delta. So
    #only use this simplification if the distance between d1 and d2
    #is 1 (they differ only in 1 AP). This is still useful because
    #it can speed up the MH construction.
    foreach my $pair (values %$simul) {
	my $u = $pair->First;
	my $v = $pair->Second;
	my $uinverse = $$inverse{$u};
	my $vinverse = $$inverse{$v};
	print "-- Pair:".$u->ToString($names)." ".$v->ToString($names)."\n";
	next unless (defined $uinverse && defined $vinverse);

	#Find conjunct in which $u and $v occur
	my $affected = Set->new;
	foreach my $upair (values %{$uinverse}) {
	    my $ulabel = $upair->First;
	    my $upred  = $upair->Second;
	    foreach my $vpair (values %{$vinverse}) {
		my $vlabel = $vpair->First;
		my $vpred  = $vpair->Second;
		next unless $ulabel->IsEqual($vlabel);
		next unless $upred->IsEqual($vpred);
		$affected->Push($upred);
	    }
	}

	#Apply Theorem
	foreach my $state (values %$affected) {
	    my $image = $$delta{$state};
	    #print "S:".$state->ToString($names)."->";
	    #print "I:".$image->ToString($names)."\n";
	    foreach my $lpair (values %$image) {
		my $conjunct = $lpair->Second;
		#print "C:".$conjunct->ToString($names)."\n";
		my $du = $conjunct->FindSecond($u);
		my $dv = $conjunct->FindSecond($v);
		next unless (defined $du and defined $dv);
		#print $du->ToString($names)." and ";
		#print $dv->ToString($names)."\n";

		#Be more careful about shared transitions
		#Pairs are unique therefore don't use
		#'$dv->First->Push($invert)'
		# make new imagesets!!
		if ($du->First->IsIncluded($dv->First)) { #or equal
		    print "Remove second in ".$dv->ToString($names)."\n";
		    $conjunct->Delete($dv);
		} elsif ($dv->First->IsIncluded($du->First)) {
 		    print "Restrict second in ".$dv->ToString($names)."\n";
  		    my $diff = $du->First->Difference($dv->First);
  		    next unless ($diff->Size == 1);
		    $conjunct->Delete($dv);
  		    my $invert = $diff->Pick->Negate;
		    my $dir = $dv->First->Set;
		    $dir->Push($invert);
		    $dir = UniqSet->newFromSet($dir);
 		    $conjunct->Push(Pair->new($dir,$dv->Second));
  		    print "Newdir:". $dir->ToString($names)."\n";
		} else {
		    #print "Disjoint\n";
		}
	    }
	}
    }

    #Apply Theorem 5
    #Check if there are simulating conjuncts,e.g. for the word case
    #delta(s,a)={{s1,s2},{s3,s4,s5}} if s3,s4, and s5 are simulated by s1 or s2 then
    #L({s1,s2} >= L{s3,s4,s5} and we can remove {s3,s4,s5}.
    #For the tree case it is more difficult, e.g.,
    #delta(s,a)={{(d1,s1),(d2,s2)},{(d3,s3),(d4,s4),(d5,s5)}}
    #The question is when is L({(d1,s1),(d2,s2)}) <= L({(d3,s3),(d4,s4),(d5,s5)})?
    #If we can find forall d and forall (di,si) with d->di a pair (dj,sj) sucht that
    # d->dj and sj simulates si.
    foreach my $state (values %$states) {
 	my $image = $$delta{$state};
	my $removals = Set->new;
 	foreach my $lpair1 (values %$image) {
 	    my $l1 = $lpair1->First;
 	    my $C1 = $lpair1->Second;
	    foreach my $lpair2 (values %$image) {
		next if $lpair1 eq $lpair2;
		my $l2 = $lpair2->First;
		my $C2 = $lpair2->Second;
		next unless ($l1->IsIncluded($l2)); #or equal
		next unless ($self->IsC1DirectSimulatingC2($C1,$C2,$simul));
		$removals->Push($lpair2);
		#print "--------------------\n";
		#print "Remove ", $C2->ToString($names),"\n";
	    }
	}
	$image->Subtract($removals);
    }
    
    return $simul;

    #Prune Unreachable is not so important, since unreachable states won't appear during
    #the MH construction
    #Moreover, if we reuse the automaton for construction an AWT with a higher rank, those
    #state could probably be reachable again
    #print "Prune Unreachable\n";
    #$self->PruneUnreachable;

}

######################################################################
# Compute the set of pairs (p,q) such that q simulates p and is
# distinct from it.
#
# p is simulated by q if
# 1 forall tp=(lp,Fp) in delta(p)
# 2 exists tq=(lq,Fq) in delta(q) with lp->lq
# 3 forall Cp in Fp
# 4 exists Cq in Fq
# 5 forall (dq,sq) in Cq
# 6 forall d satisfying dq exists (dp,sp) in Cp such that d satisfies dp
#   and sp is simulated by sq
#
# Forall d sat dp exists dp: d sat dp is equivalent to dq->dp and this is
# equivalent to dp->IsIncluded(dq) in our implementation.
# 
######################################################################
sub ComputeDirectSimulationRelation {
    my $self = shift;
    my %params = @_;
    my $states = $$self{states};
    my $fair = $$self{fair};
    my $delta = $$self{delta};
    my $names = $$self{names};
    my $labels = $$self{directions}->Second;
    my $inverse;
    if (defined $params{inverse}) {
	$inverse = $params{inverse};
    } else {
	$inverse = InvertDelta($states, $delta);
    }
    my $oldSimul;
    if (defined $params{oldSim}) {
	$oldSimul = $params{oldSim};
    } else {
	$oldSimul = Set->new;
    }
    # Initialize the direct simulation relation to all pairs (p,q)
    # that satisfy:
    # 1. p != q
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
	    next if ($oldSimul->IsMember($pair)); #don't recompute simul
	    push(@queue, $pair);
	    $enqueued{$pair} = 1;
	}
    }
    # Compute the greatest fixpoint.
  PAIRS: while (@queue > 0) {
	#print "SIM: ".$simul->Size."\n";
	my $pair = pop(@queue);
	delete $enqueued{$pair};
	next if ($oldSimul->IsMember($pair)); #don't recompute simul
	my $p = $pair->First;
	my $q = $pair->Second;
	my $pname = $$names{$p};
	my $qname = $$names{$q};
	if ($DEBUG eq 3) {
	    my $num = @queue;
	    print "-- #enq pairs: $num\n";
	    map {print $_->ToString($names);} @queue;
	    print "\n";
	}
	print "-- Pair: $pname simulated by $qname\n" if $DEBUG eq 3; #diag
	# check for uncovered labels  because they lead to true!!!
	my $coveredP = Cover->new;
	my $flag = 1;
	my $pimage = $$delta{$p};
	my $qimage = $$delta{$q};
	next unless defined $qimage; #q has a single TRUE-transition -> simulates everything
	# 2 forall l
      LLOOP: foreach my $label (values %$labels) { #FORALL
	    # 1 forall tp=(lp,Cp) in delta(p) with : l->lp
	    print "Check l: ". $label->ToString. "\n" if $DEBUG eq 3;
	    next unless defined $pimage; #p has a single TRUE-transition
	  PLOOP: foreach my $tp (values %$pimage) { #FORALL
		my $plabel = $tp->First;
		my $pstateset = $tp->Second;
		next unless $plabel->IsIncluded($label); #l->lp
		$coveredP->Push($label);
		print "$pname: Check tr " . $tp->ToString($names) ."\n" if $DEBUG eq 3;
		# try transitions of q
		# 2 exists tq=(lq,Cq) in delta(q) with l->lq
		my $labelCovered = 0;
	      QLOOP:foreach my $tq (values %$qimage) { #EXISTS
		    print "$qname: Use tr " . $tq->ToString($names) ."\n" if $DEBUG eq 3;
		    my $qlabel = $tq->First;
		    my $qstateset = $tq->Second;
		    next unless $qlabel->IsIncluded($label); #l->lq
		    $labelCovered = 1;
		    next PLOOP if $self->IsC1DirectSimulatingC2($qstateset, $pstateset, $simul);
		    #else next QLOOP (try next Cq)
		}
		# at this point, there exists no Cq that simulates Cp, which means that
		# not all Cp are simulated -> delete Pair
		print "tr($qname, ", $label->ToString. ") = TRUE \n" if (($labelCovered == 0) &&
									 ($DEBUG eq 3));
		next if ($labelCovered == 0); #delta(q,l) = TRUE -> simulates everything
		$simul->Delete($pair);
		print "remove 1: " if $DEBUG eq 3;
		print $pair->ToString($names)."\n" if $DEBUG eq 3;

		# Enqueue pairs affected by the deletion
		foreach my $u (values %{$$inverse{$p}}) {
		    my $ulabel = $u->First;
		    my $ustate = $u->Second;
		    foreach my $v (values %{$$inverse{$q}}) {
			next if $u eq $v;
			my $vlabel = $v->First;
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
		next PAIRS;
	    } # foreach my $tp in delta(p)
	} # foreach my $label
	
	#since all unmentioned label lead to TRUE, we have to check for them as well
	$coveredP = $coveredP->PrimeAndIrredundant; #stores all labels mentioned in p
	next if ($coveredP->Size == 1 && $coveredP->Pick->Size == 0); #all labels mentioned

	my $coveredQ = Cover->new; #stores all labels mentioned in q
	foreach (values %$qimage) {
	    $coveredQ->Push($_->First);
	}
	$coveredQ = $coveredQ->PrimeAndIrredundant;
	# all labels unmentioned in p have to be unmentioned in q too, so all labels
	# mentioned in q have to be mentioned in p too.
	if ($coveredP->IsIncluded($coveredQ)) { # P={{a=1},{a=0,b=1}} Q={{a=1,b=0},{a=0,b=1,c=0}} -> OK
	    print "P:".$coveredP->ToString($names)." Q:".$coveredQ->ToString($names)."\n" if $DEBUG eq 3;
	    print "retaine: " if $DEBUG eq 3;
	    print $pair->ToString($names)."\n" if $DEBUG eq 3;
	} else {
	    $simul->Delete($pair);
	    print "P:".$coveredP->ToString($names)." Q:".$coveredQ->ToString($names)."\n" if $DEBUG eq 3;
	    print "remove 2: " if $DEBUG eq 3;
	    print $pair->ToString($names)."\n" if $DEBUG eq 3;
	    # Enqueue pairs affected by the deletion
	    foreach my $u (values %{$$inverse{$p}}) {
		my $ulabel = $u->First;
		my $ustate = $u->Second;
		foreach my $v (values %{$$inverse{$q}}) {
		    my $vlabel = $v->First;
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
	}
    }
    #print "Direct simulation relation contains ", $simul->Size," pairs\n"; #diag
    #return $simul unless $simul->Size > 0;
    #print "Direct simulation sans identity: {[simulated,simulating],...}\n",
    #$self->StateRelationToNameString($simul), "\n"; # diag

    return $simul;
} # ComputeDirectSimulationRelation



######################################################################
# Computes if a universal-transition P (set of dir-state-pairs) is
# simulated by another universal-transition Q (which implies
# that L(P) <= L(Q) ).
#
# We can see the language of a universal-transition as the conjunct of
# all its sublanguages, e.g., L(p1/\p2/\p3) = L(p1)/\L(p2)/\L(p3). So
# each pair (p1,p2,p3) can be seen as restriction of the language.
#
# The idea is to find for each pair (dq,sq) in Q a pair (dp,sp) in P
# that restricts L(P) in the same way (or even more than) (dp,sq) does.
#
# P is simulated by Q (for a given simulation relation) if
# 1 forall (dq,sq) in Q
# 2 forall d such that d->dq (d satisfies dq)
# 3 exists (dp,sp) in P such that such that d->dp (d satisfies dp)
#   and sp is simulated by sq
#
# Note that d->dp is equivalent to dp->IsIncluded(d) in our
# implementation because d and dp are only conjuncts of terms (like a=1).
#
######################################################################
sub IsC1DirectSimulatingC2 {
    my ($self, $qstateset, $pstateset, $simul) = @_;
    my $directions = $$self{directions}->First;

    if ($qstateset->Size == 0 && #tr to false
	$pstateset->Size > 0) {
	print "conjunct of q is more restrictive than conjunct of p - FAIL\n"
	  if $DEBUG eq 3;
	return "";
    }

    foreach my $dir (values %{$directions}) {
	# FORALL qp in Q - check all qp (dir,state)-pairs
      QP: foreach my $qp (values %{$qstateset}) {
	    next unless $qp->First->IsIncluded($dir);
	    # Note that unmentioned directions lead to TRUE but that's not
	    # problem since all directions unmentioned in Cp can simulate
	    # everything in Cq
	    # EXIST pp in Cp - try all pp
	    foreach my $pp (values %{$pstateset}) {
		next unless $pp->First->IsIncluded($dir);
		# Note that unmentioned directions in Cq can only be simulate
		# by unmentioned directions in Cp, so if $qp consists of an
		# direction unmentioned in Cp, we won't find a $pp to cover $qp,
		# so q cannot simulate p in this direction
		next QP if (($pp->Second eq $qp->Second) ||
		       ($simul->IsMember(Pair->new($pp->Second,$qp->Second))));
	    }
	    #there is an uncovered direction
	    #print $dir->ToString($$self{names}) . "is not covered\n";
	    print "conjunct of q is more restrictive than conjunct of p - FAIL\n"
	      if $DEBUG eq 3;
	    return "";
	}
	#all qp are covered -> check next directions
    }
    print "conjunct of q is less restrictive than conjunct of p - OK\n"
      if $DEBUG eq 3;
    return 1;
}


######################################################################
# Computes the inverse of delta.
######################################################################
sub InvertDelta {
    my ($states,$delta) = @_;
    my %inverse = ();
    foreach my $state (values %{$states}) {
	$inverse{$state} = Set->new;
    }
    foreach my $state (values %{$states}) {
	my $image = $$delta{$state};
	foreach my $succpair (values %{$image}) {
	    my $slabel = $succpair->First;
	    my $sstateset = $succpair->Second;
	    next if  $sstateset->Size eq 0; #FALSE
	    foreach my $sdirstate (values %{$sstateset}) {
		my $sstate = $sdirstate->Second;
		$inverse{$sstate}->Push(Pair->new($slabel,$state));
	    }
	}
    }
    return \%inverse;

} # InvertDelta


######################################################################
# Check if the AWT has a valid structure
######################################################################
sub CheckTypes {
    my ($self,$str) = @_;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $names = $$self{names};
    $str = "" unless defined $str;
    
    print "Typecheck at $str:\n";
    die "" if not $init->IsIncluded($states);
    foreach my $fc (values %$fair) {
	die "" if not $fc->IsIncluded($states);
    }
    foreach my $state (values %$states) {
	die "" if not defined $$names{$state};
	my $image = $$delta{$state};
	next unless defined $image; #tr to TRUE
	die "" unless (ref($image) eq "Set"); #wrong image type
	foreach my $tr (values %$image) {
	    die "" unless (ref($tr) eq "Pair"); #label-stateset pair
	    my $label = $tr->First;
	    die "" unless (ref($label) eq "UniqSet"); #wrong label type
	    my $sset = $tr->Second;
	    die "" unless (ref($sset) eq "Set"); #wrong type (conjunct)
	    foreach my $ds (values %$sset) {
		die "" unless (ref($ds) eq "Pair"); #dir-state pair
		my $dir = $ds->First;
		my $suc = $ds->Second;
		die "" unless (ref($sset) eq "Set"); #wrong dir type
		die "" unless (ref($sset) eq "Set"); #wrong state type
	    }
	}
    }
    print "OK\n";
}
######################################################################
# Remove unreachable states from automaton.
######################################################################
sub PruneUnreachable {
    my $self = shift;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $fair = $$self{fair};
    my $names = $$self{names};
    my $reachable = Reachable($init,$delta);
    
    foreach my $state (values %{$states}) {
	delete $$delta{$state} unless $reachable->IsMember($state);
	print $state->ToString($names)." is unreachable\n" unless $reachable->IsMember($state);
    }
    foreach my $fairset (values %{$fair}) {
	$fairset->Restrict($reachable);
    }
    $states->Restrict($reachable);

} # PruneUnreachable

######################################################################
# Computes the reachable states of an automaton by BFS.
######################################################################
sub Reachable {
    print "AlternatingTree::Reachable\n";
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
		    foreach my $w (values %$trans) { #w=(dir,state)
			$image->Push($w->Second);
		    }
		}
	    }
	}
	$new = $image->Difference($reached);
	$reached->Add($image);
    }
    return $reached;

} # Reachable



####################################################################
# Hashing Function
# This function includes the consistency check, since we want to
# hash the check too.
####################################################################
sub hashing {
    my ($newstate,$states,$unexpanded,$hashtable,$num,$simul,$anames) = @_;
    die if ref($states) ne 'Set';
    die if ref($unexpanded) ne 'Set';
    die if ref($hashtable) ne 'HASH';
    die if ref($num) ne 'HASH';
    $simul = Set->new unless defined $simul;
    my $key = "";
    my $i = 0;
    my $temp = 0;
    my $stateset = $newstate->First;
    my $obligation = $newstate->Second;
    
    #build hashkey
    my (@a,@b);
    foreach my $astate (values %{$stateset}) {
	$a[$i] = $$num{$astate};
	$i++;
    }
    @a = sort numeric @a;
    $key = join(".",@a);
    $i = 0;
    foreach my $astate (values %{$obligation}) {
	$b[$i] = $$num{$astate};
	$i++;
    }
    @b = sort numeric @b;
    $key .= "|".join(".",@b);

    if (exists $$hashtable{$key}) {
	return $$hashtable{$key};
    }

    #check consistency and build new hashkey is necessary
    my $consistency = checkAndMakeConsistent($newstate,$simul,$anames);
    if ($consistency eq "") { #state is inconsistent
	$$hashtable{$key} = undef;
	$newstate = undef;
    } elsif ($consistency == 1) { #state is consistent
	$states->Push($newstate);
	$unexpanded->Push($newstate);
	$$hashtable{$key} = $newstate;
    } else { # ($consistency == 2) - state was make consistent - recompute hashkey
	$i = 0;
	my (@s,@o);
	foreach my $astate (values %{$newstate->First}) {
	    $s[$i] = $$num{$astate};
	    $i++;
	}
	@s = sort numeric @s;
	my $newkey = join(".",@s);
	$i = 0;
	foreach my $astate (values %{$newstate->Second}) {
	    $o[$i] = $$num{$astate};
	    $i++;
	}
	@o = sort numeric @o;
	$newkey .= "|".join(".",@o);
	
	if (exists $$hashtable{$newkey}) {
	    $newstate = $$hashtable{$newkey};
	} else {
	    $states->Push($newstate);
	    $unexpanded->Push($newstate);
	    $$hashtable{$newkey} = $newstate;
	}
	$$hashtable{$key} = $newstate;
    }
    return $newstate;
}

###################################################################
# For comparison
###################################################################
sub numeric { $a <=> $b}


######################################################################
# The fcts below are just for testing.
######################################################################
use LTL;
sub GetInstance {
    my $class = shift;
    my $states = Set->new;
    my $init = Set->new;
    my $directions = Pair->new(Set->new, Set->new);
    my $dirs   = $directions->First;
    my $labels = $directions->Second;
    my %delta = ();
    my %names = ();
    my $fair = Set->new;

    #build labels and directions
    my $a1 = Set->new;
    $a1->Push(LTL->new("a=1"));
    $labels->Push($a1);
    my $a0 = Set->new;
    $a0->Push(LTL->new("a=0"));
    $labels->Push($a0);

    my $r1 = Set->new;
    $r1->Push(LTL->new("r=1"));
    $dirs->Push($r1);
    my $r0 = Set->new;
    $r0->Push(LTL->new("r=0"));
    $dirs->Second->Push($r0);
    
    #build states and initial
    my $A = Set->new;
    $A->Push(LTL->new("G(a=1)"));
    $names{$A} = "A";
    $states->Push($A);
    $init->Push($A);
    
    my $B = Set->new;
    $B->Push(LTL->new("G(a=0)"));
    $names{$B} = "B";
    $states->Push($B);

    my $C = Set->new;
    $C->Push(LTL->new("F(a=0)"));
    $names{$C} = "C";
    $states->Push($C);

    my $D = Set->new;
    $D->Push(LTL->new("F(a=1)"));
    $names{$D} = "D";
    $states->Push($D);
    
    my $E = Set->new;
    $E->Push(LTL->new("TRUE"));
    $names{$E} = "E";
    $states->Push($E);
    $fair->Push(Set->new($E));

    #make transition relation
    my $conjunct;
    $delta{$A} = Set->new;
    $conjunct = Set->new;
    $conjunct->Push(Pair->new($r0,$A));
    $conjunct->Push(Pair->new($r1,$B));
    $delta{$A}->Push(Pair->new($a1,$conjunct));
    $delta{$A}->Push(Pair->new($a0,Set->new(Pair->new(Set->new, $D))));
    
    $delta{$B} = Set->new;
    $conjunct = Set->new;
    $conjunct->Push(Pair->new($r0,$A));
    $conjunct->Push(Pair->new($r1,$B));
    $delta{$B}->Push(Pair->new($a1,$conjunct));
    $delta{$B}->Push(Pair->new($a0,Set->new(Pair->new(Set->new, $C))));
    
    $delta{$C} = Set->new;
    $conjunct = Set->new;
    $conjunct->Push(Pair->new($r0,$D));
    $conjunct->Push(Pair->new($r1,$E));
    $conjunct->Push(Pair->new($r0,$E));
    $delta{$C}->Push(Pair->new($a1,$conjunct));
    $delta{$C}->Push(Pair->new($a0,Set->new(Pair->new(Set->new,$A))));

    $delta{$D} = Set->new;
    $conjunct = Set->new;
    $conjunct->Push(Pair->new($r0,$D));
    $conjunct->Push(Pair->new($r1,$E));
    $conjunct->Push(Pair->new($r0,$E));
    $delta{$D}->Push(Pair->new($a1,$conjunct));
    $delta{$D}->Push(Pair->new($a0,Set->new(Pair->new(Set->new,$B))));
    
    $delta{$E} = Set->new;
    $conjunct = Set->new;
    $conjunct->Push(Pair->new(Set->new,$E));
    $delta{$E}->Push(Pair->new(Set->new,$conjunct));
    
    my	$self = {
		 states => $states,
		 init   => $init,
		 delta  => \%delta,
		 names  => \%names,
		 directions => $directions,
		 fair   => $fair,
		};
    return bless $self, $class;

}

1;
