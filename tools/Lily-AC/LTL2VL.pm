# $Id: LTL2VL.pm 2389 2008-06-19 09:09:53Z jobstman $

######################################################################
# LTL to Verilog synthesizer. Takes an LTL formula as specification and
# generates a VERILOG module that adheres to the given specification.
#
# Lily - LInear Logic sYnthesize
# Author: Barbara Jobstmann <bjobst@ist.tugraz.at>
######################################################################

package LTL2VL;
use Exporter ();
use vars qw(@ISA @EXPORT @EXPORT_OK);
@ISA       = qw(Exporter);
@EXPORT    = qw();
@EXPORT_OK = qw();

use strict;
use LTL;
use LTL2AUT;
use Buechi;
use BuechiAL;
use BuechiALTree;

######################################################################
# Build a new synthesizer. It stores the configuration and all
# intermediate results.
######################################################################
sub new {
    my $class = shift;
    my %params = @_;

    #Read mentatory parameter
    return undef unless defined $params{formula};
    return undef unless defined $params{partition};
    
    #Read optional parameter and supply default values if needed.
    $params{directory} = "" unless defined $params{directory};
    $params{name} = "synthesis" unless defined $params{name};
    $params{prefix} = "ltl2vl" unless defined $params{prefix};
    $params{simplify} = 1 unless defined $params{simplify};
    $params{method} = "Boolean" unless defined $params{method};
    $params{verbose} = 1 unless defined $params{verbose};
    $params{optimize_nbw} = 1 unless defined $params{optimize_nbw};
    $params{optimize_uct} = 1 unless defined $params{optimize_uct};
    $params{optimize_awt} = 1 unless defined $params{optimize_awt};
    $params{optimize_witness} = 1 unless defined $params{optimize_witness};
    $params{optimize_edges} = 1 unless  defined $params{optimize_edges};
    $params{optimize_release} = 1 unless defined $params{optimize_release};
    $params{optimize_reuse} = 1 unless defined $params{optimize_reuse};
    $params{combined} = 1 unless defined $params{combined};
    $params{optimize_mh} = 1 unless defined $params{optimize_mh};
    
    # Make debug directory
    system ("mkdir ".$params{directory}) if (($params{directory} ne "") and
					(not -d $params{directory}));

    my $self = {
		formula   => $params{formula},   #stores phi
		partition => $params{partition}, #stores the IO-partition
		name      => $params{name},      #name of the generated module
		directory => $params{directory}, #debug directory
		prefix    => $params{prefix},    #prefix of output files
		simplify  => $params{simplify},  #NBW option
		method    => $params{method},    #NBW option
		optimize_nbw => $params{optimize_nbw},
		optimize_uct => $params{optimize_uct},
		optimize_awt => $params{optimize_awt},
		optimize_witness => $params{optimize_witness},
		optimize_mh =>  $params{optimize_mh},
		optimize_edges => $params{optimize_edges},
		optimize_release => $params{optimize_release},
		optimize_reuse => $params{optimize_reuse},
		combined => $params{combined},
		verbose   => $params{verbose},
		assume    => undef,            #holds automaton for the assumption
		nbw       => undef,            #holds automaton for not phi
		nbw_tl    => undef,            #holds transition labeled nbw
		uct       => undef,            #stores uct for phi
		#note that we store in the following variables only the result
		#for one rank. So when we increase the rank these variables are
		#overwritten.
		awt       => undef,            #stores awt for phi
		awt_sim   => Set->new,         #simulation relation of the awt
		awt_lost  => Set->new,         #set of states removed from awt
		awt_order => {},               #ordering of awt states for MH
		nbt       => undef,            #stores nbt for phi
		nbt_stateHash => {},           #stores the hash of the nbt states
		nbt_satHash => {},             #stores the hash of the satisfying assignments
		nbt_win   => Set->new,         #winning states of the nbt
		witness   => undef,            #stores a witness of phi
	       };

    print "Optimizations:\n";
    print "NBW:".$$self{optimize_nbw}." UCT:".$$self{optimize_uct}." ";
    print "AWT:".$$self{optimize_awt}." WIT:".$$self{optimize_witness}." ";
    print "MH:".$$self{optimize_mh}." MHC:".$$self{combined}." ";
    print "Edges:".$$self{optimize_edges}." ";
    print "Release:".$$self{optimize_release}." ";
    print "Reuse:".$$self{optimize_reuse}." ";
    return bless $self, $class;
}

######################################################################
# Takes a state-labeled Buechi automaton and stores it.
######################################################################
sub SetNBW {
    my ($self,$aut) = @_;

    if ($$aut{fair}->Size != 1) {
	$aut = $aut->CountingConstruction;
    }
    $$self{nbw} = $aut;
}

######################################################################
# Takes a state-labeled Buechi automaton and stores it.
######################################################################
sub SetTransitionLabeledNBW {
    my ($self,$aut) = @_;
    my $debugdir = $$self{directory};
    my $verb = $$self{verbose};
    my $optimize = $$self{optimize_nbw};

    $aut->DirectSimulationMinimization if $optimize;
    $aut->FairSimulationMinimization if $optimize;

    $$self{nbw_tl} = $aut;
    print $aut->ToString."\n";
    if ($verb > 1) {
	open( NBW, ">$debugdir"."nbw.dot" );
	print NBW $aut->ToDot("NBW");
	close NBW;
	Utils::dot2ps($debugdir."nbw.dot");
    }
}

######################################################################
# Takes an universal Co-Buechi tree automaton and stores it.
######################################################################
sub SetUCT {
    my ($self,$aut) = @_;
    my $debugdir = $$self{directory};
    my $verb = $$self{verbose};
    my $valid = 1;

    print "Note that option -oedges is ignored.\n";
    $valid = $aut->LostStatesMinimization($verb) if $$self{optimize_uct};
    $$self{uct} = $aut;
    #print $aut->ToString."\n";
    if ($verb > 1) {
	open( UCT, ">$debugdir"."uct.dot" );
	print UCT $aut->ToDot("UCT");
	close UCT;
	Utils::dot2ps($debugdir."uct.dot");
    }
    return $valid;
}

######################################################################
# Takes an universal Co-Buechi tree automaton and stores it.
######################################################################
sub SetAWT {
    my ($self,$aut) = @_;
    my $debugdir = $$self{directory};
    my $verb = $$self{verbose};
    my $optimize = $$self{optimize_awt};
    my $valid = 1;
    
    $$self{awt} = $aut;
    #print $aut->ToString."\n";
    if ($verb > 1) {
	open( UCT, ">$debugdir"."awt.dot" );
	print UCT $aut->ToDot("AWT");
	close UCT;
	Utils::dot2ps($debugdir."awt.dot");
    }
    print "Stats AWT: ", $aut->Stats, "\n";
    if ($optimize > 0) {
	print  "AWT Minimization...\n";
	if (($optimize == 1) || ($optimize == 2)) {
	    $valid = $aut->LostStatesMinimization(verbose => $verb,
						  rank => "unknown");
	}
	return "" unless $valid; #we don't store the lost states or the awt
	                         #simulation relation because we don't need
	                         #them, since the language of the awt is
	                         #empty and we don't increase the rank
	print "Stats AWT LS: ", $aut->Stats, "\n";
	if (($optimize == 1) ||($optimize == 3)) {
	    $$self{awt_sim} = $aut->DirectSimulationMinimization;
	}
	print "Stats AWT SIM: ", $aut->Stats, "\n";
	print  "AWT Minimization done\n";
	if ($verb > 1) {
	    open( AWT, ">$debugdir"."awt.dot" );
	    print AWT $aut->ToDot("AWT-OPT");
	    close AWT;
	    Utils::dot2ps($debugdir."awt.dot");
	    open AWT,  ">$debugdir"."awt.awt";
	    print AWT $aut->ToString;
	    close AWT;
	}
    }
    $$self{awt} = $aut;
    return $valid;
}

######################################################################
#   Time out handler
######################################################################
sub timeouthandler {
    my $sig = shift;
    print "CPU time: > 3600 seconds (timeout)\n";
    exit 0;
}
# Required return value.

######################################################################
# Takes an UCT as specification and
# build a VERILOG module that fulfills the specification.
######################################################################
sub SynthesizeFromUCT {
    my $self = shift;
    my $debugdir = $$self{directory};
    my $combined = (defined $$self{combined})?$$self{combined}:0;
    my $valid = 1;

    alarm 3600;
    $SIG{'ALRM'} = \&timeouthandler;
    
    #check if we have a valid UCT
    $self->GetUCT;
    
    # make debug directory 
    system ("mkdir ".$debugdir) if (($debugdir ne "") and
					(not -d $debugdir));
    my $start = 0;
    my $bound = 4;   #$rank = n*2^n
    if (not $self->IsWeak) {
	print "Increase rank bound if the formula is not realizable\n";
    } else {
	$start = 1;
	$bound = 1;
    }
    for (my $rank = $start; $rank <= $bound; $rank = $rank + 1) {
	print "---------- Synthesize with rank $rank ----------\n";
	$valid = $self->BuildAWT($rank);
	$self->MakeAWTStateOrdering;
	#TODO last if state-sets are equal
	next unless $valid;
	if ($combined) {
	    $valid = $self->BuildNBTAndWitness(rank => $rank);
	} else {
	    $valid = $self->BuildNBT(rank => $rank);
	    next unless $valid;
	    $valid = $self->BuildWitness(rank => $rank);
	}
	next unless $valid;
	last; #we found a witness
    }
	
	#####
#	exit(0); # STOP HERE FOR AWT (P_O)
	#####

    if (not $valid) {
	if (not $self->IsWeak) {
	    print "Formula is not realizable with rank $bound.\n";
	    $self->WriteOutputfiles("Formula is not realizable with rank $bound.\n");
	} else {
	    print "Formula is not realizable.\n";
	    $self->WriteOutputfiles("Formula is not realizable.\n");
	}
	return "";
    }
    return 1;
}


######################################################################
# Takes an AWT as specification and
# build a VERILOG module that fulfills the specification.
######################################################################
sub SynthesizeFromAWT {
    my $self = shift;
    my $debugdir = $$self{directory};
    my $combined = (defined $$self{combined})?$$self{combined}:0;
    my $valid = 1;

    alarm 3600;
    $SIG{'ALRM'} = \&timeouthandler;
    
    #check if we have a valid UCT
    $self->GetAWT;
    $self->MakeAWTStateOrdering;
    
    # make debug directory 
    system ("mkdir ".$debugdir) if (($debugdir ne "") and
					(not -d $debugdir));

    if ($combined) {
	$valid = $self->BuildNBTAndWitness;
    } else {
	$valid = $self->BuildNBT;
	next unless $valid;
	$valid = $self->BuildWitness;
    }

    if (not $valid) {
	print "Formula is not realizable\n";
	$self->WriteOutputfiles("Formula is not realizable.\n");
	return "";
    }
    return 1;
}


######################################################################
# Builds an NBW that recognizes all satisfiable input traces of phi
######################################################################
sub BuildPureAssumption {
    my ($self, $verb) = @_;
    $verb = $$self{verbose} unless defined $verb;
    my $formula = $$self{formula};
    my $simplify = $$self{simplify};
    my $method  = $$self{method};
    my $optimize = $$self{optimize_nbw};
    my $debugdir = $$self{directory};
    my $partition = $$self{partition};

    my $parsetree = LTL->new($formula);
    my $normalized = $parsetree->Normalize;
    $normalized = $normalized->Simplify if $simplify;
    print "Build word automaton for ";
    print $normalized->ToString, "\n";

    my $aut = LTL2AUT->new(formula => $normalized, method => $method);
    print "Stats NBW (phi): ", $aut->Stats, "\n";

    #project automaton to input signals
    my $outputs = Set->new;
    my $inputs  = "";
    foreach (keys %{$partition}) {
	if ($$partition{$_} eq 2) { #output variable
	    $outputs->Push($_);
	} else {
	    $inputs .= "$_ ";
	}
    }
    $aut->Project($outputs);
    $aut->Optimize($verb) if $optimize;
    print "Stats NBW (project): ", $aut->Stats, "\n";

    return $aut;
}

######################################################################
# Take an NBW representing assumptions on the inputs and conjoin it
# with the NBW for not phi.
######################################################################
sub UseAssumption {
    my ($self, $env_aut) = @_;
    my $result = $$self{nbw};
    my $verb   = $$self{verbose};
    my $optimize = $$self{optimize_nbw};
    my $debugdir = $$self{directory};
    
    if ($verb > 1) {
	open(ASSUME, ">$debugdir"."assume.dot");
	print ASSUME $env_aut->ToDot("Assumption");
	close ASSUME;
    }
    $result = $result->Intersection($env_aut);
    $result->Optimize($verb) if $optimize;
    print "Stats NBW (intersect): ", $result->Stats, "\n";
    $$self{nbw} = $result;
    return 1;
}

######################################################################
# Apply Counting Construction (if necessary) to get a single fairness
# condition.
######################################################################
sub ApplyCountingConstruction {
    my $self = shift;
    my $result  = $$self{nbw};
    my $verb   = $$self{verbose};
    my $optimize = $$self{optimize_nbw};

    if ($result && $result->{fair}->Size > 1) {
	print "Apply counting construction to reduce ";
	print "the fairness conditions to a single one.\n";
	my $ccresult  = $result->CountingConstruction;
	$ccresult->Optimize($verb) if ($optimize && ($result ne $ccresult));
	$$self{nbw} = $ccresult;
	print "Stats NBW (after cc): ", $result->Stats, "\n";
    }

    #check if nbw = false
    if ($$self{nbw}->IsEmpty) {
	print "Phi is trivially realizable (under the given input assumption)\n";
	return "";
    }
    return 1;
}

######################################################################
# Build an NBW automaton for the negation of the formula.
######################################################################
sub BuildNBW {
    my ($self, $verb) = @_;
    $verb = $$self{verbose} unless defined $verb;
    my $formula = $$self{formula};
    my $prefix  = $$self{prefix};
    my $simplify = $$self{simplify};
    my $method  = $$self{method};
    my $optimize = $$self{optimize_nbw};
    my $debugdir = $$self{directory};
    my $partition = $$self{partition};
    
    print "formula: ", $formula, "\n", '-' x 70, "\n";
    #invert formula and build optimized NBW
    my $negformula = "!(".$formula.")";
    my $parsetree = LTL->new($negformula);
    print $parsetree->ToString, "\n" if $verb > 1;
    print $parsetree->ToDot($negformula) if $verb > 3;
    my $normalized = $parsetree->Normalize;
    $normalized = $normalized->Simplify if $simplify;

    print "Build word automaton for ";
    print $normalized->ToString, "\n";
    if ($normalized eq LTL->new("TRUE")) {
	print "Formula is not satisfiable\n";
	exit;
    }
    if ($normalized eq LTL->new("FALSE")) {
	print "Formula is valid and so trivially realizable\n";
	exit;
    }
    my $result = LTL2AUT->new(formula => $normalized, method => $method);
    $result->Optimize($verb) if $optimize;
#    $result->CheckTypes; #DEBUG
    print "Stats NBW (not phi): ", $result->Stats, "\n";
    
    if ($verb > 1) { 
	open(BUECHI, ">$debugdir"."buechi.dot");
	print BUECHI $result->ToDot($negformula);
	close BUECHI;
	Utils::dot2ps($debugdir."buechi.dot");
	open BUECHI, ">$debugdir"."buechi.aut";
	print BUECHI $result->ToString;
	close BUECHI;
	my $al=BuechiAL->fromBuechi($result);
	open( BUECHI, ">$debugdir"."buechi-al.dot");
	print BUECHI $al->ToDot($negformula);
	close BUECHI;
    }
    print "Stats NBW: ", $result->Stats, "\n";
    print "Build NBW done\n";
    $$self{nbw} = $result;
    return 1;
}

######################################################################
# Takes a state-labeled NBW and translates it to a transition labeled
# NBW. Returns 1 if the translation was possible, otherwise "".
######################################################################
sub BuildTransitionLabeledNBW {
    my ($self,$verb) = @_;
    $verb = $$self{verbose} unless defined $verb;
    my $nbw = $self->GetNBW;
    my $name   = $$self{name};
    my $debugdir  = $$self{directory};
    my $optimize = $$self{optimize_nbw};
    
    print "NBW(state-labeled) -> NBW(transition labeled)...\n";

    #Create and check  fairness condition
    if ( $$nbw{fair}->Size == 0 ) {
	# all states are accepting
	foreach my $state ($$nbw{states}) {
	    $$nbw{fair}->Push($state);
	}
    }
    if ( $$nbw{fair}->Size != 1 ) {
	print "Fair set size not equal to 1\n";
	print "Abort BuildTransitionLabeledNBW\n";
	return "";
    }

    my $bl =  BuechiAL->fromBuechi($nbw);
    $bl->DirectSimulationMinimization if $optimize;
    $bl->FairSimulationMinimization if $optimize;
    
	open NBW, ">$debugdir"."nbw.l2a";
	print NBW $bl->ToString;
	close NBW;

    #print states - name -table
    if ($verb > 2) {
	my $states = $$bl{states};
	my $names = $$bl{names};
	foreach my $state (values %$states) {
	    print $$names{$state}." -> ".$state->ToString."\n";
	}
    }

    $$self{nbw_tl} = $bl;
    print "NBW (state) -> NBW (trans) done\n";
    print "Stats NBW: ", $bl->Stats, "\n";
    return 1;
}

######################################################################
# Takes the stored transition labeled NBW and a partition of the AP
# into IO-signals and translate it to a UCT.
######################################################################
sub BuildUCT {
    my ($self, $verb) = @_;
    $verb = $$self{verbose} unless defined $verb;
    my $bl   = $self->GetTransitionLabeledNBW;
    my $partition = $$self{partition};
    my $name = $$self{name};
    my $debugdir = $$self{directory};
    my $optimize = $$self{optimize_uct};
    my $merge_edges = $$self{optimize_edges};
    my $valid = 1;

    print "NBW -> UCT...\n";
    my $cb = CoBuechiTree->fromBuechi( $bl, $partition, $verb, $merge_edges );
    if ( $cb eq "" ) {
    	$self->WriteOutputfiles("Formula is not realizable.\n");
	return "";
    }
    print "Stats UCT: ", $cb->Stats, "\n";
    $valid = $cb->LostStatesMinimization($verb) if $optimize;
    print "Stats UCT LS: ", $cb->Stats, "\n" if $optimize;
    $self->WriteOutputfiles("Formula is not realizable.\n") if ($valid eq "");

    if ($verb > 1) {
	open( UCT, ">$debugdir"."uct.dot" );
	print UCT $cb->ToDot($name);
	close UCT;
	Utils::dot2ps($debugdir."uct.dot");
	open UCT,  ">$debugdir"."uct.uct";
	print UCT $cb->ToString;
	close UCT;
    }

    $$self{uct} = $cb;
    print "NBW -> UCT done\n";
	open UCT,  ">$debugdir"."uct.uct";
	print UCT $cb->ToString;
	close UCT;

#    $cb->CheckTypes; #DEBUG

    return $valid;
}

######################################################################
# Takes the stored UCT and a given rank, translates it to an AWT and
# minimizes the AWT.
######################################################################
sub BuildAWT {
    my $self = shift;
    my $rank = shift;
    my $verb = $$self{verbose};
    my $cb = $self->GetUCT;
    my $debugdir = $$self{directory};
    my $optimize = $$self{optimize_awt};
    my $orelease = $$self{optimize_release};
    my $weak = $self->IsWeak;
    my $name = $$self{name};
    my $valid = 1;
      
    my $awt;
    if (defined $$self{awt}) {
	#We extend the existing AWT with another layer
	$awt = $self->GetAWT;
	$$awt{init} = Set->new;  #we get a new initial state
	my $init = $$awt{init};
	my $states = $$awt{states};
	my $delta = $$awt{delta};
	my $names = $$awt{names};
	my $fair = $$awt{fair}->Pick; #we have a single fairness condition
	my $cbinit = $$cb{init};
	my $cbfair = $$cb{fair};

	
	#we do not expand alpha states in odd ranks ->
	#initial state set is empty
	if ($cbfair->Pick->IsMember($cbinit->Pick) &&
	    ($rank % 2) == 1) {
	    print "We do not expand alpha states in odd ranks\n";
	    return "";
	}

	my $newstate = Pair->new( $cbinit->Pick, $rank );
	my $unexpanded = Set->new;
	$states->Push($newstate);
	$unexpanded->Push($newstate);
	$init->Push($newstate);
	AlternatingTree::Create2layers( $cb, $states, $delta, $names,
					$unexpanded, $fair, $orelease, $verb );
    } else {
	print  "UCT -> AWT...\n";
	$awt = AlternatingTree->fromBuechi( $cb, $weak, $rank, $orelease, $verb );
	return "" if $awt eq "";
    }
    
    print "Stats AWT: ", $awt->Stats, "\n";
    if ($verb > 1) {
	open( AWTB, ">$debugdir"."awt$rank-before.dot" );
	print AWTB $awt->ToDot("AWTB$rank$name");
	close AWT;
	Utils::dot2ps($debugdir."awt$rank-before.dot");
	open AWT,  ">$debugdir"."awt$rank-before.awt";
	print AWT $awt->ToString;
	close AWT;
    }
    
    if ($optimize > 0) {
	print  "AWT Minimization...\n";
	if (($optimize == 1) || ($optimize == 2)) {
	    $valid = $awt->LostStatesMinimization( verbose => $verb,
						   lost => $$self{awt_lost},
						   rank => $rank );
	}
	print "Stats AWT LS: ", $awt->Stats, "\n";
	if (($optimize == 1) || ($optimize == 3)) {
	    $$self{awt_sim} = $awt->DirectSimulationMinimization(
				    oldSim => $$self{awt_sim} );
	}
	print  "AWT Minimization done\n";
	print "Stats AWT SIM: ", $awt->Stats, "\n";
    }
    if ($verb > 1) {
	open( AWT, ">$debugdir"."awt$rank.dot" );
	print AWT $awt->ToDot("AWT$rank$name");
	close AWT;
	Utils::dot2ps($debugdir."awt$rank.dot");
	open AWT,  ">$debugdir"."awt$rank.awt";
	print AWT $awt->ToString;
	close AWT;
    }

#    $awt->CheckTypes("BuildAWT"); #DEBUG
    $$self{awt} = $awt;
    print  "UCT -> AWT done\n";
    return $valid;
}

######################################################################
# Gives each AWT state a number, which will be used during
# MH-construction to identify sets of states. We reuse the numbering
# established for AWT's with lower ranks.
######################################################################
sub MakeAWTStateOrdering {
    my $self = shift;
    my $awt = $self->GetAWT;
    
    #make ordering of the awt states for MH
    #reuse the ordering on states with lower ranks
    my $order = $self->{awt_order};
    my $i = scalar keys %$order;
    my $awtstates = $awt->{states};
    foreach my $astate ( values %{$awtstates} ) {
	next if exists $$order{$astate};
	$$order{$astate} = $i;
	$i++;
    }
}

######################################################################
# Takes the stored AWT and translates it to an NBT.
######################################################################
sub BuildNBT {
    my $self = shift;
    my %params = @_;
    my $rank = 1;
    $rank = $params{rank} if defined $params{rank};
    my $verb = $$self{verbose};
    my $debugdir = $$self{directory};
    my $reuse = $self->{optimize_reuse};
    my $al = $self->GetAWT;
    my $order = $self->{awt_order};
    my $stateHash = $self->{nbt_stateHash};
    my $satHash = $self->{nbt_satHash};
    my $name = $$self{name};
    print  "AWT -> NBT...\n";
    my $simul = $self->GetAWTSimulationRelation if $$self{optimize_mh};
    
    my $nbt;
    if ($reuse && (defined $self->{nbt})){ #we already have an NBT for a lower rank
	#use previous results:
	$nbt = $self->{nbt};
    } else {
	my %names = ();
	my $fair = Set->new(Set->new);
	$nbt = BuechiALTree->new(directions => $$al{directions},
				 fair  => $fair,
				 names  => \%names);
    }
    my $states = $$nbt{states};
    my $ainit = $$al{init};
    my $unexpanded = Set->new;	#set of states that need to be expanded
    my $initialstate = Pair->new( $ainit, Set->new ); # ({init},{})
    $initialstate = AlternatingTree::hashing( $initialstate, $states,
					      $unexpanded, $stateHash, $order);
    $$nbt{names}{$initialstate} = "toexpand\n";
    $$nbt{init} = Set->new($initialstate);
    
    my $ready = 0;
    while (not $ready) {
	$ready = $al->CreateMHLevel($verb, $nbt, $unexpanded, $stateHash,
				    $order, $satHash, $simul);
    }
    print "Stats NBT: ", $nbt->Stats, "\n";

    if ($verb > 1) {
	open( NBT, ">$debugdir"."nbt$rank.dot" );
	print NBT $nbt->ToDot($name.$rank);
	close NBT;
	Utils::dot2ps($debugdir."nbt$rank.dot");
    }
    $$self{nbt} = $nbt;
    print  "AWT -> NBT done\n";

    return 1;
}

######################################################################
# Build witness for language non-emptiness and optimize it
######################################################################
sub BuildWitness {
    my $self = shift;
    my %params = @_;
    my $nbt = $$self{nbt};
    my $optimize = $$self{optimize_witness};
    my $reuse = $$self{optimize_reuse};
    my $oldwin = $$self{nbt_win};
    my $debugdir = $$self{directory};

    my $witness;
    if ($reuse) {
	$witness = $nbt->LanguageEmptiness(oldwin => $oldwin);
    } else {
	$witness = $nbt->LanguageEmptiness();
    }
    $$self{witness} = $witness;
    return "" if (not $witness);

    open( WIT, ">$debugdir"."witness.dot" );
    print WIT $witness->ToDot("WIT");
    close WIT;

    print "Stats Witness: ", $$self{witness}->Stats, "\n";
    $$self{witness} = $witness->Optimize if $optimize;
    print  "Stats Witness opt: ", $$self{witness}->Stats, "\n" if $optimize;
    return 1;
}

######################################################################
# Takes the stored AWT and translates it to an NBT. Computes language
# emptiness during the translation and returns the NBT and a witness
# if the language is not empty.
######################################################################
sub BuildNBTAndWitness {
    my $self = shift;
    my %params = @_;
    my $rank = 1;
    $rank = $params{rank} if defined $params{rank};
    my $verb = $$self{verbose};
    my $debugdir = $$self{directory};
    my $reuse = $self->{optimize_reuse};
    my $optimize = $$self{optimize_witness};
    my $al = $self->GetAWT;
    my $order = $self->{awt_order};
    my $name = $$self{name};
    print  "AWT -> NBT + Witness...\n";
    my $simul = $self->GetAWTSimulationRelation if $$self{optimize_mh};

    my $hashtable = $$self{nbt_stateHash};
    my $satHash = $$self{nbt_satHash};
    my $expand = Set->new;
    my $initialstate = Pair->new( $$al{init}, Set->new ); # ({init},{})
    my $nbt;
    
    if ($reuse && (defined $self->{nbt})) {#we already have an NBT for a lower rank
	$nbt = $self->{nbt};
    } else {
	my %names = ();
	my $fair = Set->new(Set->new); #we have a single fairness constraint
	$nbt = BuechiALTree->new(directions => $$al{directions},
				 fair => $fair,
				 names  => \%names);
    }
    $initialstate = AlternatingTree::hashing($initialstate, $$nbt{states},
					     $expand, $hashtable, $order);
    $$nbt{names}{$initialstate} = "toexpand";
    $$nbt{init} = Set->new($initialstate);
    
    print "MHLevel 0: expand ".$expand->Size." states, ";
    $al->CreateMHLevel($verb, $nbt, $expand, $hashtable, $order,
		       $satHash, $simul);
    print $$nbt{states}->Size." total states, \n";
    my $winning = Set->new;
    my $witness;
    my $ready = 0;
    my $loop = 1;
    while (not $ready) {
	print "MHLevel $loop: expand ".$expand->Size." states, \n";
	$ready = $al->CreateMHLevel($verb, $nbt, $expand, $hashtable,
				    $order, $satHash, $simul);
	print $$nbt{states}->Size." total states, \n";
	$winning = $nbt->Winning(oldwin => $winning);
	print $winning->Size." winning states.\n";
	$witness = $nbt->LanguageEmptiness(win => $winning);
	$loop++;
	$ready = 1 if defined $witness;
    }
    $$self{nbt}= $nbt;
    print "Stats NBT: ", $nbt->Stats, "\n";
    if ($verb > 1) {
	open( NBT, ">$debugdir"."nbt$rank.dot" );
	print NBT $nbt->ToDot($name.$rank."combined");
	close NBT;
	Utils::dot2ps($debugdir."nbt$rank.dot");
    }
    return "" if (not $witness);

    if ($verb > 1) {
    	open( WIT, ">$debugdir"."witness$rank.dot" );
	print WIT $witness->ToDot($name.$rank."WIT");
	close WIT;
    }
    
    print  "Stats Witness: ", $witness->Stats, "\n";
    $witness = $witness->Optimize if $optimize;
    print  "Stats Witness opt: ", $witness->Stats, "\n";
    $$self{witness} = $witness;
    return 1;
}

######################################################################
# Print the stored witness in DOT and VERILOG format to a file.
######################################################################
sub PrintModule {
    my $self = shift;
    my $debugdir = $$self{directory};
    my $prefix = $$self{prefix};
    my $name = $$self{name};

    print "Results can be found in $debugdir$prefix-verilog.v and";
    print " $debugdir$prefix-synthesis.dot\n";
    open(VERILOG,   ">$debugdir" . "$prefix" . "-verilog.v");
    open(SYNTHESIS, ">$debugdir" . "$prefix" . "-synthesis.dot");

    my $witness = $self->GetWitness;
    print SYNTHESIS $witness->ToDot($name);
    Utils::dot2ps("$debugdir" . "$prefix" . "-synthesis.dot");

    my $verilog = $witness->ToVerilog;
    print VERILOG "//$$self{formula}\n";
    print VERILOG $verilog;

    close VERILOG;
    close SYNTHESIS;
}

######################################################################
# Clean the output files to avoid confusion.
######################################################################
sub CleanOutputfiles {
    my $self = shift;
    my $debugdir = $$self{directory};
    my $prefix = $$self{prefix};
    open(VERILOG,   ">$debugdir" . "$prefix" . "-verilog.v");
    open(SYNTHESIS, ">$debugdir" . "$prefix" . "-synthesis.dot");
    close VERILOG;
    close SYNTHESIS;
}

######################################################################
# Write text to the output files
######################################################################
sub WriteOutputfiles {
    my ($self,$text) = @_;
    my $debugdir = $$self{directory};
    my $prefix = $$self{prefix};
    open(VERILOG,   ">$debugdir" . "$prefix" . "-verilog.v");
    open(SYNTHESIS, ">$debugdir" . "$prefix" . "-synthesis.dot");
    print VERILOG $text;
    print SYNTHESIS $text;
    close VERILOG;
    close SYNTHESIS;
}

######################################################################
#
######################################################################
sub GetTransitionLabeledNBW {
    my $self = shift;
    return $$self{nbw_tl} if (defined $$self{nbw_tl});
    die "Transition labeled NBW not computed\n";
}
sub GetNBW {
    my $self = shift;
    return $$self{nbw} if (defined $$self{nbw});
    die "NBW not computed\n";
}
sub GetUCT {
    my $self = shift;
    return $$self{uct} if (defined $$self{uct});
    die "UCT not computed\n";
}
sub GetAWT {
    my $self = shift;
    return $$self{awt} if (defined $$self{awt});
    die "AWT not computed\n";
}


# using in BuildNBT and BuildNBTAndWitness
sub GetAWTSimulationRelation {
    my $self = shift;
    
    if ((not defined $self->{awt_sim}) ||
	($self->{optimize_reuse} == 1 &&
	 $self->{optimize_awt}   != 1 &&
	 $self->{optimize_awt}   != 3)) {
	print "Compute direct simulation relation for the AWT\n";
	my $awt = $self->GetAWT;
	my $oldSim = $self->{awt_sim};
	my $inverse = AlternatingTree::InvertDelta($awt->{states},$awt->{delta});
	my $sim = $awt->ComputeDirectSimulationRelation(inverse => $inverse,
							oldSim => $oldSim);
	die "computing simulation relation failed\n" unless defined $sim;
	print "Remove simu-equivalent states since we have no equivalence classes\n";
	#TODO: make equivalence classes
	$awt->RemoveSimulationEquivalentStates(inverse => $inverse,
					       simul => $sim);
	$$self{awt_sim} = $sim;
    }
    return $$self{awt_sim};
}
sub GetNBT {
    my $self = shift;
    return $$self{nbt} if (defined $$self{nbt});
    die "NWT not computed\n";
}
sub GetWitness {
    my $self = shift;
    return $$self{witness} if (defined $$self{witness});
    die "Witness not computed\n";
}
sub IsWeak {
    my $self = shift;
    return $$self{uct}->IsWeak if (defined $$self{uct});
    die "Strength unknown\n";
}

1;
