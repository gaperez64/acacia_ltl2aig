#! /usr/bin/perl -w
#-d:DProf
# $Id: lily.pl 2389 2008-06-19 09:09:53Z jobstman $

# This script generates Buechi automata from LTL formulae using
# the Daniele-Giunchiglia-Vardi algorithm and various optimizations.

# Author: Fabio Somenzi <Fabio@Colorado.EDU>, with modifications
# by Roderick Bloem <roderick.bloem@colorado.edu> and
# Barbara Jobstmann <bjobst@ist.tugraz.at

use Sopen;
use LTL;
use LTL2AUT;
use Verilog;
use strict;
use LTL2VL;
use Sugar;

my $startTime = (times)[0];
my $nbwTime = (times)[0];
my $synTime = (times)[0];

# Set default values for options.
my $verb = 1;			# verbosity level
my @formulae = ();		# list of LTL formulae to be processed
my @formulaeAssume = ();	# list of assume formulae to be processed
my $prefix = "ltl2vl";		# prefix for output file names
my $method = "LTL2AUT";		# method (GPVW, GPVW+, LTL2AUT, Boolean)
my $simplify = 1;		# simplify formula
my $optimize = 1;		# optimize automaton
my $complete = 0;		# complete transition relation
my $help     = 0;               # help is requested
my $automaton = "";		# automaton file
my $monitorFile = "";		# Verilog monitor file
my $verify = 0;

# Set default for building the complement
my $complementA = 0;

# project to a given set of atomic propositions
my $project = 0;
my $projectVars = Set->new;

# Set default for applying the counting construction
my $cc = 0;

# Set default values for synthesis options
my $ltlfile = "";
my $sugar = "";
my $synthesis = 0;
my %partition = ();    # IO-partition
my $synthesisDir = ""; # debug and result directory
my $mc = 0;
my $env = 0;                    # extract restricted environment too
my $env_automaton = "";		# automaton that restricts the environment
my $optimize_uct = 1;		# optimize uct automaton
my $optimize_awt = 1;		# optimize awt automaton
my $optimize_witness = 1;	# optimize witness
my $optimize_mh = 1;	        # optimize MH with simulation relation
my $optimize_edges = 1;
my $optimize_release = 1;
my $optimize_reuse = 1;
my $combinedMH = 1;             # combined MH with witness computation

# Parse command line and set options accordingly.
while (defined($ARGV[0]) && substr($ARGV[0], 0, 1) eq "-") {
    if ($ARGV[0] eq "-c") {
	shift;
	$complete = shift;
    } elsif ($ARGV[0] eq "-f") {
	shift;
	push(@formulae, shift);
    } elsif ($ARGV[0] eq "-h") {
	shift;
	$help = 1;
    }  elsif ($ARGV[0] eq "-ltl") {
	shift;
	$ltlfile = shift;
	$_ = $ltlfile;
	if (/\.psl/) {
	    print "Read Sugar file.\n";
	    readSugar($_,\@formulae, \@formulaeAssume);
	    $ltlfile =~ s/\.psl/\.ltl/;
	    $sugar = 1;
	} else {
	    print "Read LTL file.\n";
	    readLTLOverSeveralLines($_,\@formulae, \@formulaeAssume);
	}
    } elsif ($ARGV[0] eq "-auto") {
	shift;
	$automaton = shift;
	unless ($automaton =~ /\.aut|\.l2a|\.uct|\.awt/) {
	    print "Wrong file extension of automata file. Use -h for more details.\n";
	    $automaton = "";
	}
    } elsif ($ARGV[0] eq "-m") {
	shift;
	$method = shift;
    } elsif ($ARGV[0] eq "-o") {
	shift;
	$optimize = shift;
    } elsif ($ARGV[0] eq "-ouct") {
	shift;
	$optimize_uct = shift;
    } elsif ($ARGV[0] eq "-oawt") {
	shift;
	$optimize_awt = shift;
    } elsif ($ARGV[0] eq "-oedges") {
	shift;
	$optimize_edges = shift;
    } elsif ($ARGV[0] eq "-orelease") {
	shift;
	$optimize_release = shift;
    } elsif ($ARGV[0] eq "-oreuse") {
	shift;
	$optimize_reuse = shift;
    } elsif ($ARGV[0] eq "-owit") {
	shift;
	$optimize_witness = shift;
    } elsif ($ARGV[0] eq "-omh") {
	shift;
	$optimize_mh = shift;
    } elsif ($ARGV[0] eq "-omhc") {
	shift;
	$combinedMH = shift;
    }  elsif ($ARGV[0] eq "-p") {
	shift;
	$prefix = shift;
    }elsif ($ARGV[0] eq "-s") {
	shift;
	$simplify = shift;
    }  elsif ($ARGV[0] eq "-v") {
	shift;
	$verb = shift;
    } elsif ($ARGV[0] eq "-ver") {
	shift;
	$verify = shift;
    } elsif ($ARGV[0] eq "-mon") {
	shift;
	$monitorFile = shift;
    } elsif ($ARGV[0] eq "-syn") {
	$synthesis = 1; 
	shift;
	my $partitionfile = shift;
	readPartition($partitionfile,\%partition);
    } elsif ($ARGV[0] eq "-syndir") {
	shift;
	$synthesisDir = shift; 
	$synthesisDir .= "/";
    } elsif ($ARGV[0] eq "-mc") {
   	shift;
	$mc = 1;
    } elsif ($ARGV[0] eq "-comp") {
	shift;
	$complementA = 1;
    } elsif ($ARGV[0] eq "-env") {
   	shift;
	$env = shift;
    } elsif ($ARGV[0] eq "-envauto") {
	shift;
	$env_automaton = shift;
	unless ($env_automaton =~ /\.aut|\.l2a/) {
	    print "Wrong file extension of automata file. Use -h for more details.\n";
	    $env_automaton = "";
	    die usage();
	}
    } elsif ($ARGV[0] eq "-pj") {
   	shift;
	$project = 1;
	my $file = shift;
	readPartition($file,\%partition);
	foreach (keys %partition) {
	    if ($partition{$_} eq 2) { #output variable
		$projectVars->Push($_);
	    }
	}
    } elsif ($ARGV[0] eq "-cc") {
   	shift;
	$cc = 1;
    } else {
	warn "unrecognized option: $ARGV[0]\n";
	shift;
    }
}
die helpMessage() if $help;
die usage() if (($env_automaton ne "" and $env ne 1) ||
		($env_automaton eq "" and $env eq 1));
die usage() if (@formulae == 0 and $automaton eq "");
die usage() if $#ARGV !=-1 or (@formulae == 0 and $automaton eq "");
die usage() if ($mc == 1 and $synthesis == 0) or
  (keys(%partition) == 0 and $synthesis == 1);
 
# Open output files
if ($synthesis == 0) {
    if ($automaton eq "") {
	open(PARSE, ">$prefix" . "-parse.dot");
	open(BUECHIAL, ">$prefix" . "-buechial.dot");
	open(L2A, ">$prefix" . "-buechial.l2a");
    }
    open(SCC, ">$prefix" . "-scc.dot");
    open(BUECHI, ">$prefix" . "-buechi.dot");
    open(COMPBUECHI, ">$prefix" . "-compbuechi.dot") if ($complementA);
    open(MONITOR, ">$monitorFile") if $monitorFile ne "";
}

if ($synthesis) {
    my $formulaAssume = "";
    my $formula = "";
    my $assume="";
    #First build the product of all formulas
    foreach my $form (@formulaeAssume) {
	$assume=1;
	if ($formulaAssume eq "") {
	    $formulaAssume = $form;
	} else {
	    $formulaAssume = "(".$form.")*(".$formulaAssume.")";
	}
	print "assume ".$form."\n" if $verb > 1;
    }

    foreach my $form (@formulae) {
	if ($formula eq "") {
	    $formula = $form;
	} else {
	    $formula = "(".$form.")*(".$formula.")";
	}
	print "assert ".$form."\n" if $verb > 1;
    }
    $formula = "(".$formulaAssume.") -> (".$formula.")" if ($formulaAssume);
    if ($sugar) {
	print "Write LTL equivalent to $ltlfile.\n";
	open(LTLF, ">$ltlfile") or die "Can't open $ltlfile : $!";
	print LTLF $formula.";\n";
	close(LTLF);
    }
    if ($assume) {
	print "Write LTL equivalent to $ltlfile.\n";
	system ("mkdir ".$synthesisDir) if (($synthesisDir ne "") and
					    (not -d $synthesisDir));
	open(LTLF, ">$synthesisDir formula.ltl-mc") or die "Can't open $synthesisDir formula.ltl-mc : $!";
	print LTLF $formula.";\n";
	$ltlfile="$synthesisDir formula.ltl-mc";
	close(LTLF);
    }
    my $synthesizer = LTL2VL->new( name      => $ltlfile,
				   formula   => $formula,
				   partition => \%partition,
				   directory => $synthesisDir,
				   prefix    => $prefix,
				   simplify  => $simplify,
				   method    => $method,
				   optimize_nbw  => $optimize,
				   optimize_uct  => $optimize_uct,
				   optimize_awt  => $optimize_awt,
				   optimize_witness  => $optimize_witness,
				   optimize_mh  => $optimize_mh,
				   optimize_edges => $optimize_edges,
				   optimize_release => $optimize_release,
				   optimize_reuse => $optimize_reuse,
				   combined => $combinedMH,
				   verbose   => $verb
				 );

    #clean previous outputfiles to avoid confusion
    $synthesizer->CleanOutputfiles;
    
    # make debug directory
    system ("mkdir ".$synthesisDir) if (($synthesisDir ne "") and
				    (not -d $synthesisDir));
    my $valid;
    $startTime = (times)[0];
    $nbwTime = (times)[0];

    if ($automaton =~ /\.awt/) {
 	print "Read an AWT automaton\n";
	my $moddate = sopen($automaton,\*AUTOMATON);
	my $aut = AlternatingTree->new(file => \*AUTOMATON);
	close AUTOMATON;
	$valid = $synthesizer->SetAWT($aut);
	goto EXIT unless $valid;
	$valid = $synthesizer->SynthesizeFromAWT($aut);
	goto EXIT unless $valid;
    } else {
	if ($automaton =~ /\.aut/) { #automaton has to be for not phi
	    print "Read NBW automaton\n";
	    my $moddate = sopen($automaton,\*AUTOMATON);
	    my $aut = Buechi->new(file => \*AUTOMATON);
	    close AUTOMATON;
	    $synthesizer->SetNBW($aut);
	    $valid = $synthesizer->BuildTransitionLabeledNBW;
	    goto EXIT unless $valid;
	    $nbwTime = (times)[0];
	    $valid = $synthesizer->BuildUCT;
	    goto EXIT unless $valid;
	} elsif ($automaton =~ /\.l2a/) {
	    print "Read a transition labeled NBW automaton\n";
	    my $moddate = sopen($automaton,\*AUTOMATON);
	    my $aut = BuechiAL->new(file => \*AUTOMATON);
	    close AUTOMATON;
	    $synthesizer->SetTransitionLabeledNBW($aut);
	    $nbwTime = (times)[0];
	    $valid = $synthesizer->BuildUCT;
	    goto EXIT unless $valid;
	} elsif ($automaton =~ /\.uct/) {
	    print "Read an UCT automaton\n";
	    my $moddate = sopen($automaton,\*AUTOMATON);
	    my $aut = CoBuechiTree->new(file => \*AUTOMATON);
	    close AUTOMATON;
	    $valid = $synthesizer->SetUCT($aut);
	    goto EXIT unless $valid;
	} else {
	    $valid = $synthesizer->BuildNBW;
	    my $env_aut;
	    if ($env == 2) {
		print "Compute class-two-realizability\n";
		$env_aut = $synthesizer->BuildPureAssumption($verb);
		$valid = $synthesizer->UseAssumption($env_aut);
	    } elsif ($env == 1) {
		if ($env_automaton =~ /\.aut/) { #automaton
		    print "Read input assumption (NBW)\n";
		    my $moddate = sopen($env_automaton,\*AUTOMATON);
		    $env_aut = Buechi->new(file => \*AUTOMATON);
		    close AUTOMATON;
		    $valid = $synthesizer->UseAssumption($env_aut);
		} elsif ($env_automaton =~ /\.l2a/) {
		    print "Read input assumption (tr-labeled NBW)\n";
		    my $moddate = sopen($env_automaton,\*AUTOMATON);
		    my $aut = BuechiAL->new(file => \*AUTOMATON);
		    close AUTOMATON;
		    if ($verb > 1) {
			open(ASSUME, ">$synthesisDir"."assume-al.dot");
			print ASSUME $aut->ToDot("Assumption");
			close ASSUME;
		    }
		    $env_aut = $aut->ToBuechi;
		    $valid = $synthesizer->UseAssumption($env_aut);
		} else {
		    die; #wrong automaton
		}
	    }
	    goto EXIT unless $valid;
	    $synthesizer->ApplyCountingConstruction;
	    $valid = $synthesizer->BuildTransitionLabeledNBW;
		#####
		exit(0); # STOP HERE FOR L2A (P_I)
		#####
	    goto EXIT unless $valid;
	    $nbwTime = (times)[0];
	    $valid = $synthesizer->BuildUCT;
	    goto EXIT unless $valid;
	}
	$valid = $synthesizer->SynthesizeFromUCT;
	goto EXIT unless $valid;
    }
    goto EXIT; ### STOP ICI AU PLUS TOT POUR AVOIR LES .AWT ET .L2A
	#$synTime = (times)[0];
    #$synthesizer->PrintModule;
    #if ($mc == 1) {
	#print "Modelcheck result...\n";
	#ModelCheck($ltlfile, $synthesisDir);
	#print "done\n";
    #}
    #goto EXIT; #end of synthesis
}

foreach my $formula (@formulae) {
    print '-' x 70, "\n", $formula, "\n", '-' x 70, "\n";
    my $parsetree = LTL->new($formula);
    print $parsetree->ToString, "\n" if $verb > 1;
    print $parsetree->ToDot($formula) if $verb > 3;
    my $normalized = $parsetree->Normalize;
    $normalized = $normalized->Simplify if $simplify;
    my $dot = $normalized->ToDot($parsetree->ToString);
    print PARSE $dot;
    print $normalized->ToString, "\n";
    my $result = LTL2AUT->new(formula => $normalized, method => $method);
    $result->Optimize($verb) if $optimize;
    if ($verify) {
	my $negation = $parsetree->Not->Normalize;
	my $complement = LTL2AUT->new(formula => $negation, method => $method);
	my $intersection = $result->Intersection($complement)->Prune;
	print "Intersection not empty!\n"
	  unless $intersection->NumberOfStates == 0;
	$result = $result->Union($complement);
	$result->Optimize($verb);
    }
    $result->MakeComplete if $complete;
#    print $result->ToString;
    print "Stats Buechi:   ", $result->Stats, "\n";

    if ($project) {
	print "Project to inputs, remove outputs=".$projectVars->ToString,"\n";
	$result->Project($projectVars);
	$result->Optimize($verb) if $optimize;
	print "Stats Buechi:   ", $result->Stats, "\n";
    }

    if ($cc && $result->{fair}->Size > 1) {
	print "Apply counting construction\n";
	$result = $result->CountingConstruction;
	$result->Optimize($verb) if $optimize;
	print "Stats Buechi:   ", $result->Stats, "\n";
    }
    print BUECHI $result->ToDot($formula);

    if ($complementA) {
	my $compResult = $result->Complement($verb);
	print COMPBUECHI $compResult->ToDot("comp");
    }
    if ($monitorFile ne "") {
	print MONITOR $result->ToVerilogMonitor;
    }
    my $quotient = $result->Quotient($result->SCC);
    print "SCC quotient graph:\n", $quotient->ToString if $verb > 2;
    print SCC $quotient->ToDot($formula);
    my $buechial = BuechiAL->fromBuechi($result);
    $buechial->DirectSimulationMinimization if $optimize;
    $buechial->FairSimulationMinimization if $optimize;
    print "Stats BuechiAL: ", $buechial->Stats, "\n";
    print BUECHIAL $buechial->ToDot($formula);
    print L2A $buechial->ToString($formula);
}
if ($automaton ne "") {
    my $moddate = sopen($automaton,\*AUTOMATON);
    my $result;
    if ($automaton =~ /\.l2a/) {
	$result = BuechiAL->new(file => \*AUTOMATON);
	$result->DirectSimulationMinimization if $optimize;
	$result->FairSimulationMinimization if $optimize;
    } else {
	$result = Buechi->new(file => \*AUTOMATON);
	$result->DirectSimulationMinimization if $optimize;
	$result->FairSimulationMinimization if $optimize;
    }
    close AUTOMATON;

    if ($complementA) {
	my $compResult = $result->Complement($verb);
	print COMPBUECHI $compResult->ToDot("comp");
    }
    print $result->ToString;
    print BUECHI $result->ToDot($automaton);
    if ($monitorFile ne "") {
	print MONITOR $result->ToVerilogMonitor;
    }
    my $quotient = $result->Quotient($result->SCC);
    print "SCC quotient graph:\n", $quotient->ToString if $verb > 2;
    print SCC $quotient->ToDot($automaton);
    print "Stats: ", $result->Stats, "\n";
}

EXIT:
close PARSE;
close BUECHI;
close BUECHIAL;
close L2A;
close COMPBUECHI;
close SCC;
close MONITOR if $monitorFile ne "";
my $endTime = (times)[0];
printf "NBW time: %.2f seconds\n",
  $nbwTime - $startTime if ($nbwTime > $startTime);
printf "Synthesis time: %.2f seconds\n",
  $synTime - $nbwTime if ($synTime>$nbwTime);
printf "Total time: %.2f seconds\n", $endTime - $startTime;

exit(0);

######################################################################
# Build a call-file to model check the synthesis result.
######################################################################
sub ModelCheck {
	my ($ltlfile, $synthesisDir) = @_;
	
	# Set Path to vis modelchecker
#	$ENV{'PATH'} = '/netshares/commons/verify/Software/bin';
		  
	open (CALL, ">$synthesisDir"."call-mc");
	print CALL "read_verilog $prefix-verilog.v\n";
	print CALL "init_verify\n";

	if ($synthesisDir ne "") {
	    print CALL "ltl_model_check ../$ltlfile\n";
	    system ("pushd $synthesisDir && vis -x -f call-mc && popd");
	} else {
	    print CALL "ltl_model_check $ltlfile\n";
	    system ("vis -x -f call-mc");
	}
	close CALL;
}

######################################################################
# Read LTL formulae from file and append them to a list.
######################################################################
sub readLTL {
    my ($file,$fref) = @_;
    my $moddate = sopen($file,\*FFILE);
    while (<FFILE>) {
	chop;				# discard newline
	s/\#.*//;			# discard comments
	s/;//;				# discard trailing semicolon
	s/\s+$//;			# discard trailing blanks
	push(@$fref,$_) unless /^\s*$/;	# skip empty lines
    }
    close(FFILE);

} # readLTL

######################################################################
# Read LTL formulae from file and append them to a list. Each formula
# can extend over several lines but has to end with a semicolon.
######################################################################
sub readLTLOverSeveralLines {
    my ($file,$fref,$aref) = @_;
    my $moddate = sopen($file,\*FFILE);
    my $formula ="";
    my $assume = 0;
    my %map;
    
    while (<FFILE>) {
	chop;				# discard newline
	s/\#.*//;			# discard comments
	s/\s+$//;			# discard trailing blanks
	if (/\\define[\s]+([\w\.\_\d]+) (.+)/) {
	    my $key = $1;
	    my $value = $2;
# 	    print "Definition found: ", $key,"\n";
	    if ($value =~ /\\/) {
		foreach my $key (keys %map) {
		    my $val = $map{$key};
		    $value =~ s/\\$key/$val/g;
		}
	    }
	    #check if the new $key has a sub or super-key
	    foreach (keys %map) {
		if ((/^$key/) || ($key =~ /^$_/)) {
		    print "Two define-keys are too similar: $key, $_\n";
		    exit 1;
		}
	    }
	    $map{$key} = $value;
	} else {
	    $formula .= $_;
	    if (/;/) {
		$formula =~ s/;//;		# discard trailing semicolon
		$formula =~ s/assert //;    # discard 'assert' keyword
		$assume = 1 if ($formula =~ s/assume //);
		$formula =~ s/\s+$//;	# discard trailing blanks
		if (/\\/) {
# 		    print "Macros found: ", $formula,"\n";
		    foreach my $key (keys %map) {
			my $val = $map{$key};
			$formula =~ s/\\$key/$val/g;
		    }
# 		    print $formula,"\n";
		}
		if ($assume) {
		    push(@$aref,$formula) unless ($formula =~ /^\s*$/);# skip empty lines
		} else { #default
		    push(@$fref,$formula) unless ($formula =~ /^\s*$/);# skip empty lines
		}
		$formula="";
		$assume = 0;
	    }
	}
    }
    if ($formula ne "") {
       print "Warning reading LTL formulae: Semicolon missing\n";
    }
    close(FFILE);

} # readLTL


######################################################################
# Read IO partitioning from file and store it in a hash table.
# '1' is an input
# '2' is an output
######################################################################
sub	readPartition {
	my ($partitionfile,$partition) = @_;
	open( FILE, $partitionfile);
	my @lines = <FILE>;
	die error("PartitionFileError") if (not @lines);
	close FILE;
	my $iovalue = 0;
	print  @lines." Lines read from partition-file '".$partitionfile."'" if $verb > 1;

L:	foreach my $line (@lines) {
		my @elems = split(/ +/,$line);
		#print "----\n".@elems.": ".$line;
		foreach (@elems) {
			next L if (/(\#.*)/);
			if (/( )|(\n)/) {
			  chop;
			}
			next if (not $_);
			if (/\.inputs/) {
				print "\ninputs: ";
				$iovalue = 1;
			} elsif (/\.outputs/) {
				print "\noutputs: ";
				$iovalue = 2;
			} else {
				next if ($iovalue == 0);
				print $_." ";
				$$partition{$_} = $iovalue;
			}
		}
	}
	print "\n";
	die error("PartitionEmpty") if (keys(%$partition) == 0);
} #readPartition


######################################################################
# Return the usage message.
######################################################################
sub error {
	$_ = shift;
	if (not $_) {
		return usage() . "General error\n";
	}
	if (/PartitionFileError/) {
		return usage() . <<EOF;
Error reading partition file.
EOF
	}
	
	if (/LTLFileEmpty/) {
	print usage() . <<EOF;
File containing the ltl formulas is empty.
EOF
	}

	if (/PartitionEmpty/) {
	print usage() . <<EOF;
I/O-partition is empty.
EOF
	}	
}

######################################################################
# Return the usage message.
######################################################################
sub usage {
    return <<EOF;
Usage: $0 [-c {0,1}] [-cc] [-f formula] [-h] [-ltl file]
       [-m method] [-o {0,1}] [-p prefix] [-s {0,1}] [-v n]
       [-ver {0,1}] [-auto file] [-mon file]
       [-syn file] [-syndir synthesisDir] [-mc]
       [-ouct {0,1}] [-oawt {0,1}] [-owit {0,1}]
       [-omh {0,1}] [-omhc {0,1}]
       [-oedges {0,1}] [-orelease {0,1}] [-oreuse {0,1}]
       [-env {0,1,2}] [-pj file] [-envauto file]
EOF

} # usage


######################################################################
# Return the help message.
######################################################################
sub helpMessage {
    return usage() . <<EOF;

-c {0,1}  : Iff n != 0, make the transition relation of the automaton complete
            (off by default).
-cc       : Apply counting construction
-comp	  : Build Buechi automaton and its complement for the given LTL formula.
-env {0,1,2}: Check different types of realizability
            0 ... realizability (default)
            1 ... realizabily under assumption L (automaton given with -envauto)
            2 ... class-two-realizability
-envauto file: Automaton specifying the input assumption.
            Use only the following file-extensions
            aut ...for reading a state labeled NBW
            l2a ...for reading a transition labeled NBW
-f formula: The LTL formula to be translated.  Use either -ltl or -f.
-h        : gives this help.
-ltl file : file containing the LTL formulae to be ranslated.
            Use either -ltl or -f.
-m method : Sets the method used in translation.  Method ranges over
            GPVW, GPVW+, LTL2AUT, Boolean.  Default is Boolean.
-o {0,1}  : Optimize the automaton after translation, using simulation
            relations. On by default.
-ouct {0,1}: Optimize the universal cobuechi tree automaton,
             using simulation relations. On by default.
-oawt {0,1}: Optimize the alternating weak tree automaton,
             using simulation relations. On by default.
-owit {0,1}: Optimize the witness/strategy, using simulation
             relations. On by default.
-omh  {0,1}: Use Fritz optimizations during MH construction.
-omhc {0,1}: Combine MH construction with language emptiness check.
-oedges {0,1}: Merge edges
-orelease {0,1}: Restrict release function to stay in odd layer if possible.
-oreuse {0,1}: Reuse the result from previous computations with lower ranks.
-p prefix : Sets the prefix of the files that are written.  Default: ltl2aut.
-pj file  : Project the automaton to the input signals given in the file
-s {0,1}  : Iff n != 0, simplify the formula before translating it, using
            rewriting.  On by default.
-v n      : Sets the verbosity level (0 <= n <= 4, default is 1).
-ver{0,1} : Iff n!= 0, make an attempt at verifying the automaton.
            Off by default.
-auto file: Optimizes an automaton described in file.
            Use only the following file-extensions
            aut ...for reading a state labeled NBW
            l2a ...for reading a transition labeled NBW
            uct ...for reading an UCT
-mon file : Write a Verilog monitor to file.
-syn file : Synthesizes the given ltl formula to Verilog code using the 
	    IO-partition stored in the given file.
-syndir dn: Only valid with -syn option. dn is the directory name where all
	    (temporal) results of the synthesis process are stored. Default 
	    value is 'synthesis'.
-mc       : Only valid with -syn option. Modelchecks the result of the 
            synthesis process using VIS.

This is Wring, by Fabio Somenzi, University of Colorado.  No warranty
is given for the correctness of this code or its suitability for any
purpose.  Given an LTL formula, creates a Buechi automaton that
accepts exactly those traces that satisfy the formula.  See [SB00] for
a description of the algorithm.  Wring incorporates the algorithms of
[GPVW95] and [DGV99], as special cases.  The program writes three
files: prefix-parse.dot, prefix-buechi.dot, and prefix-scc.dot.  These
files hold the graphs of the parse tree, the Buechi automaton, and the
SCC-quotient graphs of the automaton respectively.  They are in dot
format, which can be translated using dot.  Please learn the syntax of
LTL formulae from the examples below.

Examples:

ltl2aut.pl -f '!(p=1 U (q=1 U r=1))' -p wring
Produces the automaton for the formula using wring, the strongest algorithm.
Equivalent to:
ltl2aut.pl -f '!(p=1 U (q=1 U r=1))' -p wring -m Boolean -s 1 -o 1

ltl2aut.pl -f '(G(F(p=1))) -> (G(F(q=1)))' -p wring -s 0 -o 0 -m LTL2AUT -v 4
Produces the automaton for the formula in the manner of [DGV99].

ltl2aut.pl -f '(F(p=1)) U (G(q=1))' -p wring -s 0 -o 0 -m GPVW -v 0
Produces the automaton for the formula in the manner of [GPVW95].

NB: The algorithm uses hash tables extensively, which makes it sensitive to
memory issues.  Results may be different between a run that uses -s 1 and and
run that does not, even though -s 1 is the default, because specifying options
shifts data in memory.

EOF

} # helpMessage
