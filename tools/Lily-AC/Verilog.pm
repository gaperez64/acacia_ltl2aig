# $Id: Verilog.pm,v 1.2 2005/09/26 11:44:23 bjobst Exp $

######################################################################
# Functions to translate Buechi automata into Verilog monitors.
#
# Author: Fabio Somenzi <Fabio@Colorado.EDU>
#
######################################################################
package Buechi;

use strict;

######################################################################
# Convert a Buechi automaton to a Verilog monitor.
# The inputs to the monitor are the names appearing in the labels of
# the states of the automaton.
# The outputs correspond to the fairness constraints.  If there are no
# fairness constraints, an output called "safe" is created, which is 1
# whenever the monitor is not in the trap state.
# An initial state and a trap state are added if necessary.
# The trap state is added only if the transition relation is not complete.
# The initial state is introduced only if there is no initial state of
# the automaton such that its successors are exactly all the initial
# states.
######################################################################
sub ToVerilogMonitor {
    my ($self, $suffix) = @_;
    my $states = $$self{states};
    my $delta = $$self{delta};
    my $init = $$self{init};
    my $names = $$self{names};
    my $fair = $$self{fair};
    $suffix = "" unless defined $suffix;
    my $modulename = "Buechi" . $suffix;
    my $typename = "states" . $suffix;

    # Build lists of inputs, outputs, and states.
    my @inputs = @{$self->GetInputs};
    my @outputs = @{$self->GetOutputs};
    my @states = map {$$names{$_}} values %{$states};

    # Build state transition functions.  In the process, collect
    # nondeterministic assignments and corresponding wire declarations
    # in a hash table.
    my $ndAssign = {};
    my $stateCases = {};
    my $nsString = qq!  always @ (posedge clock) begin\n    case (state)\n!;
    # Check whether we can avoid introducing a separate initial state.
    my $initName = "Init";
    foreach my $state (values %{$init}) {
	my $succ = $$delta{$state};
	if ($succ->IsEqual($init)) {
	    $initName = $$names{$state};
	    last;
	}
    }
    if ($initName eq "Init") {
	$self->BuildInit($init,$ndAssign,$stateCases,$typename);
	unshift(@states, "Init");
    }
    foreach my $state (values %{$states}) {
	$self->BuildNSFunction($state,$ndAssign,$stateCases,$typename);
    }
    # Check whether trap state necessary.
    foreach my $case (keys %{$stateCases}) {
	if ($case =~ /Trap/) {
	    my $assign = "\tstate = Trap;\n";
	    if (exists $$stateCases{$assign}) {
		$$stateCases{$assign} = $$stateCases{$assign} . ",Trap";
	    } else {
		$$stateCases{$assign} = "Trap";
	    }
	    push(@states, "Trap");
	    last;
	}
    }
    # Create the body of the "always" block.
    foreach my $case (keys %{$stateCases}) {
	$nsString .= "      " . $$stateCases{$case} . ":\n" . $case;
    }
    $nsString .= qq!    endcase\n  end\n!;
    # Create list of wire declarations and nondeterministic assignments.
    my $assignString = "";
    my $wireString = "";
    foreach my $assign (keys %{$ndAssign}) {
	$assignString .= $assign;
	$wireString .= $$ndAssign{$assign};
    }

    # Build output functions.
    my $fairString = "";
    if ($fair->Size == 0) {
	if ($states[$#states] eq "Trap") {
	    $fairString .= qq%  assign safe = (state != Trap);\n%;
	} else {
	    $fairString .= qq%  assign safe = 1;\n%;
	}
    } else {
	my $i = 0;
	foreach my $fairset (values %{$fair}) {
	    $fairString .= qq!  assign $outputs[$i] = !;
	    my $delim = "";
	    foreach my $state (values %{$fairset}) {
		$fairString .= $delim . "(state == " . $$names{$state} . ")";
		$delim = " || ";
	    }
	    $fairString .= ";\n";
	}
    }

    # Assemble monitor description.
    # Declare an enumerated type for the FSM states.
    my $string = qq!typedef enum {! . join(',', @states) .
      qq!} $typename;\n\n!;

    # Open module definition.
    my $inputString = join(',', ("clock", @inputs));
    my $outputString = join(',', @outputs);
    $string .= qq!module $modulename($inputString,$outputString);\n! .
      qq!  input $inputString;\n  output $outputString;\n!;

    # Add register and wire declarations, continuous assignments, and
    # state initialization.
    $string .= qq!  $typename reg state;\n!;
    $string .= $wireString;
    $string .= $assignString;
    $string .= $fairString;
    $string .= qq!  initial state = $initName;\n!;

    # Add "always" block.
    $string .= $nsString;
    # Close module definition.
    $string .= qq!endmodule // $modulename\n!;
    return $string;

} # ToVerilogMonitor


######################################################################
# Build the case for one non-initial state.
######################################################################
sub BuildNSFunction {
    my ($self,$state,$ndAssign,$stCases,$typename) = @_;
    my $delta = $$self{delta};
    my $names = $$self{names};
    my $succ = $$delta{$state};
    my $name = $$names{$state};
    my $assign = $self->BuildAssign($succ,$ndAssign,$typename);
    if (exists $$stCases{$assign}) {
	$$stCases{$assign} = $$stCases{$assign} . "," . $name;
    } else {
	$$stCases{$assign} = $name;
    }
    return;

} # BuildNSFunction


######################################################################
# Builds the case for the initial state.
######################################################################
sub BuildInit {
    my ($self,$init,$ndAssign,$stCases,$typename) = @_;
    my $names = $$self{names};
    my $assign = $self->BuildAssign($init,$ndAssign,$typename);
    if (exists $$stCases{$assign}) {
	$$stCases{$assign} = $$stCases{$assign} . ",Init";
    } else {
	$$stCases{$assign} = "Init";
    }
    return;

} # BuildInit


######################################################################
# Builds assignment for a state.
######################################################################
sub BuildAssign {
    my ($self,$states,$ndAssign,$typename) = @_;
    my $names = $$self{names};
    my @inputs = sort @{$self->GetInputs($states)};
    my $string = "\t";
    my $ninputs = @inputs;
    if ($ninputs) {
	my $inputString = join(',', @inputs);
	$string .= ($ninputs == 1) ? qq!case ($inputString)\n! :
	  qq!case (\{$inputString\})\n!;
	my $cases = $self->BuildCase(\@inputs,$states,$ndAssign,$typename);
	foreach my $case (@$cases) {
	    $string .= "\t" . $ninputs . "'b" . $case;
	}
	$string .= qq!\tendcase\n!;
    } else {
	if ($states->Size == 1) {
	    my $state = $states->Pick;
	    $string .= "state = " . $$names{$state} . ";\n";
	} elsif ($states->Size == 0) {
	    $string .= "state = Trap;\n";
	} else {
	    my @names = ();
	    foreach my $state (values %{$states}) {
		push(@names, $$names{$state});
	    }
	    @names = sort @names;
	    my $wireName = "ND_" . join( "_", @names);
	    my $wire = "  $typename wire $wireName;\n";
	    my $assign =  "  assign $wireName = \$ND(" .
	      join(",", @names) . ");\n";
	    $$ndAssign{$assign} = $wire;
	    $string .= qq!state = $wireName;\n!;
	}
    }
    return $string;

} # BuildAssign


######################################################################
# Recursively builds case statement.
######################################################################
sub BuildCase {
    my ($self,$inputs,$states,$ndAssign,$typename) = @_;
    my @cases = ();
    my $names = $$self{names};
    if (@$inputs == 0) {
	if ($states->Size == 1) {
	    my $state = $states->Pick;
	    push(@cases, ": state = " . $$names{$state} . ";\n");
	} elsif ($states->Size == 0) {
	    push(@cases, ": state = Trap;\n");
	} else {
	    my @names = ();
	    foreach my $state (values %{$states}) {
		push(@names, $$names{$state});
	    }
	    @names = sort @names;
	    my $wireName = "ND_" . join( "_", @names);
	    my $wire = "  $typename wire $wireName;\n";
	    my $assign =  "  assign $wireName = \$ND(" .
	      join(",", @names) . ");\n";
	    $$ndAssign{$assign} = $wire;
	    push(@cases, ": state = $wireName;\n");
	}
    } else {
	# Split the state set on the first input and recur.
	my @copy = @$inputs;
	my $input = shift(@copy);
	my $ratom = LTL->new($input . "=" . "0");
	my $rstates = $self->SelectStates($ratom,$states);
	my $rcases = $self->BuildCase(\@copy,$rstates,$ndAssign,$typename);
	my $latom = LTL->new($input . "=" . "1");
	my $lstates = $self->SelectStates($latom,$states);
	my $lcases = $self->BuildCase(\@copy,$lstates,$ndAssign,$typename);
	# Attempt some distance-one merging of the cases.
	for (my $i = 0; $i < @$rcases; $i++) {
	    my $rcase = $$rcases[$i];
	    if (defined $$lcases[$i] and $$lcases[$i] eq $rcase) {
		$rcase = "?" . $rcase;
		push(@cases,$rcase);
		$$lcases[$i] = "";
	    } else {
		$rcase = "0" . $rcase;
		push(@cases,$rcase);
	    }
	}
	foreach my $lcase (@$lcases) {
	    if ($lcase ne "") {
		$lcase = "1" . $lcase;
		push(@cases,$lcase);
	    }
	}
    }
    return \@cases;

} # BuildCase


######################################################################
# Select the states from the given set that are not in contradiction
# with the give atom.
######################################################################
sub SelectStates {
    my ($self,$atom,$states) = @_;
    my $labels = $$self{labels};
    my $select = Set->new;
    my $negation = $atom->Negate;
    foreach my $state (values %{$states}) {
	my $label = $$labels{$state};
	unless ($label->IsMember($negation)) {
	    $select->Push($state);
	}
    }
    return $select;

} # SelectStates


######################################################################
# Get the inputs appearing in the labels of a set of states.
# Return a reference to a list that is lexicographically sorted.
######################################################################
sub GetInputs {
    my ($self,$set) = @_;
    unless (defined $set) {
	$set = $$self{states};
    }
    my $labels = $$self{labels};
    my $inputs = Set->new;
    my @inputs = ();
    foreach my $state (values %{$set}) {
	my $label = $$labels{$state};
	foreach my $atom (values %{$label}) {
	    my $value = $atom->Value;
	    $value =~ s/=.*//;
	    unless ($inputs->IsMember($value)) {
		$inputs->Push($value);
		push(@inputs,$value);
	    }
	}
    }
    @inputs = sort {$a cmp $b} @inputs;
    return \@inputs;

} # GetInputs


######################################################################
# Get the outputs of a monitor.
######################################################################
sub GetOutputs {
    my $self = shift;
    my $fair = $$self{fair};
    my @outputs = ();
    if ($fair->Size == 0) {
	push(@outputs, "safe");
    } elsif ($fair->Size == 1) {
	push(@outputs, "fair");
    } else {
	for (my $i = 0; $i < $fair->Size; $i++) {
	    push(@outputs, "fair" . $i);
	}
    }
    return \@outputs;

} # GetOutputs

# Required return value.
1;
