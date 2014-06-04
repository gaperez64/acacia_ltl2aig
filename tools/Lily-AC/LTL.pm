# $Id: LTL.pm,v 1.2 2005/09/26 11:44:23 bjobst Exp $

######################################################################
# This module defines class LTL whose objects are LTL parse trees.
# Method "new" takes a string representing a LTL formula as input and
# produces a parse graph.
#
# The syntax for LTL is:
#
# FORMULA    ::= TERM { BINARYOP TERM }
# TERM       ::= {ATOM | (FORMULA) |
#                UNARYOP FORMULA | TEMPORALOP (FORMULA)};
# BINARYOP   ::= * | + | ^ | -> | <-> | U | R | V
# UNARYOP    ::= !
# TEMPORALOP ::=  G|F|X
# ATOM       ::= VARIABLE = VALUE
# VARIABLE   ::= \w+
# VALUE      ::= 0 | 1
#
# Each node of the parse graph has five fields:
#   type:  one of atom, binaryop, unaryop, temporalop.
#   value: the token attached to the node; e.g., "G" or "a=1".
#   left:  the left child of the node, or the only child if there is only one.
#   right: the right child of the node.
#   mark:  field use to mark selected nodes.
# The two children may not exist.
#
# The package guarantees that each node is unique.
#
# Authors: Santhosh Heddese <santhosh.heddese@colorado.edu>
#          Fabio Somenzi <Fabio@Colorado.EDU>
######################################################################

package LTL;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK %uniqueTable);
@ISA       = qw(Exporter);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
use strict;


######################################################################
# Create a new parse tree from a string representing a LTL formula.
######################################################################
sub new {
    my ($class,$string) = @_;
    $string =~ s/\s+//g;
    my $self;
    ($self,$string) = Formula($string);
    die "syntax error: $string\n" unless $string eq "";
    return $self;

} # new


######################################################################
# Maintains canonical representation.
######################################################################
sub findOrAdd {
    my ($type,$value,$left,$right) = @_;
    my $lefthash = defined($left) ? $left : "";
    my $righthash = defined($right) ? $right : "";
    my $key = join(',',$type,$value,$lefthash,$righthash);
    if (defined($uniqueTable{$key})) {
	return $uniqueTable{$key};
    }
    my $new = {
	       type => $type,
	       value => $value
	      };
    $$new{left}  = $left if defined($left);
    $$new{right} = $right if defined($right);
    $uniqueTable{$key} = $new;
    return bless $new;

} # findOrAdd


######################################################################
# Parses a formula.
######################################################################
sub Formula {
    my $string = shift;
    my $substring;
    my $treenode;
    my $right;
    ($treenode,$string) = Term($string);
    while ((($substring,$string) = BinaryOp($string))[0] ne "") {
	($right,$string) = Term($string);
	my $left = $treenode;
	$treenode = findOrAdd('binaryop', $substring, $left, $right);
    }
    return ($treenode,$string);

} # Formula


######################################################################
# Parses a term.
######################################################################
sub Term {
    my $string = shift;
    my $substring;
    my $treenode;
    my $child;
    if ((($substring,$string) = Atom($string))[0] ne "") {
	$treenode = findOrAdd('atom', $substring, undef, undef);
    } elsif ($string =~ s/^\(//) {
	($treenode,$string) = Formula($string);
	$string   =~ s/^\)// || die "Missing right paren: $string\n";
    } elsif ((($substring,$string) = UnaryOp($string))[0] ne "") {
	($child,$string)    = Formula($string);
	$treenode = findOrAdd('unaryop', $substring, $child, undef);
    } elsif ((($substring,$string) = TemporalOp($string))[0] ne "") {
	($child,$string)    = Formula($string);
	$string   =~ s/^\)// || die "Missing right paren: $string\n";
	$treenode = findOrAdd('temporalop', $substring, $child, undef);
    }
    return ($treenode,$string);

} # Term


######################################################################
# Parses a binary propositional or until operator.
######################################################################
sub BinaryOp {
    my $string = shift;
    my $substring;
    if ($string =~ s/^(\+|\*|\^|->|<->|U|R|V)//) {
	$substring = $1;
	$string    = $';
    } else {
	$substring = "";
    }
    return ($substring,$string);

} # BinaryOp


######################################################################
# Parses a unary propositional operator.
######################################################################
sub UnaryOp {
    my $string = shift;
    my $substring;
    if ($string =~ s/^(!)//) {
	$substring = $1;
	$string    = $';
    } else {
	$substring = "";
    }
    return ($substring,$string);

} # UnaryOp


######################################################################
# Parses a temporal operator.
######################################################################
sub TemporalOp {
    my $string = shift;
    my $substring;
    if ($string =~ s/^(G|F|X)\(//) {
	$substring = $1;
	$string    = $';
    } else {
	$substring = "";
    }
    return ($substring,$string);

} # TemporalOp


######################################################################
# Parses an atom.
######################################################################
sub Atom {
    my $string = shift;
    my $substring;
    if ($string =~ s/^(TRUE|FALSE)//) {
	$substring = $1;
	$string = $';
    } elsif ($string =~ s/^([\w<>]+\s*=\s*[01])//) {
	$substring = $1;
	$string    = $';
    } else {
	$substring = "";
    }
    return ($substring,$string);

} # Atom


######################################################################
# Builds a string in dot format from a LTL parse graph.
######################################################################
sub ToDot {
    my ($root,$name) = @_;
    my $dot = qq!digraph "$name" {\nordering=out;\nnode [shape=circle];\n!;
    my %visited = ();
    my ($ndot,$key) = tree2dotInt($root,0,\%visited);
    $dot .= qq!size = \"7.5,10\"\ncenter = true;\n!;
    $dot .= qq!"title" [label=\"$name\",shape=plaintext];\n! . $ndot . qq!}\n!;

} # ToDot


######################################################################
# DFS procedure to build the dot string from the LTL parse graph.
######################################################################
sub tree2dotInt {
    my ($root,$key,$visited) = @_;
    if (defined($$visited{$root})) {
	return ("",$$visited{$root});
    }
    my ($lstring,$lkey) = (defined($$root{left})) ?
      tree2dotInt($$root{left},$key,$visited) :
	("",$key);
    $key = $key > $lkey ? $key : $lkey;
    my ($rstring,$rkey) = (defined($$root{right})) ?
      tree2dotInt($$root{right},$key,$visited) :
	("",$key);
    $key = $key > $rkey ? $key+1 : $rkey+1;
    $$visited{$root} = $key;
    my $string = qq!"$key" [label=\"$$root{value}\"];\n!;
    $string .= qq!"$key" -> "$lkey";\n! if defined($$root{left});
    $string .= qq!"$key" -> "$rkey";\n! if defined($$root{right});
    $string .= $lstring . $rstring;
    return ($string,$key);

} # tree2dotInt


######################################################################
# Convert a parse graph to a string.
######################################################################
sub ToString {
    my $self = shift;
    my $string = "";
    my $type = $self->Type;
    if ($type eq 'atom') {
	return $self->Value;
    } elsif ($type eq 'unaryop' || $type eq 'temporalop') {
	return $self->Value . "(" . ToString($self->Left) . ")";
    } elsif ($type eq 'binaryop') {
	return "(" . ToString($self->Left) . ")" . $self->Value .
	  "(" . ToString($self->Right) . ")";
    }
    return $string;

} # ToString


######################################################################
# Access function for the node type.
######################################################################
sub Type {
    my $self = shift;
    return $self->{type};

} # Type


######################################################################
# Access function for the node value.
######################################################################
sub Value {
    my $self = shift;
    return $self->{value};

} # Value


######################################################################
# Access function for the node left child.
######################################################################
sub Left {
    my $self = shift;
    return $self->{left};

} # Left


######################################################################
# Access function for the node right child.
######################################################################
sub Right {
    my $self = shift;
    return $self->{right};

} # Right


######################################################################
# Access function for the node mark field.
######################################################################
sub IsMarked {
    my $self = shift;
    return exists($self->{mark});

} # Mark


######################################################################
# Put a LTL parse tree in positive (negation) normal form.
######################################################################
sub Normalize {
    my $self = shift;
    my $exp = $self->ExpandAbbreviations;
    return $exp->PushNegations;

} # Normalize


######################################################################
# Expand abbreviations in a LTL parse tree.
######################################################################
sub ExpandAbbreviations {
    my $self = shift;
    my $type = $self->Type;
    my $value = $self->Value;
    if ($type eq 'atom') {
	return $self;
    } elsif ($type eq 'binaryop') {
	my $left =  $self->Left->ExpandAbbreviations;
	my $right =  $self->Right->ExpandAbbreviations;
	if ($value eq '*' || $value eq '+' || $value eq 'U' ||
	   $value eq 'R' || $value eq 'V') {
	    # In these cases we only need to recursively expand the
	    # two children.
	    $value = 'R' if $value eq 'V';
	    return findOrAdd('binaryop', $value, $left, $right);
	} elsif ($value eq '->') {
	    # Here we apply p -> q = !p + q.
	    my $neg = findOrAdd('unaryop', '!', $left, undef);
	    return findOrAdd('binaryop', '+', $neg, $right);
	} elsif ($value eq '^') {
	    # The expansion of the exclusive OR and of the equivalence
	    # transforms the parse tree into a DAG.
	    my $negl = findOrAdd('unaryop', '!', $left, undef);
	    my $negr = findOrAdd('unaryop', '!', $right, undef);
	    my $cnj1 = findOrAdd('binaryop', '*', $left, $negr);
	    my $cnj2 = findOrAdd('binaryop', '*', $negl, $right);
	    return findOrAdd('binaryop', '+', $cnj1, $cnj2);
	} elsif ($value eq '<->') {
	    # transforms the parse tree into a DAG.
	    my $negl = findOrAdd('unaryop', '!', $left, undef);
	    my $negr = findOrAdd('unaryop', '!', $right, undef);
	    my $cnj1 = findOrAdd('binaryop', '*', $left, $right);
	    my $cnj2 = findOrAdd('binaryop', '*', $negl, $negr);
	    return findOrAdd('binaryop', '+', $cnj1, $cnj2);
	}
    } elsif ($type eq 'unaryop') {
	die "unexpected unary operator\n" unless $value eq '!';
	my $left =  $self->Left->ExpandAbbreviations;
	return findOrAdd('unaryop', '!', $left, undef);
    } elsif ($type eq 'temporalop') {
	my $left =  $self->Left->ExpandAbbreviations;
	if ($value eq 'X') {
	    return findOrAdd('temporalop', 'X', $left, undef);
	} elsif ($value eq 'F') {
	    my $true = findOrAdd('atom', 'TRUE', undef, undef);
	    return findOrAdd('binaryop', 'U', $true, $left);
	} elsif ($value eq 'G') {
	    my $false = findOrAdd('atom', 'FALSE', undef, undef);
	    return findOrAdd('binaryop', 'R', $false, $left);
	} else {
	    die "unexpected temporalop node in ExpandAbbreviations\n";
	}
    } else {
	die "unexpected node type in ExpandAbbreviations\n";
    }

} # ExpandAbbreviations


######################################################################
# Push negations to the leaves in the parse tree of a LTL formula.
# This function can be applied also to LTL parse trees that still
# contain abbreviations, though in normal use the abbreviations are
# expanded before calling this function.
######################################################################
sub PushNegations {
    my $self = shift;
    my $type = $self->Type;
    my $value = $self->Value;
    if ($type eq 'unaryop') {
	die "unexpected unary operator\n" unless $value eq '!';
	my $child = $self->Left;
	my $ctype = $child->Type;
	my $cvalue = $child->Value;
	if ($ctype eq 'unaryop') { # involution: a'' = a
	    die "unexpected unary operator\n" unless $cvalue eq '!';
	    my $grandchild = $child->Left;
	    return $grandchild->PushNegations;
	} elsif ($ctype eq 'temporalop') {
	    my $grandchild = $child->Left;
	    my $neg = findOrAdd('unaryop', '!', $grandchild, undef);
	    my $recur = $neg->PushNegations;
	    if ($cvalue eq 'X') {
		return findOrAdd($ctype, $cvalue, $recur, undef);
	    } elsif ($cvalue eq 'G') {
		return findOrAdd($ctype, 'F', $recur, undef);
	    } elsif ($cvalue eq 'F') {
		return findOrAdd($ctype, 'G', $recur, undef);
	    } else {
		die "unexpected temporal operator\n";
	    }
	} elsif ($ctype eq 'binaryop') {
	    # We divide the operators into those for which we can
	    # push down the negation by negating one of the operands,
	    # and those for which we need to negate both operands.
	    # For '^' and '<->' we could simply swap the operators,
	    # but this would introduce a third class.
	    my ($left,$right);
	    my $grandchild = $child->Right;
	    my $neg = findOrAdd('unaryop', '!', $grandchild, undef);
	    $right = $neg->PushNegations;
	    if ($cvalue eq '^' || $cvalue eq '<->' || $cvalue eq '->') {
		$left = $child->Left->PushNegations;
		return findOrAdd($ctype,($cvalue eq '->' ? '*' : $cvalue),
				 $left, $right);
	    }
	    $grandchild = $child->Left;
	    $neg = findOrAdd('unaryop', '!', $grandchild, undef);
	    $left = $neg->PushNegations;
	    if ($cvalue eq '+') {
		return findOrAdd($ctype, '*', $left, $right);
	    } elsif ($cvalue eq '*') {
		return findOrAdd($ctype, '+', $left, $right);
	    } elsif ($cvalue eq 'U') {
		return findOrAdd($ctype, 'R', $left, $right);
	    } elsif ($cvalue eq 'R' || $cvalue eq 'V') {
		return findOrAdd($ctype, 'U', $left, $right);
	    } else {
		die "unexpected binary operator\n";
	    }
	} elsif ($ctype eq 'atom') {
	    # Our atoms are of the form var=val, with val either 0 or 1.
	    # The only exceptions are TRUE and FALSE.  Hence, we just
	    # swap 0's and 1's, and TRUE and FALSE.  As a result, the
	    # negation nodes completely disappear from the formula.
	    my $newvalue;
	    if ($cvalue =~ /=1/) {
		($newvalue = $cvalue) =~ s/=1/=0/;
	    } elsif ($cvalue =~ /=0/) {
		($newvalue = $cvalue) =~ s/=0/=1/;
	    } elsif ($cvalue eq 'TRUE') {
		$newvalue = 'FALSE';
	    } elsif ($cvalue eq 'FALSE') {
		$newvalue = 'TRUE';
	    } else {
		die "unexpected atom\n";
	    }
	    return findOrAdd($ctype, $newvalue, undef, undef);
	} else {
	    die "unexpected child of unary operator\n";
	}
    } elsif ($type eq 'binaryop') {
	# In this case and the next we just need to push down the
	# negations recursively.
	my $left = $self->Left->PushNegations;
	my $right = $self->Right->PushNegations;
	return findOrAdd($type, $value, $left, $right);
    } elsif ($type eq 'temporalop') {
	my $left = $self->Left->PushNegations;
	return findOrAdd($type, $value, $left, undef);
    } elsif ($type eq 'atom') {
	return $self;
    } else {
	die "unexpected type\n";
    }

} # PushNegations


######################################################################
# Create a tree for the negation of self in normal form.
######################################################################
sub Negate {
    my $self = shift;
    return $self->Not->PushNegations;

} # Negate


######################################################################
# Create a tree for X self.
######################################################################
sub X {
    my $self = shift;
    return findOrAdd('temporalop', 'X', $self, undef);

} # X


######################################################################
# Create a tree for G self.
######################################################################
sub G {
    my $self = shift;
    return findOrAdd('temporalop', 'G', $self, undef);

} # G


######################################################################
# Create a tree for G self.
######################################################################
sub F {
    my $self = shift;
    return findOrAdd('temporalop', 'F', $self, undef);

} # F


######################################################################
# Create a tree for not self.
######################################################################
sub Not {
    my $self = shift;
    return findOrAdd('unaryop', '!', $self, undef);

} # Not


######################################################################
# Create a tree for self and other.
######################################################################
sub And {
    my ($self,$other) = @_;
    return findOrAdd('binaryop', '*', $self, $other);

} # And


######################################################################
# Create a tree for self or other.
######################################################################
sub Or {
    my ($self,$other) = @_;
    return findOrAdd('binaryop', '+', $self, $other);

} # Or


######################################################################
# Create a tree for self until other.
######################################################################
sub U {
    my ($self,$other) = @_;
    return findOrAdd('binaryop', 'U', $self, $other);

} # U


######################################################################
# Create a tree for self releases other.
######################################################################
sub R {
    my ($self,$other) = @_;
    return findOrAdd('binaryop', 'R', $self, $other);

} # R


######################################################################
#
######################################################################
sub MarkUright {
    my $formula = shift;
    my %visited = ();
    markUrightRecur($formula,\%visited);

} # MarkUright


######################################################################
#
######################################################################
sub markUrightRecur {
    my ($root,$visited) = @_;
    return if defined($$visited{$root});
    $$visited{$root} = 1;
    markUrightRecur($$root{left},$visited) if defined($$root{left});
    markUrightRecur($$root{right},$visited) if defined($$root{right});
    if ($root->Type eq 'binaryop' && $root->Value eq 'U') {
	my $right = $$root{right};
	$$right{mark} = 1 unless defined($$right{mark});
    }

} # markUrightRecur


######################################################################
# Perform simple rewriting of a formula.
# Abbreviations should have been already expanded.
######################################################################
sub Simplify {
    my $self = shift;
    my $left = Simplify($self->Left) if defined($$self{left});
    my $right = Simplify($self->Right) if defined($$self{right});
    my $type = $self->Type;
    my $value = $self->Value;
    if ($type eq 'binaryop') {
	if ($value eq '*') {
	    if ($left->IsSimplyImplied($right)) {
		return $right;
	    } elsif ($right->IsSimplyImplied($left)) {
		return $left;
	    } elsif ($left->Not->PushNegations->IsSimplyImplied($right)) {
		return LTL->new('FALSE');
	    } elsif ($right->Not->PushNegations->IsSimplyImplied($left)) {
		return LTL->new('FALSE');
	    } elsif ($left->Type eq 'binaryop' && $left->Value eq 'R' &&
		     $right->Type eq 'binaryop' && $right->Value eq 'R' &&
		     $left->Left == $right->Left) {
		my $and = findOrAdd('binaryop', '*',
				    $left->Right, $right->Right);
		return findOrAdd('binaryop', 'R', $left->Left, $and);
	    } elsif ($left->Type eq 'binaryop' && $left->Value eq 'U' &&
		     $right->Type eq 'binaryop' && $right->Value eq 'U' &&
		     $left->Right == $right->Right) {
		my $and = findOrAdd('binaryop', '*',
				    $left->Left, $right->Left);
		return findOrAdd('binaryop', 'U', $and, $left->Right);
	    } elsif ($left->Type eq 'temporalop' && $left->Value eq 'X' &&
		     $right->Type eq 'temporalop' && $right->Value eq 'X') {
		my $and = findOrAdd('binaryop', '*',
				    $left->Left, $right->Left);
		return findOrAdd('temporalop', 'X', $and, undef);
	    } elsif ($left->Type  eq 'binaryop' && $left->Value  eq 'R' &&
		     $right->Type eq 'binaryop' && $right->Value eq 'U' &&
		     $left->Left == $right->Right) {
		my $X = findOrAdd('temporalop', 'X', $left->Right, undef);
		my $and = ($right->Left->Type eq 'atom' &&
			   $right->Left->Value eq 'TRUE') ?
		  $X : findOrAdd('binaryop', '*', $X, $right->Left);
		my $U = findOrAdd('binaryop', 'U', $and, $left->Left);
		return findOrAdd('binaryop', '*', $U, $left->Right);
	    } elsif ($right->Type eq 'binaryop' && $right->Value eq 'R' &&
		     $left->Type  eq 'binaryop' && $left->Value  eq 'U' &&
		     $right->Left == $left->Right) {
		my $X = findOrAdd('temporalop', 'X', $right->Right, undef);
		my $and = ($left->Left->Type eq 'atom' &&
			   $left->Left->Value eq 'TRUE') ?
			     $X : findOrAdd('binaryop', '*', $X, $left->Left);
		my $U = findOrAdd('binaryop', 'U', $and, $right->Left);
		return findOrAdd('binaryop', '*', $U, $right->Right);
	    } elsif ($left->Type eq 'binaryop' && $left->Value eq 'R' &&
		     $left->Left->IsSimplyImplied($right)) {
		return findOrAdd('binaryop', '*', $left->Right, $right);
	    } elsif ($right->Type eq 'binaryop' && $right->Value eq 'R' &&
		     $right->Left->IsSimplyImplied($left)) {
		return findOrAdd('binaryop', '*', $right->Right, $left);
	    } elsif ($left->Type eq 'binaryop' && $left->Value eq 'U' &&
		     $left->Left->Not->PushNegations->IsSimplyImplied($right)) {
		return findOrAdd('binaryop', '*', $left->Right, $right);
	    } elsif ($right->Type eq 'binaryop' && $right->Value eq 'U' &&
		     $right->Left->Not->PushNegations->IsSimplyImplied($left)) {
		return findOrAdd('binaryop', '*', $right->Right, $left);
	    } elsif ($left->IsFG && $right->IsFG) {
		my $and = findOrAdd('binaryop', '*',
				   $left->Right->Right, $right->Right->Right);
		my $G = findOrAdd('binaryop', 'R', LTL->new('FALSE'), $and);
		return findOrAdd('binaryop', 'U', LTL->new('TRUE'), $G);
	    } else {
		return findOrAdd('binaryop', '*', $left, $right);
	    }
	} elsif ($value eq '+') {
	    if ($left->IsSimplyImplied($right)) {
		return $left;
	    } elsif ($right->IsSimplyImplied($left)) {
		return $right;
	    } elsif ($left->IsSimplyImplied($right->Not->PushNegations)) {
		return LTL->new('TRUE');
	    } elsif ($right->IsSimplyImplied($left->Not->PushNegations)) {
		return LTL->new('TRUE');
	    } elsif ($left->Type  eq 'binaryop' && $left->Value eq 'U' &&
		     $right->Type eq 'binaryop' && $right->Value eq 'U' &&
		     $left->Left == $right->Left) {
		my $or = findOrAdd('binaryop', '+',
				   $left->Right, $right->Right);
		return findOrAdd('binaryop', 'U', $left->Left, $or);
	    } elsif ($left->Type  eq 'binaryop' && $left->Value eq 'R' &&
		     $right->Type eq 'binaryop' && $right->Value eq 'R' &&
		     $left->Right == $right->Right) {
		my $or = findOrAdd('binaryop', '+',
				   $left->Left, $right->Left);
		return findOrAdd('binaryop', 'R', $or, $left->Right);
	    } elsif ($left->Type  eq 'temporalop' && $left->Value eq 'X' &&
		     $right->Type eq 'temporalop' && $right->Value eq 'X') {
		my $or = findOrAdd('binaryop', '+',
				   $left->Left, $right->Left);
		return findOrAdd('temporalop', 'X', $or, undef);
	    } elsif ($left->Type  eq 'binaryop' && $left->Value  eq 'U' &&
		     $right->Type eq 'binaryop' && $right->Value eq 'R' &&
		     $left->Left == $right->Right) {
		my $X = findOrAdd('temporalop', 'X', $left->Right, undef);
		my $or = ($right->Left->Type eq 'atom' &&
			  $right->Left->Value eq 'FALSE') ?
			    $X : findOrAdd('binaryop', '+', $X, $right->Left);
		my $R = findOrAdd('binaryop', 'R', $or, $left->Left);
		return findOrAdd('binaryop', '+', $R, $left->Right);
	    } elsif ($right->Type eq 'binaryop' && $right->Value eq 'U' &&
		     $left->Type  eq 'binaryop' && $left->Value  eq 'R' &&
		     $right->Left == $left->Right) {
		my $X = findOrAdd('temporalop', 'X', $right->Right, undef);
		my $or = ($left->Left->Type eq 'atom' &&
			  $left->Left->Value eq 'FALSE') ?
			    $X : findOrAdd('binaryop', '+', $X, $left->Left);
		my $R = findOrAdd('binaryop', 'R', $or, $right->Left);
		return findOrAdd('binaryop', '+', $R, $right->Right);
	    } elsif ($left->Type eq 'binaryop' && $left->Value eq 'U' &&
		     $right->IsSimplyImplied($left->Left)) {
		return findOrAdd('binaryop', '+', $left->Right, $right);
	    } elsif ($right->Type eq 'binaryop' && $right->Value eq 'U' &&
		     $left->IsSimplyImplied($right->Left)) {
		return findOrAdd('binaryop', '+', $right->Right, $left);
	    } elsif ($left->Type eq 'binaryop' && $left->Value eq 'R' &&
		     $right->IsSimplyImplied($left->Left->Not->PushNegations)) {
		return findOrAdd('binaryop', '+', $left->Right, $right);
	    } elsif ($right->Type eq 'binaryop' && $right->Value eq 'R' &&
		     $left->IsSimplyImplied($right->Left->Not->PushNegations)) {
		return findOrAdd('binaryop', '+', $right->Right, $left);
	    } elsif ($left->IsGF && $right->IsGF) {
		my $or = findOrAdd('binaryop', '+',
				   $left->Right->Right, $right->Right->Right);
		my $F = findOrAdd('binaryop', 'U', LTL->new('TRUE'), $or);
		return findOrAdd('binaryop', 'R', LTL->new('FALSE'), $F);
	    } else {
		return findOrAdd('binaryop', '+', $left, $right);
	    }
	} elsif ($value eq 'U') {
	    if ($right->IsSimplyImplied($left)) {
		return $right;
	    } elsif ($right->Type eq 'atom' && $right->Value eq 'FALSE') {
		return $right;
	    } elsif ($left->Type eq 'temporalop' && $left->Value eq 'X' &&
		    $right->Type eq 'temporalop' && $right->Value eq 'X') {
		my $U = findOrAdd('binaryop', 'U', $left->Left, $right->Left);
		return findOrAdd('temporalop', 'X', $U, undef);
	    } elsif ($left->Type eq 'atom' && $left->Value eq 'TRUE' &&
		    $right->Type eq 'temporalop' && $right->Value eq 'X') {
		my $U = findOrAdd('binaryop', 'U', $left, $right->Left);
		return findOrAdd('temporalop', 'X', $U, undef);
	    } elsif ($right->Type eq 'binaryop' && $right->Value eq 'U' &&
		    $right->Left->IsSimplyImplied($left)) {
		return $right;
	    } elsif ($right->IsFGorGF) {
		return $right;
	    } elsif ($left->Type eq 'atom' && $left->Value eq 'TRUE' &&
		     $right->Type eq 'binaryop' && $right->Value eq '*' &&
		     $right->Right->IsFGorGF) {
		my $F = findOrAdd('binaryop', 'U', LTL->new('TRUE'),
				  $right->Left);
		return findOrAdd('binaryop', '*', $F, $right->Right);
	    } elsif ($left->Type eq 'atom' && $left->Value eq 'TRUE' &&
		     $right->Type eq 'binaryop' && $right->Value eq '*' &&
		     $right->Left->IsFGorGF) {
		my $F = findOrAdd('binaryop', 'U', LTL->new('TRUE'),
				  $right->Right);
		return findOrAdd('binaryop', '*', $right->Left, $F);
	    } elsif ($left->IsSimplyImplied($right->Not->PushNegations)) {
		return findOrAdd('binaryop', 'U', LTL->new('TRUE'), $right);
	    } elsif ($left->Type eq 'binaryop' && $left->Type eq '+' &&
		    $right->IsSimplyImplied($left->Left)) {
		return findOrAdd('binaryop', 'U', $left->Right, $right);
	    } elsif ($left->Type eq 'binaryop' && $left->Type eq '+' &&
		    $right->IsSimplyImplied($left->Right)) {
		return findOrAdd('binaryop', 'U', $left->Left, $right);
	    } else {
		return findOrAdd('binaryop', 'U', $left, $right);
	    }
	} elsif ($value eq 'R') {
	    if ($left->IsSimplyImplied($right)) {
		return $right;
	    } elsif ($right->Type eq 'atom' && $right->Value eq 'TRUE') {
		return $right;
	    } elsif ($left->Type eq 'temporalop' && $left->Value eq 'X' &&
		    $right->Type eq 'temporalop' && $right->Value eq 'X') {
		my $r = findOrAdd('binaryop', 'R', $left->Left, $right->Left);
		return findOrAdd('temporalop', 'X', $r, undef);
	    } elsif ($left->Type eq 'atom' && $left->Value eq 'FALSE' &&
		    $right->Type eq 'temporalop' && $right->Value eq 'X') {
		my $r = findOrAdd('binaryop', 'R', $left, $right->Left);
		return findOrAdd('temporalop', 'X', $r, undef);
	    } elsif ($right->Type eq 'binaryop' && $right->Value eq 'R' &&
		     $left->IsSimplyImplied($right->Left)) {
		return $right;
	    } elsif ($right->IsFGorGF) {
		return $right;
	    } elsif ($left->Type eq 'atom' && $left->Value eq 'FALSE' &&
		     $right->Type eq 'binaryop' && $right->Value eq '+' &&
		     $right->Right->IsFGorGF) {
		my $R = findOrAdd('binaryop', 'R', LTL->new('FALSE'),
				  $right->Left);
		return findOrAdd('binaryop', '+', $R, $right->Right);
	    } elsif ($left->Type eq 'atom' && $left->Value eq 'FALSE' &&
		     $right->Type eq 'binaryop' && $right->Value eq '+' &&
		     $right->Left->IsFGorGF) {
		my $R = findOrAdd('binaryop', 'R', LTL->new('FALSE'),
				  $right->Right);
		return findOrAdd('binaryop', '+', $right->Left, $R);
	    } elsif ($left->Not->PushNegations->IsSimplyImplied($right)) {
		return findOrAdd('binaryop', 'R', LTL->new('FALSE'), $right);
	    } elsif ($left->Type eq 'binaryop' && $left->Type eq '*' &&
		    $left->Left->IsSimplyImplied($right)) {
		return findOrAdd('binaryop', 'R', $left->Right, $right);
	    } elsif ($left->Type eq 'binaryop' && $left->Type eq '*' &&
		    $left->Right->IsSimplyImplied($right)) {
		return findOrAdd('binaryop', 'R', $left->Left, $right);
	    } else {
		return findOrAdd('binaryop', 'R', $left, $right);
	    }
	} else {
	    return findOrAdd($type, $value, $left, $right);
	}
    } elsif ($type eq 'temporalop') {
	die "unexpected temporal operator\n" unless $value eq 'X';
	if ($left->Type eq 'atom' && ($left->Value eq 'TRUE' ||
				      $left->Value eq 'FALSE')) {
	    return $left;
	} elsif ($left->Type eq 'binaryop' &&
		 ($left->Value eq '+' || $left->Value eq '*') &&
		 $left->Right->IsFGorGF) {
	    my $X = findOrAdd('temporalop', 'X', $left->Left, undef);
	    return findOrAdd('binaryop', $left->Value, $X, $left->Right);
	} elsif ($left->Type eq 'binaryop' &&
		 ($left->Value eq '+' || $left->Value eq '*') &&
		 $left->Left->IsFGorGF) {
	    my $X = findOrAdd('temporalop', 'X', $left->Right, undef);
	    return findOrAdd('binaryop', $left->Value, $left->Left, $X);
	} elsif ($left->IsFGorGF) {
	    return $left;
	} else {
	    return findOrAdd('temporalop', 'X', $left, undef);
	}
    } else {
	return findOrAdd($type, $value, $left, $right);
    }

} # Simplify


######################################################################
# Return 1 if the formula is an FG.
######################################################################
sub IsFG {
    my $self = shift;
    return $self->Type eq 'binaryop' &&
      $self->Value eq 'U' &&
	$self->Left->Type eq 'atom' && $self->Left->Value eq 'TRUE' &&
	  $self->Right->Type eq 'binaryop' && $self->Right->Value eq 'R' &&
	    $self->Right->Left->Type eq 'atom' &&
	      $self->Right->Left->Value eq 'FALSE';

} # IsFG


######################################################################
# Return 1 if the formula is a GF.
######################################################################
sub IsGF {
    my $self = shift;
    return $self->Type eq 'binaryop' &&
      $self->Value eq 'R' &&
	$self->Left->Type eq 'atom' && $self->Left->Value eq 'FALSE' &&
	  $self->Right->Type eq 'binaryop' && $self->Right->Value eq 'U' &&
	    $self->Right->Left->Type eq 'atom' &&
	      $self->Right->Left->Value eq 'TRUE';

} # IsGF


######################################################################
# Return 1 if the formula is an FG or a GF.
######################################################################
sub IsFGorGF {
    my $self = shift;
    return $self->Type eq 'binaryop' &&
      ($self->Value eq 'R' &&
       $self->Left->Type eq 'atom' && $self->Left->Value eq 'FALSE' &&
       $self->Right->Type eq 'binaryop' && $self->Right->Value eq 'U' &&
       $self->Right->Left->Type eq 'atom' &&
       $self->Right->Left->Value eq 'TRUE' ||
       $self->Value eq 'U' &&
       $self->Left->Type eq 'atom' && $self->Left->Value eq 'TRUE' &&
       $self->Right->Type eq 'binaryop' && $self->Right->Value eq 'R' &&
       $self->Right->Left->Type eq 'atom' &&
       $self->Right->Left->Value eq 'FALSE');

} # IsFGorGF


######################################################################
# Detects easy cases of implication between formulae.
######################################################################
sub IsSimplyImplied {
    my ($self,$other) = @_;
    return 1 if $self == $other;
    my $type = $self->Type;
    my $value = $self->Value;
    return 1 if $type eq 'atom' && $value eq 'TRUE';
    my $otype = $other->Type;
    my $ovalue = $other->Value;
    return 1 if $otype eq 'atom' && $ovalue eq 'FALSE';
    if ($type eq 'binaryop') {
	if ($value eq '*') {
	    return 1 if $self->Left->IsSimplyImplied($other) &&
	      $self->Right->IsSimplyImplied($other);
	} elsif ($value eq '+') {
	    return 1 if $self->Left->IsSimplyImplied($other) ||
	      $self->Right->IsSimplyImplied($other);
	} elsif ($value eq 'U') {
	    return 1 if $self->Right->IsSimplyImplied($other);
	    if ($otype eq 'binaryop' && $ovalue eq 'U') {
		return 1 if $self->Left->IsSimplyImplied($other->Left) &&
		  $self->Right->IsSimplyImplied($other->Right);
	    }
	} elsif ($value eq 'R' || $value eq 'V') {
	    return 1 if $self->Left->IsSimplyImplied($other) &&
	      $self->Right->IsSimplyImplied($other);
	    if ($otype eq 'binaryop' && ($ovalue eq 'R' || $ovalue eq 'V')) {
		return 1 if $self->Left->IsSimplyImplied($other->Left) &&
		  $self->Right->IsSimplyImplied($other->Right);
	    }
	}
    }
    if ($otype eq 'binaryop') {
	if ($ovalue eq '*') {
	    return 1 if $self->IsSimplyImplied($other->Left) ||
	      $self->IsSimplyImplied($other->Right);
	} elsif ($ovalue eq '+') {
	    return 1 if $self->IsSimplyImplied($other->Left) &&
	      $self->IsSimplyImplied($other->Right);
	} elsif ($ovalue eq 'U') {
	    return 1 if $self->IsSimplyImplied($other->Left) &&
	      $self->IsSimplyImplied($other->Right);
	} elsif ($ovalue eq 'R' || $ovalue eq 'V') {
	    return 1 if $self->IsSimplyImplied($other->Right);
	}
    }
    return "";

} # IsSimplyImplied


######################################################################
# Generates a random normalized LTL formula.
# Parameters:
#   n: number of atomic propositions
#   l: length of the formula
#   p: probability of having U or R as operator of the top node
######################################################################
sub Random {
    my ($class,$n,$l,$p) = @_;

    if ($l == 1) {
	my $phase = int(rand() + 0.5);
	my $index = int(rand $n+1);
	my $atom;
	if ($index == $n) {
	    $atom = $phase ? 'TRUE' : 'FALSE';
	} else {
	    $atom = 'p' . $index . "=$phase";
	}
	return findOrAdd('atom', $atom, undef, undef);
    } elsif ($l == 2) {
	return findOrAdd('temporalop', 'X', LTL->Random($n,1,$p), undef);
    } else {
	my $wheel = rand();
	if ($wheel < (2+$p)/3) { # binary operator
	    my $ll = int(rand $l-2) + 1;
	    my $left = LTL->Random($n,$ll,$p);
	    my $right = LTL->Random($n,$l-$ll-1,$p);
	    my $value;
	    if ($wheel < $p/2) {
		$value = 'U';
	    } elsif ($wheel < $p) {
		$value = 'R';
	    } elsif ($wheel < (1+2*$p)/3) {
		$value = '+';
	    } else {
		$value = '*';
	    }
	    return findOrAdd('binaryop', $value, $left, $right);
	} else {
	    return findOrAdd('temporalop', 'X',
			     LTL->Random($n,$l-1,$p), undef);
	}
    }

} # Random
