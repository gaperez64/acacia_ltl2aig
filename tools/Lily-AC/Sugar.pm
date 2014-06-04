# $Id: Sugar.pm,v 1.2 2006/03/22 14:04:10 bjobst Exp $

######################################################################
# Functions for translating Sugar formulae (in the linear-time
# segment) to LTL equivalents.
#
# Lily - LInear Logic sYnthesize
# Author: Barbara Jobstmann <bjobst@ist.tugraz.at>
#
######################################################################
#package Sugar;
#use Exporter ();
#use vars qw($VERSION @ISA @EXPORT @EXPORT_OK $nameIndex $DEBUG);
#@ISA       = qw(Exporter);
#@EXPORT    = qw();
#@EXPORT_OK = qw();
#$VERSION   = 1.00;
#$DEBUG     = -3;

sub readSugar {
    my ($file,$refAssert, $refAssume) = @_;
    my $moddate = sopen($file,\*FFILE);
    my $formula ="";
    my $sugar   ="";
    while (<FFILE>) {
	chop;				# discard newline
	s/\#.*//;			# discard comments
	s/\s+$//;			# discard trailing blanks
	$formula .= $_;
	if (/;/) {
	    $formula =~ s/;//;		# discard trailing semicolon
	    $formula =~ s/\s+$//;	# discard trailing blanks
	    $formula =~ s/^\s+//;       # discard preceding blanks
	    next if ($formula =~ /^\s*$/);# skip empty lines
            $sugar = translateToLTL($formula);
	    #print "Read: ".$formula."\n";
	    #print "Push: ".$sugar."\n";
	    if ($formula =~ /assume/) {#append formula to assume list
		push(@$refAssume,$sugar);
	    } else {#append formula to assert list (default)
		push(@$refAssert,$sugar)
	    }
	    $formula="";
	}
    }
    if ($formula ne "") {
       print "Warning reading Sugar formulae: Semicolon missing\n";
    }
    close(FFILE);
} # readSugar


sub translateToLTL {
    $_ = shift;
    my @elems = split(/ +|\+|$|\(|\)|\->|&+|\|+|\*|!|;/);
    my @vars;
    foreach my $var (@elems) {
	next if ($var =~ /assume/);
	next if ($var =~ /assert/);
	next if ($var =~ /next/);
	next if ($var =~ /until/);
	next if ($var =~ /always/);
	next if ($var =~ /eventually/);
	next if ($var =~ /=/);
	push(@vars,$var) unless ($var =~ /^\s*$/);
    }
    @vars = sort @vars;
    @vars = uniq(@vars);
    s/assert\s*//g;
    s/assume\s*//g;
    s/always/G/g;
    s/eventually!/F/g;
    s/until!/U/g;
    if (/until/) {
	print "Error parsing Sugar: Used until! instead of until.\n";
	die;
    }
    s/&&/\*/g;
    s/\|\|/\+/g;
    s/&/\*/g;
    s/\|/\+/g;
    $dead=0;
    while (/next_([a|e])\[([0-9]*):([0-9]*)\](\s*)(\(.+\))/) {
	$dead = $dead + 1;
	$count=0;
	$statement = "next_$1\[$2:$3\]$4";
	@chars = split(//,$5);
	@inside = ();
	foreach my $c (@chars) {
	    push(@inside,$c);
	    $count = $count + 1 if ($c eq '(');
	    $count = $count - 1 if ($c eq ')');
	    last if ($count == 0);
	}
	$inside = join('',@inside);
	$statement .= $inside;
	
	$replace = "(";
	for ($i=$2; $i <= $3; $i++) {
	    if ($i == 0) {
		$replace .= $inside if $i == 0;
	    } else {
		$replace .= "X("x ($i-1)."X".$inside.")"x ($i-1);
	    }
	    $replace .= " + " if ($i ne $3);
	}
	$replace .= ")";

	#brackets and parentheses must be escaped in the replace string
	$statement =~ s/\[/\\\[/g;
	$statement =~ s/\]/\\\]/g;
	$statement =~ s/\(/\\\(/g;
	$statement =~ s/\)/\\\)/g;
	$statement =~ s/\|/\\\|/g;
	$statement =~ s/\+/\\\+/g;
	$statement =~ s/\*/\\\*/g;
	s/$statement/$replace/g;

	if ($dead > 30) {
	    print "Infinite loop -> Break\n";
	    last;
	}
    }
    if (/next_([a|e])/) {
	print "Error parsing Sugar: next_$1 requires parentheses.\n";
	die;
    }

    s/next\s*\(/X\(/g;
    if (/next/) {
	print "Error parsing Sugar: next requires parentheses.\n";
	die;
    }
    foreach my $var (@vars) {
	#print "replace: ".$var."\n";
	s/$var/$var=1/g;
    }
    return $_;
}

sub uniq {
    my @list = @_;
    my @newlist = ();
    foreach my $elem (@list) {
	if (grep(/$elem/, @newlist) > 0) {
	    #print "Skip:".$elem."\n";
	} else {
	    push(@newlist,$elem);
	    #print "Push:".$elem."\n";
	}
    }
    return @newlist;
}

1;
