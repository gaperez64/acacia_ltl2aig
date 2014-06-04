# $Id: Utils.pm,v 1.6 2006/06/23 08:43:45 bjobst Exp $

######################################################################
# Functions for debugging
#
# Lily - LInear Logic sYnthesize
# Author: Barbara Jobstmann <bjobst@ist.tugraz.at>
#
######################################################################
package Utils;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK $nameIndex $DEBUG);
@ISA       = qw(Exporter);
@EXPORT    = qw();
@EXPORT_OK = qw();
$VERSION   = 1.00;
$DEBUG     = -3;

sub dot2ps {
    # If you want to translate the dot-file into ps-file  automatically,
    # uncomment the follwing lines.
#     my $file = shift;
#     print "dot2ps $file...\n";
#     $_="$file"; s/dot/ps/;
#     system ("/usr/bin/dot -Tps ".$file." > ".$_." &");
#     print "dot2ps $file done\n";
}
# parameters are $n then $d
sub calcBitNum {
    my $r = shift; 
    my $q = 0;
    while ($r > 2) { 
	$r = $r / 2;
	$q = $q + 1;
    }
    return $q;
}

1;
