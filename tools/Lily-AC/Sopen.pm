# $Id: Sopen.pm,v 1.2 2005/09/26 11:44:23 bjobst Exp $

#####################################################################
# This module exports a function that opens a file for reading.
#
# Author: Fabio Somenzi <Fabio@Colorado.EDU>
#
#####################################################################

package Sopen;
use Exporter ();
use vars qw($VERSION @ISA @EXPORT @EXPORT_OK);
@ISA       = qw(Exporter);
@EXPORT    = qw(sopen);
@EXPORT_OK = qw();
$VERSION   = 1.00;
use strict;



###############################################################
# sopen: semi-sophisticated open
# Opens a file for reading. If the file is compressed by
# compress, compact, or gzip, it is uncompressed on the fly.
# Returns the modification date.
###############################################################
sub sopen {
    my($filename,$handle) = @_;
    my($cx1,$cx2);

    open($handle,$filename) || die "Can't open $filename: $!\n";

    # Get stats on this file, extract and format the modification date.
    # The format is: mm/dd/yy hh:mm:ss

    my($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,$atime,$mtime,
       $ctime,$blksize,$blocks) = stat ($handle);
    my(@moddate) = localtime($mtime);
    my($moddate) = $moddate[4]+1 . "/" . $moddate[3] . "/" . $moddate[5] .
      " " . $moddate[2] . ":" . $moddate[1] . ":" . $moddate[0];

    # Check for compressed file.
    # The "&& -B $handle" test works on Unix, but not on Windows95.
    if (-e $handle) { # binary file --  may be compressed/compacted/gzipped
	if (($cx1 = getc($handle)) eq "\377" && (getc($handle) eq "\037")) {
	    open ($handle, "uncompact < $filename|");
	} elsif ($cx1 eq "\037" && (($cx2 = getc($handle)) eq "\235")) {
	    open ($handle, "uncompress < $filename|");
	} elsif ($cx1 eq "\037" && ($cx2 eq "\213")) {
	    open ($handle, "gzip -d < $filename|");
	} else {
	    seek($handle,0,0);	# rewind
	}
    }
    return $moddate;

} # end of sopen
