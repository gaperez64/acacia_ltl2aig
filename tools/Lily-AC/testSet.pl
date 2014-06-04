#! /usr/bin/perl -w

# $Id: testSet.pl,v 1.2 2005/09/26 11:44:23 bjobst Exp $

# This script tests the set package.

# Author: Fabio Somenzi <Fabio@Colorado.EDU>

use Sopen;
use LTL;
use Set;
use strict;

my $startTime = (times)[0];

my $a = Set->new("a","b","d","c");
print "a: ", $a->ToString(), "\n";
# print "a: $a\n";		# use overloading
print "unsorted a: {", join(',', $a->List), "}\n";
print "sorted a  : {", join(',', $a->Sort), "}\n";

my $f1 = LTL->new("p=1");
my $f2 = LTL->new("X(q=0)");
my $b = Set->new($f1,$f2);
print "b: ", $b->ToString(), "\n";
# print "b: $b\n";		# use overloading
print "sorted b: {", join(',', map {$_->ToString} $b->Sort), "}\n";

my $c = Set->new(1,2,3,4.5,-3.2,10);
print "c: ", $c->ToString(), "\n";
# print "c: $c\n";		# use overloading
print "sorted c: {", join(',', $c->Sort(sub{$Set::a <=> $Set::b})), "}\n";
print "2 is ", $c->IsMember(2) ? "" : "not ", "in c; ";
print "4 is ", $c->IsMember(4) ? "" : "not ", "in c\n";

my $f3 = LTL->new("p=1 U q=0");
my $d = Set->new($f1,$f3);
print "d: ", $d->ToString(), "\n";

my $e = $b->Intersection($d);
print "b * d: ", $e->ToString(), "\n";
print "b + d: ", $b->Union($d)->ToString(), "\n";
print "size of b + d = ", $b->Union($d)->Size(), "\n";
print "b \\ d: ", $b->Difference($d)->ToString(), "\n";
print "b * d is ", ($e->IsEqual($b) ? "" : "not "), "equal to b\n";
print "b * d is ", ($e->IsIncluded($b) ? "" : "not "), "included in b\n";

my $f = $b->Clone();
print "f: ", $f->ToString(), "\n";
my $g = $f->Pop();
print "popped ", $g->ToString(), " from f\n";
print "f: ", $f->ToString(), "\n";
print "b: ", $b->ToString(), "\n";
$f->Push($g);
print "pushed ", $g->ToString(), " onto f\n";
print "f is ", ($f->IsEqual($b) ? "" : "not "), "equal to b\n";

my $endTime = (times)[0];
printf "CPU time: %.2f seconds\n", $endTime - $startTime;

exit(0);
