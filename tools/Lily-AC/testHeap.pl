#! /usr/bin/perl -w

# $Id: testHeap.pl,v 1.2 2005/09/26 11:44:23 bjobst Exp $

# This script tests the Heap package.

# Author: Fabio Somenzi <Fabio@Colorado.EDU>

use Heap;
use strict;

my $startTime = (times)[0];

# Basic test of a small queue.
my $q = Heap->new;
$q->Push(12, "third");
$q->Push(3, "first");
$q->Push(13, "fourth");
$q->Push(5, "second");
$q->Push(12, "another third");
print "q: ", $q->ToString(), "\n";
printf "q is %s\n", $q->Test ? "valid" : "invalid";
my $c = $q->Clone;
print "Extracting elements from q:\n";
while ($q->Size > 0) {
    my ($key, $item) = $q->Pop;
    print "key = $key; item = $item\n";
}
printf "q is %s valid \n", $q->Test ? "still" : "no longer";
printf "c is %s\n", $c->Test ? "valid" : "invalid";
print "Extracting elements from c:\n";
while ($c->Size > 0) {
    my ($key, $item) = $c->Pop;
    print "key = $key; item = $item\n";
}
printf "c is %s valid \n", $c->Test ? "still" : "no longer";
# Test of a queue initialized with a few elements.
my $r = Heap->new([[1, "a"], [4, "d"], [2, "b"]]);
print "r: ", $r->ToString(), "\n";
printf "r is %s\n", $r->Test ? "valid" : "invalid";
print "Extracting elements from r:\n";
while ($r->Size > 0) {
    my ($key, $item) = $r->Pop;
    print "key = $key; item = $item\n";
}

# Heap-sort numbers.
for (my $i = 0; $i < 20000; $i++) {
    my $n = rand;
    $q->Push($n,$n);
}
printf "q is %s\n", $q->Test ? "valid" : "invalid";
my $prev = -1;
while ($q->Size > 0) {
    my ($key, $item) = $q->Pop;
    # print "key = $key; item = $item\n";
    die "items out of order" if $item < $prev;
    $prev = $item;
}

my $endTime = (times)[0];
printf "CPU time: %.2f seconds\n", $endTime - $startTime;

exit(0);
