#! /bin/sh

# $Id: procLTL.sh,v 1.2 2005/09/26 11:44:23 bjobst Exp $

# Wrapper to run ltl2aut and then dot on the resulting graphs.
# Running the script like this:
#
# procLTL.sh foo -f 'G(p=1)'
#
# will generate:
#    foo-parse.{dot,ps}    parse graph of the formula G(p=1)
#    foo-buechi.{dot,ps}   Buechi automaton for the formula
#    foo-scc.{dot,ps}      SCC quotient graph of the automaton
#
# the prefix for the filenames ("foo" in the example) must be the first
# argument to procLTL.sh
#
# For the other options look at ltl2aut.pl.  Do not put spaces in the
# LTL formula if you use this wrapper script.
#
# Author: Fabio Somenzi <Fabio@Colorado.EDU>

./ltl2aut.pl -p $* || exit 1
dot -Tps -o $1-parse.ps $1-parse.dot
dot -Tps -o $1-buechi.ps $1-buechi.dot
dot -Tps -o $1-scc.ps $1-scc.dot

exit 0
