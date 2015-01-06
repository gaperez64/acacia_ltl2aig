"""
 Copyright (c) 2014 Guillermo A. Perez

 This library is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 This library is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 See the GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this file. If not, see <http://www.gnu.org/licenses/>.
"""
import re
import subprocess
import argparse
import math
from pygraph.classes.digraph import digraph

import acacia_plus
import utils
import boolnet

EXIT_STATUS_REALIZABLE = 10
EXIT_STATUS_UNREALIZABLE = 20
EXIT_STATUS_UNKNOWN = 30
debug = False
log = True


def DBG_MSG(s):
    if debug:
        print "[DBG] " + str(s)


def LOG_MSG(s):
    if log:
        print "[LOG] " + str(s)


# reads a file and returns a list of inputs and outputs
def read_partition(partition_file):
    f = open(partition_file, "r")
    partition = f.readlines()
    f.close()

    for l in partition:
        l = l.lstrip(" ")  # remove white spaces in front of l
        if re.match(re.compile("\.inputs.*"), l):
            inputs = re.split(re.compile("\s+"), l)[1:]
        elif re.match(re.compile("\.outputs.*"), l):
            outputs = re.split(re.compile("\s+"), l)[1:]
    # clean the input lists
    try:
        inputs_temp = []
        for x in inputs:
            if x != "" and x != "\n":
                inputs_temp.append(x.lower())
        inputs = inputs_temp
    except UnboundLocalError:
        print "Input signals not found"
        exit(0)
    # clean the output list
    try:
        outputs_temp = []
        for x in outputs:
            if x != "" and x != "\n":
                outputs_temp.append(x)
        outputs = outputs_temp
    except UnboundLocalError:
        print "Output signals not found"
        exit(0)

    return (inputs, outputs)


# reads ltl file in Wring format and returns the ltl formula
def read_formulae(filename, compositional):
    f = open(filename, "r")
    spec_names = []  # list of specifications names
    form = ""
    forms = []
    l = f.readline()
    while l != "":
        if not compositional:
            if not l.startswith("#") and not l.startswith("[spec_unit") and\
                    not l.startswith("group_order"):
                form += l
            l = f.readline()
        else:  # compositional approach
            # Find first line of ######...
            while not l.startswith("[spec_unit") and l != "":
                l = f.readline()
            if l == "":  # end of file -> only one spec
                print "Formula problem: [spec_unit name] pattern " +\
                      "not found! You probably chose a compositional " +\
                      "construction and there is only one specification."
                exit(0)
            spec_names.append(l.split(']')[0][1:])
            l = f.readline()  # first line of current spec
            # Get the spec
            cur_formula = ""
            while not l.startswith("[spec_unit") and\
                    not l.startswith("group_order") and l != "":
                if not l.startswith("#"):
                    cur_formula += l
                l = f.readline()
            forms.append(cur_formula)
            # If this is the last spec, the group_order method follows
            if l.startswith("group_order"):
                break
    if not compositional:
        spec_names.append("u0")
        forms.append(form)
    LOG_MSG(str(len(spec_names)) + " specs read")
    DBG_MSG("Read specs: " + str(spec_names))
    assert len(forms) == len(spec_names)
    return forms


def negate_ltl2ba(formula):
    return "!(" + formula + ")"


# formula conversion, from Wring to LTL2BA format
def wring_to_ltl2ba(formula, inputs, outputs):
    newformula = ""
    (assumptions, guarantees) = extract_assumptions_and_guarantees(formula)

    def convert_local(subform):
        subform = subform.replace("assume", "")
        subform = subform.replace("\t", " ")
        subform = subform.replace("\n", "")
        subform = subform.replace("G", "[] ")
        subform = subform.replace("F", "<> ")
        subform = subform.replace("+", " || ")
        subform = subform.replace("*", " && ")
        # WARNING: inputs + outputs must include all of them
        for i in (inputs + outputs):
            subform = subform.replace(i + "=0", "!" + i)
            subform = subform.replace(i + "=1", i)
        return (subform)

    newassumptions = ""
    if assumptions.__len__() > 0:
        newassumptions = convert_local(assumptions[0])
        for f in assumptions[1:]:
            newassumptions = newassumptions + " && (" + convert_local(f) + ")"
        newassumptions = "(" + newassumptions + ")"

    newguarantees = ""
    if guarantees.__len__() > 0:
        newguarantees = convert_local(guarantees[0])
        for f in guarantees[1:]:
            newguarantees = newguarantees + "&& (" + convert_local(f) + ")"
        newguarantees = "(" + newguarantees + ")"

    if newassumptions != "" and newguarantees != "":
        newformula = newassumptions + " -> " + newguarantees
    elif newassumptions != "":
        newformula = "!(" + newassumptions + ")"
    elif newguarantees != "":
        newformula = newguarantees
    else:
        print("Empty formula")
        exit(0)

    if re.match(re.compile(".*(=1|=0).*"), newformula):
        print("Partition file doesn\"t match formula!")
        exit(0)

    return newformula


# extract assumptions and guarantees from formula
def extract_assumptions_and_guarantees(formula):
    lines = formula.splitlines()
    # remove comments
    formula = ""
    for l in lines:
        if l != "":
            ls = re.split(re.compile("#"), l)
            formula = formula + ls[0] + "\n"
    subformulas = re.split(re.compile(";"), formula)

    assumptions = []
    guarantees = []
    for f in subformulas:
        if re.match(re.compile("\s*assume(.|\n)*"), f):
            assumptions.append(f)
        elif re.match(re.compile("(.|\s)*\w(.|\s)*"), f):
            guarantees.append(f.lstrip("\n"))

    return (assumptions, guarantees)


# Constructs an automaton from ltl2ba for the formula
def construct_automata(formula):
    tool_cmd = ["./tools/ltl2ba-1.1/ltl2ba", "-f"]
    try:
        out = subprocess.Popen(tool_cmd + [formula], stdout=subprocess.PIPE)
        (automata, err) = out.communicate()
    except:
        print "ltl2ba not found! Don't forget to install it"
        exit(0)

    accepting_states = []

    # automaton parsing
    s = automata.split("*/\n")
    if s.__len__() < 2:
        print("empty automaton, LTL syntax error?")
        exit(0)

    automata = s[1]

    r = re.compile(";\n\}?\n?")
    transitions = re.split(r, automata)
    nb_trans = 0

    # create a new graph
    g = digraph()
    g.__init__()

    # local function which determines if a state is initial
    def isinitial(s):
        return re.match(re.compile(".*init"), s)

    # iterate over transitions (except the last which is the empty string)
    l = transitions.__len__() - 1
    if transitions[l] == "":
        tobound = l
    else:
        tobound = l + 1

    for t in transitions[0:tobound]:
        # split transition into head (state) and body (rules)
        rstate = re.compile(":\n")
        trans = re.split(rstate, t)
        # state extraction
        s = re.split(re.compile("\Aaccept_"), trans[0])
        if len(s) == 1:
            state = s[0]
            accept = False
        elif len(s) == 2:
            state = s[1]
            accept = True
        if isinitial(state):
            state = "initial"
        if accept:
            accepting_states.append(state)
        if not g.has_node(state):
            g.add_node(state)

        # rules extraction
        if re.match(re.compile("(.|\n)*skip(.|\n)*"), trans[1]):
            tuple = (state, state)
            g.add_edge(tuple, wt=1, label="(1)")
            nb_trans += 1
        elif not re.match(re.compile("(.|\n)*false(.|\n)*"), trans[1]):
            l = re.split(re.compile("::"), trans[1])
            for y in l:
                if not re.match(re.compile("\s*if\s"), y):
                    fr = re.split(re.compile(" -> goto "), y)
                    edgelab = fr[0].strip()
                    if re.match(re.compile(".*accept.*"), fr[1]):
                        accept = True  # the state is accepting
                    else:
                        accept = False
                    gre = re.split(re.compile("accept_"), fr[1])
                    gre = re.split(re.compile("\s+f?i?"), gre[len(gre) - 1])
                    goto_state = gre[0]
                    if isinitial(goto_state):
                        goto_state = "initial"
                    if not g.has_node(goto_state):  # new goto, add it
                        g.add_node(goto_state)
                    tuple = (state, goto_state)
                    disj_size = edgelab.count("||") + 1
                    g.add_edge(tuple, wt=disj_size, label=edgelab)
                    nb_trans = nb_trans + 1

    return (g, accepting_states)


def int2binlatch(varlist, n):
    net = boolnet.BoolNet(True)
    dividend = n
    power = len(varlist) - 1
    for v in varlist:
        divisor = math.pow(2, power)
        if dividend >= divisor:
            net &= boolnet.BoolNet(v)
            dividend -= divisor
        else:
            net &= ~boolnet.BoolNet(v)
        power -= 1
    return net


def int2latchlist(varlist, n):
    l = []
    dividend = n
    power = len(varlist) - 1
    for v in varlist:
        divisor = math.pow(2, power)
        if dividend >= divisor:
            l.append(v)
            dividend -= divisor
        power -= 1
    return l


def label2inputs(inputs, outputs, label, input_map):
    all_signals = inputs + outputs
    labels = label.split("||")
    input_net = boolnet.BoolNet(False)
    for l in labels:
        (props,
         n_disj) = utils.convert_formula_to_proptab(l, all_signals)
        if props == "T":
            DBG_MSG("Trivial edge")
            input_net |= boolnet.BoolNet(True)
            continue
        props = list(props)
        temp = boolnet.BoolNet(True)
        for p in range(len(all_signals)):
            p_val = props[p]
            if p_val == "1":
                temp &= boolnet.BoolNet(input_map[all_signals[p]])
            elif p_val == "2":
                temp &= ~boolnet.BoolNet(input_map[all_signals[p]])
        input_net |= temp
    return input_net


def write_aig(inputs, outputs, latches, error, file_name):
    f = open(file_name, "w")
    all_signals = inputs + outputs
    n_signals = len(all_signals)
    n_latches = len(latches)
    # STEP 0: Compute the number of gates to be used
    m_vars = boolnet.BoolNet.count_nonterminals()
    # STEP 1: Print header
    f.write("aag " + str(m_vars + n_signals + n_latches) + " " +
            str(n_signals) + " " +
            str(n_latches) + " " +
            "1 " +
            str(m_vars) + "\n")
    # STEP 2: Print inputs (and name them)
    var_map = dict()
    for i in range(2, 2 * (n_signals + 1), 2):
        f.write(str(i) + "\n")
        var_map[boolnet.BoolNet(i).index] = i
    # STEP 3: Print latches
    # for this part we need to have numbered/named the gates
    # and assigned a var to True and False
    cur_var = 2 * (n_signals + n_latches + 1)
    var_map[0] = 0
    var_map[1] = 1
    for v in boolnet.BoolNet.iterate_nonterminals():
        var_map[v.index] = cur_var
        cur_var += 2
    # name the latches and print their latch [space] net.index line
    # TECH NOTE
    # =========
    # the boolnet data structure makes sure the following invariant holds:
    # v.neg => v is a literal, therefore v.is_or() != v.neg is equivalent to
    # v.is_or() | v.neg
    for (l, net) in sorted(latches.items()):
        var_map[boolnet.BoolNet(l).index] = l

    for (l, net) in sorted(latches.items()):
        assert ~net.is_or() | ~net.neg
        if net.is_or() != net.neg:
            f.write(str(l) + " " + str(var_map[net.index] ^ 1) + "\n")
        else:
            f.write(str(l) + " " + str(var_map[net.index]) + "\n")
    # STEP 4: Print error
    err = var_map[error.index]
    if error.is_or() != error.neg:
        err ^= 1
    f.write(str(err) + "\n")
    # STEP 5: Print gates
    # we are using deMorgan's Law to have all gates be AND-gates
    for v in boolnet.BoolNet.iterate_nonterminals():
        f.write(str(var_map[v.index]) + " ")
        # the gate might be an or, meaning everyone else will use its
        # negation
        local_neg = v.is_or()
        # we now print the left operand
        left = v.get_left()
        assert ~left.is_or() | ~left.neg
        if local_neg != (left.is_or() != left.neg):
            f.write(str(var_map[left.index] ^ 1) + " ")
        else:
            f.write(str(var_map[left.index]) + " ")
        # same treatment for the right operand
        right = v.get_right()
        assert ~right.is_or() | ~right.neg
        if local_neg != (right.is_or() != right.neg):
            f.write(str(var_map[right.index] ^ 1) + "\n")
        else:
            f.write(str(var_map[right.index]) + "\n")
    # STEP 6: Print symbol table
    cnt = 0
    for i in inputs:
        f.write("i" + str(cnt) + " " + str(i) + "\n")
        cnt += 1
    for i in outputs:
        f.write("i" + str(cnt) + " controllable_" + str(i) + "\n")
        cnt += 1
    cnt = 0
    for l in latches:
        f.write("l" + str(cnt) + " latch" + str(cnt) + "\n")
        cnt += 1
    f.write("o0 error\n")
    # STEP 7: Close the file
    f.close()


############################# MAIN ##########################
# NOTE: var_offset is applied to latches and gates but not to inputs/outputs
def translate2aig(inputs, outputs, k, states, buchi_states,
                  var_offset, edges):
    LOG_MSG("k = " + str(k))
    LOG_MSG(str(len(inputs)) + " inputs")
    DBG_MSG("inputs: " + str(inputs))
    LOG_MSG(str(len(outputs)) + " outputs")
    DBG_MSG("outputs: " + str(outputs))

    # STEP 1: check number of states
    n_nodes = len(states)
    LOG_MSG(str(n_nodes) + " states")
    DBG_MSG("states: " + str(states))

    # STEP 2: assign inputs and outputs a number
    free_var = 2
    input_map = dict()
    input_map["F"] = 0
    input_map["T"] = 1
    for i in inputs:
        input_map[i] = free_var
        free_var += 2
    # reserve outputs and negations
    for o in outputs:
        input_map[o] = free_var
        free_var += 2
    # reserve latches X counters, and negations
    # and get the initial node
    if var_offset is not None:
        assert free_var <= var_offset
        free_var = var_offset
    state_latch_map = dict()
    latch_net = dict()
    init_node = None
    for u in states:
        if u == "initial":
            init_node = u
            DBG_MSG("initial state: " + str(u))
        for i in range(k + 2):
            state_latch_map[(u, i)] = free_var
            latch_net[free_var] = boolnet.BoolNet(False)
            free_var += 2
    LOG_MSG(str(len(buchi_states)) + " buchi states")
    DBG_MSG("buchi states: " + str(buchi_states))
    LOG_MSG(str(len(edges)) + " edges")

    # STEP 3: create the boolean network rep. of automata
    # first transition is to let the 0 config go directly to the initial state
    all_off = boolnet.BoolNet(True)
    for latch in state_latch_map.values():
        all_off &= ~boolnet.BoolNet(latch)
    latch_net[state_latch_map[(init_node, 0)]] |= all_off
    # now add each individual transition,
    # incrementing counters when a state is buchi
    for ((u, v), l) in edges:
        # state u goes to state v
        DBG_MSG("edge: " + str(u) + "->" +
                str(v) + " (label: " +
                str(l) + ")")
        # which inputs enable the transition?
        input_net = label2inputs(inputs, outputs, l,
                                 input_map)
        # play with the counters
        for i in range(k + 2):
            # if buchi, add value
            if v in buchi_states:
                j = min(i + 1, k + 1)
                latch_net[state_latch_map[(v, j)]] |= (
                    boolnet.BoolNet(state_latch_map[(u, i)]) &
                    input_net)
            else:
                latch_net[state_latch_map[(v, i)]] |= (
                    boolnet.BoolNet(state_latch_map[(u, i)]) &
                    input_net)

    # STEP 4: create the error net
    error_net = boolnet.BoolNet(False)
    for u in states:
        error_net |= boolnet.BoolNet(state_latch_map[(u, k + 1)])
    # RETURN latchnet and errornet
    return (latch_net, error_net, free_var)


def main(formula_file, part_file, k, args):
    # STEP 0: read partition, ltl formula and create BA
    (inputs, outputs) = read_partition(part_file)
    wring_formulae = read_formulae(formula_file, args.compositional)
    var_offset = None
    latch_net = dict()
    error_net = boolnet.BoolNet(False)
    for wring_formula in wring_formulae:
        ltl2ba_formula = wring_to_ltl2ba(wring_formula, inputs, outputs)
        formula = negate_ltl2ba(ltl2ba_formula)
        DBG_MSG("negated formula: " + str(formula))
        (automata, buchi_states) = construct_automata(formula)
        # STEP 1: translate aig
        (ln, en,
         var_offset) = translate2aig(inputs, outputs, k, automata.nodes(),
                                     buchi_states, var_offset,
                                     [(e, automata.edge_label(e)) for e in
                                      automata.edges()])
        latch_net.update(ln)
        error_net |= en
    # STEP 2: call Acacia+ to see if this is realizable or not
    arg_list = ["--ltl", formula_file,
                "--part", part_file,
                "--player", "1",
                "--kbound", str(k - 1),
                "--verb", "0",
                "--crit", "OFF",
                "--opt", "none",
                "--check", "REAL"]
    if args.compositional:
        arg_list.extend(["--syn", "COMP",
                         "--nbw", "COMP"])
    (solved, is_real) = acacia_plus.main(arg_list)
    LOG_MSG("acacia+ replied (solved, realizability) = (" +
            str(solved) + ", " + str(is_real) + ")")
    if solved and is_real:
        file_name = formula_file[:-4] + "_" + str(k) + "_REAL.aag"
        ret = EXIT_STATUS_REALIZABLE
    elif solved and not is_real:
        file_name = formula_file[:-4] + "_" + str(k) + "_UNREAL.aag"
        ret = EXIT_STATUS_UNREALIZABLE
    else:
        file_name = formula_file[:-4] + "_" + str(k) + "_UNREAL.aag"
        ret = EXIT_STATUS_UNKNOWN
    # FINALLY: dump the AIG
    write_aig(inputs, outputs, latch_net,
              error_net, file_name)
    return ret


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="LTL to AIG Game translation")
    parser.add_argument("formula", metavar="formula", type=str,
                        help="LTL formula file (Wring format)")
    parser.add_argument("part", metavar="part", type=str,
                        help="Input partition file")
    parser.add_argument("k", metavar="k", type=int,
                        help="k for which the corresponding k-coBuchi game " +
                             "will be constructed")
    parser.add_argument("-c", dest="compositional", default=False,
                        action="store_const", const=True,
                        help="construct formulas compositionally")
    args = parser.parse_args()
    exit(main(args.formula, args.part, args.k, args))
