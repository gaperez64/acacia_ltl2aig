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

import pydot


class BoolNet(object):
    AND = 2  # to avoid any STUPID 0 == False mistakes
    OR = 3

    # we'll be working with sextuples in the table of nodes
    # (var, op, left, right, lNeg, rNeg)
    T = [(None, False, None, None, None, None),
         (None, True, None, None, None, None)]
    # lookup hash table
    H = {}

    @staticmethod
    def reset():
        BoolNet.T[2:] = []
        BoolNet.H = {}

    @staticmethod
    def left(u):
        return BoolNet.T[u][2]

    @staticmethod
    def right(u):
        return BoolNet.T[u][3]

    @staticmethod
    def var(u):
        return BoolNet.T[u][0]

    @staticmethod
    def op(u):
        return BoolNet.T[u][1]

    @staticmethod
    def lNeg(u):
        return BoolNet.T[u][4]

    @staticmethod
    def rNeg(u):
        return BoolNet.T[u][5]

    # four cases to handle here:
    # 1. making a tautology or contradiction
    # 2. the operation is actually an identity
    # 3. the node exists
    # 4. really making something new
    # * plus the stupid case of operating 0 and 1
    @staticmethod
    def mk(var, op, left, right, lNeg, rNeg):
        #print "making " + str((var, op, left, right, lNeg, rNeg))
        # get rid of negations on T or F
        if left in [0, 1] and lNeg:
            left = int(not left)
            lNeg = False
        if right in [0, 1] and rNeg:
            right = int(not right)
            rNeg = False
        # stupid simple case = two terminals
        if left in [0, 1] and right in [0, 1]:
            return left or right if op == BoolNet.OR else left and right
        # tautologies
        elif op == BoolNet.OR and ((right == 1 or left == 1) or
                                   (left == right and lNeg != rNeg)):
            return 1
        # contradictions
        elif op == BoolNet.AND and ((right == 0 or left == 0) or
                                    (left == right and lNeg != rNeg)):
            return 0
        # identities (only possible if the operand is not negated)
        elif (not lNeg and not rNeg and
              ((op == BoolNet.AND and (right == 1 or left == 1)) or
               (op == BoolNet.OR and (right == 0 or left == 0)))):
            return right if left in [0, 1] else left
        # cached?
        elif (var, op, left, right, lNeg, rNeg) in BoolNet.H:
            return BoolNet.H[(var, op, left, right, lNeg, rNeg)]
        # new node
        else:
            u = len(BoolNet.T)
            BoolNet.T.append((var, op, left, right, lNeg, rNeg))
            BoolNet.H[(var, op, left, right, lNeg, rNeg)] = u
            return u

    # return a list of all the indices on which this given one depends
    # it includes itself
    @staticmethod
    def _depends(u):
        l = []
        if BoolNet.left(u) is not None:
            l.extend([x for x in BoolNet._depends(BoolNet.left(u))
                      if x not in l])
        if BoolNet.right(u) is not None:
            l.extend([x for x in BoolNet._depends(BoolNet.right(u))
                      if x not in l])
        l.append(u)
        return l

    # push the negations to the leaves
    @staticmethod
    def neg_to_leaves(u, neg):
        used = set([])
        cache = {}

        def _push(u, neg):
            if (u, neg) in cache:
                return cache[(u, neg)]
            elif BoolNet.left(u) is None:  # ignore terminals
                used.add((BoolNet.var(u), neg))
                return u
            else:
                flipLeft = BoolNet.lNeg(u)
                flipLeft = not flipLeft if neg else flipLeft
                flipRight = BoolNet.rNeg(u)
                flipRight = not flipRight if neg else flipRight
                flipOp = BoolNet.op(u)
                flipOp = int(not flipOp) if neg else flipOp
                # tricky part: we have to inspect children to allow negated
                # edges in case the children are terminals
                tLeft = BoolNet.left(BoolNet.left(u)) is None
                tRight = BoolNet.right(BoolNet.right(u)) is None
                pushed = BoolNet.mk(BoolNet.var(u), flipOp,
                                    _push(BoolNet.left(u), flipLeft),
                                    _push(BoolNet.right(u), flipRight),
                                    flipLeft and tLeft,
                                    flipRight and tRight)
                cache[(u, neg)] = pushed
                return pushed
        return (_push(u, neg), used)

    # monotonise the system, i.e. remove negations by introducing more
    # variables
    @staticmethod
    def rec_remove_neg(u, neg, swapDict):
        cache = {}

        def _remove(u, neg):
            #print (BoolNet.var(u), neg)
            if (u, neg) in cache:
                return cache[(u, neg)]
            elif BoolNet.left(u) is None:  # terminals
                if BoolNet.var(u) in swapDict and neg:
                    removed = BoolNet.mk(swapDict[BoolNet.var(u)], None, None,
                                         None, None, None)
                else:
                    removed = u
            else:
                # tricky part: we have to inspect children to allow negated
                # edges in case the children are terminals we want
                tLeft = not (BoolNet.left(BoolNet.left(u)) is None and
                             BoolNet.lNeg(u) and
                             BoolNet.var(BoolNet.left(u)) in swapDict)
                tRight = not (BoolNet.right(BoolNet.right(u)) is None and
                              BoolNet.rNeg(u) and
                              BoolNet.var(BoolNet.right(u)) in swapDict)
                removed = BoolNet.mk(BoolNet.var(u), BoolNet.op(u),
                                     _remove(BoolNet.left(u),
                                             BoolNet.lNeg(u)),
                                     _remove(BoolNet.right(u),
                                             BoolNet.rNeg(u)),
                                     BoolNet.lNeg(u) and tLeft,
                                     BoolNet.rNeg(u) and tRight)
            cache[(u, neg)] = removed
            return removed
        return _remove(u, neg)

    # outputs the dependency graph of the given list of indices
    @staticmethod
    def dependency_graph_png(out, latches, filename=None, variables=None):
        graph = pydot.Dot(graph_type="digraph")
        graph.edges = {}
        visited = []
        nodeCache = {}
        latchVars = [str(l) for l in latches.keys()]
        for i in range(len(BoolNet.T)):
            visited.append(None)

        # Generates the graph
        def _create_graph(u, root):
            if not visited[u] and BoolNet.left(u):  # not terminal
                visited[u] = True
                _create_graph(BoolNet.left(u), root)
                _create_graph(BoolNet.right(u), root)
            elif not visited[u]:  # and terminal
                visited[u] = True
                var = BoolNet.var(u)
                if var and var in latchVars:
                    if var not in nodeCache:
                        if BoolNet.op(u) is not None:
                            v_name = str(BoolNet.op(u))
                        else:
                            v_name = variables[var] if variables else str(var)
                        nodeCache[var] = pydot.Node(name=str(var),
                                                    label=v_name)
                        graph.add_node(nodeCache[var])
                    graph.add_edge(pydot.Edge(
                                   nodeCache[str(BoolNet.var(root))],
                                   nodeCache[var],
                                   arrowtype="normal",
                                   dir="forward"))

        nodeCache[str(out.var)] = pydot.Node(name="BAD", label="BAD")
        graph.add_node(nodeCache[str(out.var)])
        _create_graph(out.index, out.index)
        for l in latches.keys():
            visited = []
            for i in range(len(BoolNet.T)):
                visited.append(None)
            nodeCache[str(l)] = pydot.Node(name=str(l), label=str(l))
            graph.add_node(nodeCache[str(l)])
            _create_graph(latches[l].index, BoolNet(l).index)
        if not filename:
            filename = "dependencies.png"
        graph.write_png(filename)

    # reads an aig file with one output
    # return a latch for the output,
    @staticmethod
    def read_aag(aagFile):
        # open file and read header
        f = open(aagFile, 'r')
        header = f.readline().split()
        header[1:] = map(int, header[1:])
        print aagFile
        print "M I L O A = %d %d %d %d %d" % tuple(header[1:])
        # get M I L O A values from header
        I = header[2]
        IL = sum(header[2:4])
        ILO = sum(header[2:5])
        ILOA = sum(header[2:6])
        cInputs = []
        uInputs = []
        latchMappings = {}
        nodes = [BoolNet(False), BoolNet(True)]
        # create terminals
        for i in range(0, I):
            line = f.readline().split()
            aigId = line[0]
            nodes.append(BoolNet(aigId))
            nodes.append(BoolNet(aigId).lnot())
        # store latch mappings
        for i in range(I, IL):
            line = f.readline().split()
            latchMappings[int(line[0])] = int(line[1])
            aigId = line[0]
            nodes.append(BoolNet(aigId))
            nodes.append(BoolNet(aigId).lnot())
        # store output id
        for i in range(IL, ILO):
            outId = int(f.readline())
        # compute network from AND-gates
        for i in range(ILO, ILOA):
            line = map(int, f.readline().split())
            gate = nodes[line[1]].land(nodes[line[2]], line[0])
            nodes.append(gate)
            nodes.append(gate.lnot())
        # mark controllable inputs
        for i in range(0, I):
            line = f.readline()
            if "controllable" in line:
                cInputs.append(i)
            else:
                uInputs.append(i)
        # make latchMappings map to the actual node
        for k in latchMappings.keys():
            latchMappings[k] = nodes[latchMappings[k]]
        # dump dependency png
        #BoolNet.dependency_graph_png(nodes[outId], latchMappings,
        #                             filename=aagFile + "dep.png")
        # return everything
        f.close()
        return (nodes[outId], latchMappings, cInputs, uInputs, len(nodes))

    @staticmethod
    def count_nonterminals():
        n = 0
        for i in range(len(BoolNet.T)):
            if BoolNet.op(i) in [BoolNet.AND, BoolNet.OR]:
                n += 1
        return n

    @staticmethod
    def iterate_nonterminals():
        for i in range(len(BoolNet.T)):
            if BoolNet.op(i) in [BoolNet.AND, BoolNet.OR]:
                yield BoolNet(index=i)

    ######################### INSTANCE METHODS ###########################

    # opaque container for the boolean network
    def __init__(self, var=None, index=None):
        if index is not None:  # this index might be zero
            u = index
        elif not isinstance(var, bool):
            u = BoolNet.mk(var, None, None, None, None, None)
        else:
            u = 1 if var else 0

        self.index = u
        self.neg = False

    def get_var(self):
        return BoolNet.var(self.index)

    def get_left(self):
        b = BoolNet.left(self.index)
        if b is None:
            return None
        b = BoolNet(index=b)
        b.neg = BoolNet.lNeg(self.index)
        return b

    def get_right(self):
        b = BoolNet.right(self.index)
        if b is None:
            return None
        b = BoolNet(index=b)
        b.neg = BoolNet.rNeg(self.index)
        return b

    def get_op(self):
        return BoolNet.op(self.index)

    def lnot(self):
        """ We want to avoid having gates being negated, only literals should
        be negated """
        o = BoolNet.op(self.index)
        if o == BoolNet.AND:
            u = BoolNet.mk(None, BoolNet.OR, BoolNet.left(self.index),
                           not BoolNet.lNeg(self.index),
                           BoolNet.right(self.index),
                           not BoolNet.rNeg(self.index))
            return BoolNet(index=u)
        elif o == BoolNet.OR:
            u = BoolNet.mk(None, BoolNet.AND, BoolNet.left(self.index),
                           not BoolNet.lNeg(self.index),
                           BoolNet.right(self.index),
                           not BoolNet.rNeg(self.index))
            return BoolNet(index=u)
        else:
            nu = BoolNet(index=self.index)
            nu.neg = not self.neg
            return nu

    def land(self, other, var=None):
        u = BoolNet.mk(var, BoolNet.AND, self.index, other.index,
                       self.neg, other.neg)
        return BoolNet(index=u)

    def lor(self, other, var=None):
        u = BoolNet.mk(var, BoolNet.OR, self.index, other.index,
                       self.neg, other.neg)
        return BoolNet(index=u)

    def __invert__(self):
        return self.lnot()

    def __and__(self, other):
        return self.land(other)

    def __or__(self, other):
        return self.lor(other)

    def push_and_deps(self):
        (u, terminalDeps) = BoolNet.neg_to_leaves(self.index, self.neg)
        return (BoolNet(index=u), terminalDeps)

    def remove_neg(self, swapDict):
        return BoolNet(index=BoolNet.rec_remove_neg(self.index,
                                                    self.neg, swapDict))

    def depends(self, not_interesting=[]):
        l = BoolNet._depends(self.index)
        # not interesting gates
        not_int_idx = set([0, 1])
        not_int_idx |= set([b.index for b in not_interesting])
        l = [i for i in l if i not in not_int_idx]
        return [BoolNet(index=u) for u in l]

    def is_or(self):
        return self.get_op() == BoolNet.OR

    def to_dot(self, variables=None):
        graph = pydot.Dot(graph_type="digraph", label="Negated = " +
                          str(self.neg))
        graph.edges = {}
        visited = []
        for i in range(len(BoolNet.T)):
            visited.append(None)

        # Generates the graph
        def _create_graph(u):
            #print "creating graph for "
            #print BoolNet.T[u]
            if not visited[u] and BoolNet.left(u):  # not terminal
                var = BoolNet.var(u)
                opStr = "OR" if BoolNet.op(u) == BoolNet.OR else "AND"
                v_name = opStr + " (" + str(var) + ")" if var else opStr
                visited[u] = pydot.Node(name=str(u), label=v_name)
                graph.add_node(visited[u])
                _create_graph(BoolNet.left(u))
                _create_graph(BoolNet.right(u))
                if BoolNet.lNeg(u):
                    graph.add_edge(pydot.Edge(visited[u],
                                   visited[BoolNet.left(u)],
                                   style="dashed", arrowtype="normal",
                                   dir="forward"))
                else:
                    graph.add_edge(pydot.Edge(visited[u],
                                   visited[BoolNet.left(u)],
                                   arrowtype="normal",
                                   dir="forward"))
                if BoolNet.rNeg(u):
                    graph.add_edge(pydot.Edge(visited[u],
                                   visited[BoolNet.right(u)],
                                   style="dashed", arrowtype="normal",
                                   dir="forward"))
                else:
                    graph.add_edge(pydot.Edge(visited[u],
                                   visited[BoolNet.right(u)],
                                   arrowtype="normal",
                                   dir="forward"))
            elif not visited[u]:  # and terminal
                var = BoolNet.var(u)
                if BoolNet.op(u) is not None:
                    v_name = str(BoolNet.op(u))
                else:
                    v_name = variables[var] if variables else str(var)
                visited[u] = pydot.Node(name=str(u), label=v_name, shape="box")
                graph.add_node(visited[u])

        _create_graph(self.index)
        return graph

    def to_png(self, filename=None, variables=None):
        if not filename:
            filename = "{0}.png".format(str(self.var))

        graph = self.to_dot(variables)
        graph.write_png(filename)
