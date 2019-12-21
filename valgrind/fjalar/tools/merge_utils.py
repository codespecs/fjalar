#! /usr/bin/env python3
r"""This file contains auxiliary functions for the Dyncomp
comparability tracking scripts. It defines a graph
class (MergeGraph) that represents the set
of all merges performed by Dyncomp.
"""

import pickle


class MergeEdge:
    def __init__(self, src, dest, sourceInfo, function):
        """src and dest are integer tags.
        sourceInfor indicates file and line the merge occured at.
        function indicates whether this is a value merge or a variable merge"""
        self.src = src
        self.dest = dest
        self.sourceInfo = sourceInfo
        self.function = function

    def __repr__(self):
        return "[MergeEdge] %d -> %d (Function: %s, sourceInfo: %s)" % (
            self.src, self.dest, self.function, self.sourceInfo)

    def __cmp__(self, other):
        if self is None or other is None:
            return self is not other

        if (self.src == other.src) and (self.dest == other.dest) and \
                (self.function == other.function):
            return 0
        return 1

    def __hash__(self):
        return int(hash(self.src) + hash(self.dest) + hash(self.function))


class MergeGraph:
    ## Should this comment refer to MergeEdge?
    """MergeGraph is made up of MergeNodes that contain information
    on the location of the merge including the file name and line number."""
    def __init__(self):
        self.nodes = {}

    def insertNode(self, node):
        """Insert a node."""
        self.nodes[node] = []

    def insertEdge(self, edge):
        """Insert an edge."""
        if edge.src == edge.dest:
            return

        reverseEdge = MergeEdge(edge.dest, edge.src, edge.sourceInfo, edge.function)

        if edge.src not in self.nodes:
            self.nodes[edge.src] = set()
        if edge.dest not in self.nodes:
            self.nodes[edge.dest] = set()

        self.nodes[edge.src].add(edge)
        self.nodes[edge.dest].add(reverseEdge)


class VarRecord:
    def __init__(self):
        self.tags = []
        self.is_global = False

    def __repr__(self):
        return "[VarRecord] Functions: " + "\n\Tag_list: " + str(self.tags)


class ObservationPoint:
    def __init__(self, tag, function, is_entry, invocation):
        self.tag = tag
        self.function = function
        if is_entry:
            self.info = "ENTER"
        else:
            self.info = "EXIT"
        self.invocation = invocation

    def __repr__(self):
        return "(%d, <%s %s, %d>)" % (self.tag, self.function, self.info, self.invocation)
