#! /usr/bin/env python

## This file contains auxiliary functions for the Dyncomp
## comparability tracking scripts. It defines a graph
## class(merge_graph) that will be used to represent the set
## of all merges performed by Dyncomp. merge_graph is made up of
## merge_nodes which contain information on the location of the merge
## including the file name and line number.
import cPickle
import sets

class MergeEdge:
    def __init__(self, src, dest, sourceInfo, function):
        """Needs the file and line the merge occured at.
        additionally, it need to know whether or not this is
        a value merge or a variable merge"""
        self.sourceInfo = sourceInfo
        self.function = function
        self.src = src
        self.dest = dest

    def __repr__(self):
        return "[MergeEdge] %d -> %d (Function: %s, sourceInfo: %s)" % (self.src, self.dest, self.function, self.sourceInfo)

    def __cmp__(self, other):
        if self is None or other is None:
            return not (self is other)

        if (self.src == other.src) and (self.dest == other.dest) and \
                (self.function == other.function):
            return 0
        return 1

    def __hash__(self):
        return int(hash(self.src) + hash(self.dest) + hash(self.function))
        
        
class MergeGraph:
    def __init__(self):
        self.nodes = {}

    def insertNode(self, node):
        self.nodes[node] = []

    def insertEdge(self, edge):
        if edge.src == edge.dest:
            return

        reverseEdge = MergeEdge(edge.dest, edge.src, edge.sourceInfo, edge.function)
        
        if edge.src not in self.nodes:
            self.nodes[edge.src] = sets.Set()
        if edge.dest not in self.nodes:
            self.nodes[edge.dest] = sets.Set()

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


def print_set(set):
  print "Set(",
  for x in set:
    print x
  print ")"
