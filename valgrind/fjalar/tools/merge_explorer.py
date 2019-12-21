#! /usr/bin/env python3
r"""Program to assist in understanding the series of interactions (C/C++)
DynComp observers when performing comparability analysis.

This takes a database file produced by merge_tracker and prints
information on the given tag or variable
"""

import logging
import logging.handlers
import optparse
import os
import pickle
import pprint
import re
import signal
import sys
import time

import merge_utils

var_records = None
merge_graph = None
tag_source = None


class OptionParser(optparse.OptionParser):
    """Parses options"""
    def check_required(self, opt):
        """Checks that required aptions are present (?)"""
        option = self.get_option(opt)

        # Assumes the option's 'default' is set to None!
        if getattr(self.values, option.dest) is None:
            self.error("%s option not supplied" % option)


def bfs_path(src, target, ppt, graph):
    """Performs a breadth-first search between two nodes
    Will only traverse merge_edges whose ppt is None or
    equal to the ppt passed as an argument."""

    parents = {}
    parents[src] = None

    if ((src not in graph.nodes) or (target not in graph.nodes)):
        return parents

    visited = set()
    toVisit = list(graph.nodes[src])
    while toVisit:
        cur_edge = toVisit.pop(0)
        if (cur_edge.dest not in parents) and (cur_edge not in visited) and (
                cur_edge.dest in graph.nodes):
            for edge in graph.nodes[cur_edge.dest]:
                if edge in visited:
                    continue
                assert cur_edge.dest == edge.src
                if (edge.function is not None) and not edge.function == ppt:
                    logging.info("%s does not match %s" % (edge.function, ppt))
                    continue
                toVisit.append(edge)
            if cur_edge.dest not in parents and (cur_edge.dest !=
                                                 src) and (cur_edge.function == ppt):
                parents[cur_edge.dest] = cur_edge
        visited.add(cur_edge)
    return parents


def find_path(src, target, ppt, graph):
    """Attempts to find an interaction path between two
    tags. It proceeds by first attempting to find
    an interaction path without traversing edges
    with ppt's (These correspond to variable level merges)
    If it fails it will retry including merge edges
    that are equal to the passed in ppt."""

    print("Attempting to find a value interaction path")
    parents = bfs_path(src, target, None, graph)

    if target in parents:
        print("Found value interaction path")
        curNode = parents[target]
    else:
        return None
        logging.info("Attempting to find a variable interaction path")
        parents = bfs_path(src, target, ppt, graph)
        if target in parents:
            curNode = parents[target]
        else:
            return None

    path = []
    logging.debug("Constructing path")
    while curNode is not None:
        if curNode.src in parents:
            logging.debug("Appending " + str(curNode))
            path.insert(0, curNode)
            assert curNode != parents[curNode.src]
            curNode = parents[curNode.src]
        else:
            print("Failed to reconstruct path")
            return None

    print(path)
    return path


def load_db(db_file, dump_names, dump_info):
    """Loads the pickled db file created by merge_tracker."""
    global var_records, merge_graph, tag_source

    print("Loading " + db_file)

    input = open(db_file, "rb")
    var_records = pickle.load(input)

    if dump_names or dump_info:
        if dump_names:
            for name in var_records.keys():
                print(name)
        if dump_info:
            pp = pprint.PrettyPrinter(indent=4)
            pp.pprint(var_records)

        for v in var_records.keys():
            if var_records[v].is_global:
                assert len(var_records[v].functions) == len(var_records[v].entry_tags)
                sys.exit(0)
        sys.exit(0)

    merge_graph = pickle.load(input)
    tag_source = pickle.load(input)

    print("Loaded " + db_file)


def dump_vars(ppt):
    """Dumps all variable information. This includes the variable's name and all
recorded tags. Tends to produce a lot of output."""

    pp = pprint.PrettyPrinter(indent=4)
    pp.pprint(var_records)

    for v in var_records.keys():
        if var_records[v].is_global:
            assert len(var_records[v].functions) == len(var_records[v].entry_tags)


def search(src_var, target_var):
    """Attempts to find an interaction patch between src_var and target_var"""
    if (not src_var) or (not target_var):
        return

    print("Searching for [%s] - [%s]" % (src_var, target_var))

    source = None
    target = None
    source_record = None
    target_record = None
    result = []

    if target_var:
        for k in var_records.keys():
            if (source is None) and (k == src_var):
                source_name = k
                source_record = var_records[k]

            if (not target) and (k == target_var):
                target_name = k
                target_record = var_records[k]

            if source_record and target_record:
                checked_pairs = set()
                print("Interactions between %s (loaded from 0xNYI) and %s (loaded from 0xNYI):" %
                      (source_name, target_name))
                for i in range(len(source_record.tags)):
                    src_tag = source_record.tags[i].tag
                    for j in range(len(target_record.tags)):
                        target_tag = target_record.tags[j].tag
                        if (src_tag, target_tag) in checked_pairs:
                            continue
                        info_string = "Path found between %d (Function %s (%s) invocation %d) and %d (Function %s (%s) invocation %d)"
                        logging.info("Searching for path between %d and %d.." %
                                     (src_tag, target_tag))
                        if src_tag == target_tag:
                            print(
                                "\nThere is a common tag between %s @ (Function %s (%s) invocation %d) and %s @ (Function %s (%s) \
                                   invocation %d).\n" %
                                (source_name, source_record.tags[i].function,
                                 source_record.tags[i].info, source_record.tags[i].invocation,
                                 target_name, target_record.tags[i].function,
                                 target_record.tags[i].info, target_record.tags[i].invocation))
                            return
                        result = find_path(src_tag, target_tag, "", merge_graph)
                        checked_pairs.add((src_tag, target_tag))
                        if result:
                            print(
                                "\nPath found between %s - %d (Function %s (%s) invocation %d) and %s - %d (Function %s (%s) \
                                   invocation %d).\n" %
                                (source_name, src_tag, source_record.tags[i].function,
                                 source_record.tags[i].info, source_record.tags[i].invocation,
                                 target_name, target_tag, target_record.tags[j].function,
                                 target_record.tags[j].info, target_record.tags[j].invocation))
                            for edge in result:
                                print("%d -> %d - [%s]" % (edge.src, edge.dest, edge.sourceInfo))
                            return
                return
    print("No paths found")


#LOG_FILENAME = '/scratch/merge_tracker.log'
#logging.basicConfig(filename=LOG_FILENAME,level=logging.DEBUG,)
#handler = logging.handlers.RotatingFileHandler (LOG_FILENAME, maxBytes=100000000, backupCount=5)
if __name__ == "__main__":
    usage = "Usage: %prog -f db_file [options]"
    parser = OptionParser(usage=usage)
    parser.add_option("-f",
                      "--file",
                      default=None,
                      help="merge database generated by merge_tracker",
                      dest="db_file")
    parser.add_option("-S",
                      "--source",
                      default=None,
                      help="regex matching variable of interest",
                      dest="src_var")
    parser.add_option("-T",
                      "--target",
                      default=None,
                      help="regex matching variable of interest",
                      dest="target_var")
    parser.add_option("-d",
                      "--dump-var-names",
                      default=False,
                      action="store_true",
                      help="Dump variable names",
                      dest="dump_var_names")
    parser.add_option("-D",
                      "--dump-var-info",
                      default=False,
                      action="store_true",
                      help="Dump variable names. WARNING: ALOT OF TEXT",
                      dest="dump_var_info")
    (options, args) = parser.parse_args()
    parser.check_required("-f")

    load_db(options.db_file, options.dump_var_names, options.dump_var_info)

    search(options.src_var, options.target_var)
