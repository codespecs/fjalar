#! /usr/bin/env python3
r"""Program to assist in understanding the series of interactions (C/C++)
DynComp observes when performing comparability analysis.

This takes in a trace file from a DynComp run on a program and
generates a graph of all the merges performed by DynComp. It then,
using Python's built in pickle serialization, writes out the graph
for use with merge_explorer.

TODO: It would be nice to track some data flow information on tags
so a user can see where a tag is generated. Unfortunately DynComp
simply does not keep track of enough information for this.
"""

## Usage merge_tracker trace-file
import logging
from pprint import pprint
import pickle
import pprint
import re
import sys

import merge_utils

if len(sys.argv) < 3:
    sys.exit("Usage: merge_tracker input-file output-db")

tag_source = {}
merge_graph = merge_utils.MergeGraph()
var_records = {}
var_records_set = {}

if sys.argv[1] == "-":
    print("Reading from standard input.")
    f = sys.stdin
else:
    print("Opening file" + sys.argv[1])
    f = open(sys.argv[1])

output_file = open(sys.argv[2], "wb")

create_tag_regex = "\[DynComp\] Creating fresh tag (.+?) at (.+) \((.+)\)"
value_merge_regex = "\[DynComp\] Merging (.+?) with (.+?) to get (.+?) at (.+?)\)$"
obs_point_regex = "\[DynComp\] OBSERVATION POINT: (.+?) - (.+?) \((.+?) (.+?) invocation (.+?)\)"

create_tag_re = re.compile(create_tag_regex)
value_merge_re = re.compile(value_merge_regex)
obs_point_re = re.compile(obs_point_regex)


def insertLine(line, regex, isVariable):
    """Parse a line from the trace and update the interaction graph if necessary."""

    match = regex.match(line)
    if match:
        tag1 = match.group(1)
        tag2 = match.group(2)
        sourceInfo = match.group(4)
        function = None

        if isVariable:
            function = match.group(5)
        merge_graph.insertEdge(merge_utils.MergeEdge(int(tag1), int(tag2), sourceInfo, function))


# Main script begins here.

for line in f:
    # Update graph with tag creation. This just adds an unconnected
    # node and is not terribly useful without additional source
    # information
    create_match = create_tag_re.match(line)
    if create_match:
        (tag, source) = (int(create_match.group(1)), create_match.group(3))
        tag_source[tag] = source
        continue

    # Update graph with an observation point. This represents DynComp
    # updating it's knowledge of values held by a particular variable.
    obs_point_match = obs_point_re.match(line)
    if obs_point_match:
        isGlobal = False
        (var, tag, entryInfo,
         func, invocation) = (obs_point_match.group(1), obs_point_match.group(2),
                              obs_point_match.group(3), obs_point_match.group(4),
                              obs_point_match.group(5))
        is_entry = (entryInfo == "ENTRY")

        if var[0] == "/":
            isGlobal = True

        if not isGlobal:
            unique_name = var.strip() + "." + func.strip()
        else:
            unique_name = var.strip()

        tag = int(tag)
        invocation = int(invocation)
        if unique_name not in var_records:
            var_records[unique_name] = merge_utils.VarRecord()
        var_records[unique_name].tags.append(
            merge_utils.ObservationPoint(tag, func, is_entry, invocation))

    # Handle a possible interaction line.
    insertLine(line, value_merge_re, False)

print("Creating merge database.")
pickle.dump(var_records, output_file, -1)
pickle.dump(merge_graph, output_file, -1)
pickle.dump(tag_source, output_file, -1)
output_file.close()
