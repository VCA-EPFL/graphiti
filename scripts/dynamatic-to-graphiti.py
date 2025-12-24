import pydot
import networkx as nx
import sys
import subprocess
import re
import graphiti_conv as gc
import argparse
import logging

log = logging.getLogger(__name__)

# def set_one_fork(nx_graph, mux_id):

def rearrange_forks(nx_graph, mux_id):
    mux_data = nx_graph.nodes[mux_id]

    fork_of_mux, _, fork_of_mux_data = gc.get_input_and_check(nx_graph, mux_id, "in1", "Fork")
    init_merge, _, init_merge_data = gc.get_input_and_check(nx_graph, fork_of_mux, "in1", "Init")
    branch, _, branch_data = gc.get_input_and_check(nx_graph, init_merge, "in1", "Branch")
    fork_of_branch, _, fork_of_branch_data = gc.get_input_and_check(nx_graph, branch, "in2", "Fork")

    fork_of_mux_num = len(gc.get_data(fork_of_mux_data, "out").split())
    fork_of_branch_num = len(gc.get_data(fork_of_branch_data, "out").split())

    if fork_of_mux_num != fork_of_branch_num + 1:
        raise Exception(f'fork sizes mismatch: {fork_of_mux}({fork_of_mux_num}) and {fork_of_branch}({fork_of_branch_num})')

def add_init_node(nx_graph, mux_id):
    mux_data = nx_graph.nodes[mux_id]

    fork_of_mux, _, fork_of_mux_data = gc.get_input_and_check(nx_graph, mux_id, "in1", "Fork")
    init_merge, _, init_merge_data = gc.get_input_and_check(nx_graph, fork_of_mux, "in1", "Merge")

    to_sink, to_sink_port = gc.get_input(nx_graph, init_merge, "in2")
    to_sink_data = nx_graph.nodes[to_sink]

    # Turn the Merge into an Init node
    init_merge_data["type"] = '"Init"'
    init_merge_data["in"] = '"in1:1"'

    # Sink the other input into the Init
    nx_graph.remove_edge(to_sink, init_merge)

    nx_graph.add_node(f'sink_{init_merge}', **{
        "type": '"Sink"',
        "in": "in1:1",
        "bbID": 0,
    })

    nx_graph.add_edge(to_sink, f'sink_{init_merge}', **{'from': to_sink_port, 'to': '"in1"'})

def split_mc(nx_graph):
    pass

def process_dot(input_path, output_path, mux_id):
    nx_graph = gc.parse_dot(input_path)

    # Find the correct mux, rearrange the forks and insert the Init component
    if mux_id is not None:
        add_init_node(nx_graph, mux_id)
        rearrange_forks(nx_graph, mux_id)

    # Split up MCs
    split_mc(nx_graph)

    gc.write_dot(output_path, nx_graph)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Convert a Dynamatic graph into a graph ready for Graphiti.')
    parser.add_argument('input', help='input graph from Dynamatic')
    parser.add_argument('--output', '-o', help='path for output graph')
    parser.add_argument('--mux_id', '-m', help='ID for mux node at the head of loop')
    args = parser.parse_args()
    process_dot(args.input, args.output, args.mux_id)
