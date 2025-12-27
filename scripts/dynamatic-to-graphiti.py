import pydot
import networkx as nx
import sys
import subprocess
import re
import graphiti_conv as gc
import argparse
import logging
import json

log = logging.getLogger(__name__)

def find_port_for(nx_graph, branch):
    mux, _, mux_data = gc.get_output_and_check(nx_graph, branch, "out1", "Mux")
    fork, fork_port, fork_data = gc.get_input_and_check(nx_graph, mux, "in1", "Fork")
    port_num = int(re.search(r'\d+', fork_port)[0])
    return port_num

def rearrange_forks(nx_graph, mux_id, fork_of_mux, fork_of_branch):
    mux_data = nx_graph.nodes[mux_id]
    fork_of_mux_data = nx_graph.nodes[fork_of_mux]
    fork_of_branch_data = nx_graph.nodes[fork_of_branch]

    init_merge, _, init_merge_data = gc.get_input_and_check(nx_graph, fork_of_mux, "in1", "Init")

    fork_of_mux_num = len(gc.get_data(fork_of_mux_data, "out").split())
    fork_of_branch_num = len(gc.get_data(fork_of_branch_data, "out").split())

    if fork_of_mux_num + 1 != fork_of_branch_num:
        raise Exception(f'fork sizes mismatch: {fork_of_mux}({fork_of_mux_num}) and {fork_of_branch}({fork_of_branch_num})')

    branches = [x[1] for x in nx_graph.out_edges(fork_of_branch) if gc.get_data(nx_graph.nodes[x[1]], "type") == "Branch"]
    remapping = [(x, find_port_for(nx_graph, x)) for x in branches]

    # Remove all outgoing edges from the forks
    nx_graph.remove_edges_from(list(nx_graph.out_edges(fork_of_branch)))

    nx_graph.add_edge(fork_of_branch, init_merge, **{'from': '"out1"', 'to': '"in1"'})
    for branch, idx in remapping:
        nx_graph.add_edge(fork_of_branch, branch, **{'from': f'"out{idx+1}"', 'to': '"in2"'})

def is_branch_fork(nx_graph, merge_id, nid):
    outs = nx_graph.out_edges(nid, data=True)
    return all([(x[1] == merge_id or nx_graph.nodes[x[1]]["type"].strip('"') == "Branch") for x in outs]) and nx_graph.nodes[nid]["type"].strip('"') == "Fork"

def add_init_node(nx_graph, mux_id):
    mux_data = nx_graph.nodes[mux_id]

    fork_of_mux, _, fork_of_mux_data = gc.get_input_and_check(nx_graph, mux_id, "in1", "Fork")
    init_merge, _, init_merge_data = gc.get_input_and_check(nx_graph, fork_of_mux, "in1", "Merge")

    merge_in1, mereg_in1_port = gc.get_input(nx_graph, init_merge, "in1")
    merge_in2, mereg_in2_port = gc.get_input(nx_graph, init_merge, "in2")

    if is_branch_fork(nx_graph, init_merge, merge_in1):
        to_branch, to_branch_port = gc.get_input(nx_graph, init_merge, "in1")
        to_branch_data = nx_graph.nodes[to_branch]
        to_sink, to_sink_port = gc.get_input(nx_graph, init_merge, "in2")
        to_sink_data = nx_graph.nodes[to_sink]
    elif is_branch_fork(nx_graph, init_merge, merge_in2):
        to_branch, to_branch_port = gc.get_input(nx_graph, init_merge, "in2")
        to_branch_data = nx_graph.nodes[to_branch]
        to_sink, to_sink_port = gc.get_input(nx_graph, init_merge, "in1")
        to_sink_data = nx_graph.nodes[to_sink]
    else:
        raise Exception('no fork found')

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
    nx_graph.edges[to_branch, init_merge, 0]['to'] = 'in1'

    return (fork_of_mux, to_branch)

def split_mc(nx_graph):
    for mc, mc_data in gc.find_nodes_of_type(nx_graph, "MC"):
        ldcount = int(gc.get_data_default(mc_data, "ldcount", "0"))
        stcount = int(gc.get_data_default(mc_data, "stcount", "0"))
        if ldcount > 1 and stcount == 0:
            mc_data['graphiti_metadata'] = json.dumps({
                'in': gc.get_data(mc_data, 'in'),
                'out': gc.get_data(mc_data, 'out'),
              })
            mc_data['in'] = "in1:32*l0a"
            mc_data['out'] = "out1:32*l0d out2:0*e"
            for port in range(1, ldcount):
                nid, inP = gc.get_output(nx_graph, mc, f'out{port+1}')
                _, outP = gc.get_input(nx_graph, mc, f'in{port+1}')
                nx_graph.remove_edge(mc, nid)
                nx_graph.remove_edge(nid, mc)
                nx_graph.add_node(f'{mc}_shard_{port}', **{
                    "type": '"MC"',
                    "in": "in1:32*l0a",
                    "out": "out1:32*l0d out2:0*e",
                    "memory": gc.get_data(mc_data, "memory"),
                    "bbID": 0,
                    'graphiti_metadata': json.dumps({
                        'parent_mc': mc,
                        'shard_num': port,
                      }),
                })
                nx_graph.add_edge(f'{mc}_shard_{port}', nid, **{'from': '"out1"', 'to': f'{inP}'})
                nx_graph.add_edge(nid, f'{mc}_shard_{port}', **{'from': f'{outP}', 'to': '"in1"'})

def remove_load_mc_connections_to_exit(nx_graph):
    exit_node = gc.find_node_of_type(nx_graph, "Exit")[0]
    for node, data in list(nx_graph.nodes(data=True)):
        if gc.get_data(data, "type") == 'MC' and int(gc.get_data_default(data, "stcount", "0")) == 0:
            exit_port = gc.get_data(data, "out").split()[-1].split(":")[0]
            edge = nx_graph[node].get(exit_node, [None])[0]
            if edge is not None: nx_graph.remove_edge(node, exit_node)

def process_dot(input_path, output_path, mux_ids):
    nx_graph = gc.parse_dot(input_path)

    # Find the correct mux, rearrange the forks and insert the Init component
    for mux_id in mux_ids:
        fork_mux, fork_branch = add_init_node(nx_graph, mux_id)
        rearrange_forks(nx_graph, mux_id, fork_mux, fork_branch)

    # Split up MCs
    remove_load_mc_connections_to_exit(nx_graph)
    split_mc(nx_graph)

    gc.write_dot(output_path, nx_graph)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Convert a Dynamatic graph into a graph ready for Graphiti.')
    parser.add_argument('input', help='input graph from Dynamatic')
    parser.add_argument('--output', '-o', help='path for output graph')
    parser.add_argument('--mux-ids', '-m', nargs='*', help='ID for mux node at the head of loop')
    args = parser.parse_args()
    process_dot(args.input, args.output, args.mux_ids)
