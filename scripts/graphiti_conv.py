import pydot
import networkx as nx
import sys
import subprocess
import re

def write_dot(output_path, nx_graph):
    nx.relabel_nodes(nx_graph, lambda x: f'"{x}"' if x[0] != '"' else x, copy=False)
    final_graph = nx.drawing.nx_pydot.to_pydot(nx_graph)
    final_graph.set_strict(False)
    # These are left over from using a MultiDiGraph
    for edge in final_graph.get_edges():
        if 'key' in edge.obj_dict.get('attributes', {}):
            del edge.obj_dict['attributes']['key']
    final_graph.write_raw(output_path)
    subprocess.run(['sed', '-i', 's/tagger_id="-1"/tagger_id=-1/g', output_path])

def parse_dot(input_path):
    graphs = pydot.graph_from_dot_file(input_path)
    if not graphs:
        raise ValueError("Could not parse DOT file.")
    graph = graphs[0]

    subgraphs = graph.get_subgraphs()
    for subgraph in subgraphs:
        nodes = subgraph.get_nodes()
        for node in nodes:
            graph.add_node(node)
        edges = subgraph.get_edges()
        for edge in edges:
            graph.add_edge(edge)

    nx_graph = nx.MultiDiGraph(nx.drawing.nx_pydot.from_pydot(graph))
    return nx_graph

def get_input(nx_graph, node_id, port_id):
    in_edges = nx_graph.in_edges(node_id, data=True)
    return [(x[0], x[2]["from"]) for x in in_edges if x[2]["to"].strip('"') == port_id][0]

def get_output(nx_graph, node_id, port_id):
    out_edges = nx_graph.out_edges(node_id, data=True)
    return [(x[1], x[2]["to"]) for x in out_edges if x[2]["from"].strip('"') == port_id][0]

def get_input_and_check(nx_graph, node_id, inp, typ):
    prev_node = get_input(nx_graph, node_id, inp)
    prev_node_data = nx_graph.nodes[prev_node[0]]

    if prev_node_data["type"].strip('"') != typ:
        raise Exception(f'could not find {typ} for {node_id}/{inp}')

    return (prev_node[0], prev_node[1], prev_node_data)

def get_output_and_check(nx_graph, node_id, out, typ):
    next_node = get_output(nx_graph, node_id, out)
    next_node_data = nx_graph.nodes[next_node[0]]

    if next_node_data["type"].strip('"') != typ:
        raise Exception(f'could not find {typ} for {node_id}/{out}')

    return (next_node[0], next_node[1], next_node_data)

def find_nodes_of_type(nx_graph, node_type):
    ret = []
    for node, data in nx_graph.nodes(data=True):
        if get_data(data, "type") == node_type:
            ret += [(node, data)]
    return ret

def find_node_of_type(nx_graph, node_type):
    return find_nodes_of_type(nx_graph, node_type)[0]

def first_bitwidth(s):
    return s.split()[0].split(':')[1]

def get_sizes(data, inout):
    [x.split(":")[1] for x in data[inout].split()]

def get_size_0(data, inout):
    if data[inout].split()[0].split(":")[1] == "0":
        return (f'"{inout}1"', f'"{inout}2"', data[inout].split()[1].split(":")[1])
    elif data[inout].split()[1].split(":")[1] == "0":
        return (f'"{inout}2"', f'"{inout}1"', data[inout].split()[0].split(":")[1])
    else:
        return None

def get_data(node_data, key):
    return node_data[key].strip('"').strip()

def get_data_default(node_data, key, default):
    return node_data.get(key, default).strip('"').strip()
