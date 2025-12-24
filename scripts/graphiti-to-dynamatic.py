import pydot
import networkx as nx
import re
from collections import defaultdict
import sys
import subprocess
import graphiti_conv as gc

def find_bbID(node, graph):
    PROPERTY_KEY = 'bbID'
    start_node = node

    for node in nx.dfs_preorder_nodes(graph, source=start_node):

        node_attributes = graph.nodes[node]
        attr = node_attributes.get(PROPERTY_KEY)

        if attr is not None: return attr

def find_all_bbID(nx_graph):
    for node_id, data in nx_graph.nodes(data=True):
        attr = data.get('bbID')
        if attr is None:
            data['bbID'] = find_bbID(node_id, nx_graph)

def find_tagger_or_untagger(node, graph):
    start_node = node
    prev_node = node

    # If we have a tagger, we just set tagged to false and move on.
    node_attr = graph.nodes[node]
    node_type = node_attr.get('type')
    if node_type == "\"TaggerUntagger\"":
        node_attr['tagged'] = False
        return

    # For any other node, we check if we are in the tagger or outside of it.
    for node in nx.dfs_preorder_nodes(graph, source=start_node):
        node_attr = graph.nodes[node]
        # If we hit the tagger, we have to check how we hit it.  If it is to in1 then we are inside the tagger,
        # otherwise we are outside.
        if node_attr["type"] == "\"TaggerUntagger\"":
            return graph[prev_node][node][0]["to"] == "\"in1\""

        prev_node = node

    # If we never hit the tagger, then we are outside.
    return False

def add_tagger_info(nx_graph):
    for node_id, data in nx_graph.nodes(data=True):
        attr = data.get('tagger_id')
        if attr is None:
            data['tagger_id'] = -1
        is_tagged = find_tagger_or_untagger(node_id, nx_graph)
        data['tagged'] = "true" if is_tagged else "false"
        data['taggers_num'] = 1 if is_tagged else 0

def translate_tagger(nx_graph, tag_num):
    # Find the tagger node:
    t = gc.find_node_of_type(nx_graph, "TaggerUntagger")
    if t is None: return
    tagger_node, tagger_data = t

    tagger_bitwidth = gc.first_bitwidth(tagger_data["in"])
    tagger_bbID = tagger_data["bbID"]

    edge_in1 = gc.get_input(nx_graph, tagger_node, "in1")
    edge_in2 = gc.get_input(nx_graph, tagger_node, "in2")
    edge_out1 = gc.get_output(nx_graph, tagger_node, "out1")
    edge_out2 = gc.get_output(nx_graph, tagger_node, "out2")

    nx_graph.add_node("new_aligner_branch_0", **{
        "type": '"Aligner_Branch"',
        "bbID": tagger_bbID,
        "in": f"in1:{tagger_bitwidth} in2?:32",
        "out": " ".join([f"out{x+1}:{tagger_bitwidth}" for x in range(tag_num)]),
        "delay": 0.672,
        "tagged": "false",
        "taggers_num": 0,
        "tagger_id": 0,
    })
    nx_graph.add_node("new_aligner_mux_0", **{
        "type": '"Aligner_Mux"',
        "bbID": tagger_bbID,
        "in": f"in1?:32 " + " ".join([f"in{x+2}:{tagger_bitwidth}" for x in range(tag_num)]),
        "out": f"out1:{tagger_bitwidth}",
        "delay": 3.637,
        "tagged": "false",
        "taggers_num": 0,
        "tagger_id": 0,
    })
    nx_graph.add_node("new_un_tagger_0", **{
        "type": '"Un_Tagger"',
        "bbID": tagger_bbID,
        "in": f"in1:{tagger_bitwidth}",
        "out": f"out1:{tagger_bitwidth} out2:{tagger_bitwidth}",
        "tagged": "false",
        "taggers_num": 0,
        "tagger_id": 0,
    })
    nx_graph.add_node("new_free_tags_fifo_0", **{
        "type": '"Free_Tags_Fifo"',
        "bbID": tagger_bbID,
        "in": "in1:32",
        "out": "out1:32",
        "tagged": "false",
        "taggers_num": 0,
        "tagger_id": -1,
    })
    nx_graph.add_node("new_tagger_0", **{
        "type": '"Tagger"',
        "bbID": tagger_bbID,
        "in": f"in1:{tagger_bitwidth} in2:{tagger_bitwidth}",
        "out": f"out1:{tagger_bitwidth}",
        "delay": 0.672,
        "tagged": "false",
        "taggers_num": 0,
        "tagger_id": -1,
    })
    nx_graph.add_node("new_fork_1", **{
        "type": '"Fork"',
        "bbID": tagger_bbID,
        "in": f"in1:{tagger_bitwidth}",
        "out": f"out1:{tagger_bitwidth} out2:{tagger_bitwidth}",
        "tagged": "true",
        "taggers_num": 0,
        "tagger_id": -1,
    })
    nx_graph.add_node("new_fork_2", **{
        "type": '"Fork"',
        "bbID": tagger_bbID,
        "in": f"in1:{tagger_bitwidth}",
        "out": f"out1:{tagger_bitwidth} out2:{tagger_bitwidth}",
        "tagged": "true",
        "taggers_num": 0,
        "tagger_id": -1,
    })

    nx_graph.add_edge("new_fork_1", "new_aligner_branch_0", **{"from": '"out1"', "to": '"in1"'})
    nx_graph.add_edge("new_fork_1", "new_aligner_branch_0", **{"from": '"out2"', "to": '"in2"'})
    nx_graph.add_edge("new_aligner_mux_0", "new_un_tagger_0", **{"from": '"out1"', "to": '"in1"'})
    nx_graph.add_edge("new_fork_2", "new_aligner_mux_0", **{"from": '"out2"', "to": '"in1"'})
    nx_graph.add_edge("new_un_tagger_0", "new_free_tags_fifo_0", **{"from": '"out1"', "to": '"in1"'})
    nx_graph.add_edge("new_un_tagger_0", edge_out2[0], **{"from": '"out2"', "to": edge_out2[1]})
    nx_graph.add_edge("new_free_tags_fifo_0", "new_tagger_0", **{"from": '"out1"', "to": '"in1"'})
    nx_graph.add_edge(edge_in2[0], "new_tagger_0", **{"from": edge_in2[1], "to": '"in2"' })
    nx_graph.add_edge("new_tagger_0", "new_fork_2", **{"from": '"out1"', "to": '"in1"' })
    nx_graph.add_edge("new_fork_2", edge_out1[0], **{"from": '"out1"', "to": edge_out1[1] })
    nx_graph.add_edge(edge_in1[0], "new_fork_1", **{"from": edge_in1[1], "to": '"in1"' })

    for x in range(tag_num):
        nx_graph.add_edge("new_aligner_branch_0", "new_aligner_mux_0", **{"from": f'"out{x+1}"', "to": f'"in{x+2}"'})

    nx_graph.remove_node(tagger_node)

def concat0_to_sink(nx_graph):
    for node, data in list(nx_graph.nodes(data=True)):
        if data["type"] == "\"Concat\"":
            size_0 = gc.get_size_0(data, "in")
            if size_0 is not None:
                nx_graph.add_node(node + "_sink", **{
                    "type": '"Sink"',
                    "in": "in1:0",
                    "bbID": data["bbID"],
                    "tagged": data["tagged"],
                    "taggers_num": data["taggers_num"],
                    "tagger_id": data["tagger_id"],
                })
                in_edges = nx_graph.in_edges(node, data=True)
                out_edges = nx_graph.out_edges(node, data=True)

                edge_to_sink = [(x[0], x[2]["from"]) for x in in_edges if x[2]["to"] == size_0[0]][0]
                edge_in = [(x[0], x[2]["from"]) for x in in_edges if x[2]["to"] == size_0[1]][0]
                edge_out = [(x[1], x[2]["to"]) for x in out_edges if x[2]["from"] == "\"out1\""][0]

                nx_graph.add_edge(edge_in[0], edge_out[0], **{"from": edge_in[1], "to": edge_out[1]})
                nx_graph.add_edge(edge_to_sink[0], node+"_sink", **{"from": edge_to_sink[1], "to": '"in1"'})
                nx_graph.remove_node(node)

def split0_to_fork(nx_graph):
    for node, data in list(nx_graph.nodes(data=True)):
        if data["type"] == "\"Split\"":
            size_0 = gc.get_size_0(data, "out")
            if size_0 is not None:
                nx_graph.add_node(node + "_fork", **{
                    "type": '"Fork"',
                    "in": f"in1:{size_0[2]}",
                    "out": f"out1:{size_0[2]} out2:{size_0[2]}",
                    "bbID": data["bbID"],
                    "tagged": data["tagged"],
                    "taggers_num": data["taggers_num"],
                    "tagger_id": data["tagger_id"],
                })
                in_edges = nx_graph.in_edges(node, data=True)
                out_edges = nx_graph.out_edges(node, data=True)

                edge_in1 = [(x[0], x[2]["from"]) for x in in_edges if x[2]["to"] == '"in1"'][0]
                edge_out1 = [(x[1], x[2]["to"]) for x in out_edges if x[2]["from"] == "\"out1\""][0]
                edge_out2 = [(x[1], x[2]["to"]) for x in out_edges if x[2]["from"] == "\"out2\""][0]

                nx_graph.add_edge(edge_in1[0], node+"_fork", **{"from": edge_in1[1], "to": '"in1"'})
                nx_graph.add_edge(node+"_fork", edge_out1[0], **{"from": '"out1"', "to": edge_out1[1]})
                nx_graph.add_edge(node+"_fork", edge_out2[0], **{"from": '"out2"', "to": edge_out2[1]})
                nx_graph.remove_node(node)

def remove_MC_and_sink_tags(nx_graph):
    exit_node = None
    for node, data in nx_graph.nodes(data=True):
        if data["type"] == '"Exit"':
            exit_node = node
            break
    else:
        print("Exit node not found")
        return

    count = 0
    for node, data in nx_graph.nodes(data=True):
        if data["type"] == '"MC"':
            data.pop("tagged", None)
            data["bbID"] = 0
            data.pop("taggers_num", None)
            data.pop("tagger_id", None)
            exit_port = data["out"].strip('"').strip().split()[-1].split(":")[0]
            edge = nx_graph[node].get(exit_node, [None])[0]
            if edge is not None: nx_graph.remove_edge(node, exit_node)
            nx_graph.add_edge(node, exit_node, **{"from": f'"{exit_port}"', "to": f'"in{count+1}"'})
            count = count + 1
        if data["type"] == '"Sink"':
            data.pop("tagged", None)
            data["bbID"] = 0
            data.pop("taggers_num", None)
            data.pop("tagger_id", None)

def process_dot(tag_num, input_path, output_path):
    nx_graph = gc.parse_dot(input_path)
    find_all_bbID(nx_graph)
    add_tagger_info(nx_graph)
    translate_tagger(nx_graph, tag_num)
    concat0_to_sink(nx_graph)
    split0_to_fork(nx_graph)
    remove_MC_and_sink_tags(nx_graph)
    gc.write_dot(output_path, nx_graph)

if __name__ == "__main__":
    process_dot(int(sys.argv[1]), sys.argv[2], sys.argv[3])
