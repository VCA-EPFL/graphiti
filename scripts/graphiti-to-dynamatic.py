import pydot
import networkx as nx
import re
from collections import defaultdict
import sys
import subprocess

unquoted_fields = {
    "stcount", "bbcount", "ldcount", "bbID", "delay", "tagged", "taggers_num", "tagger_id"
}

def is_valid_node_name(name):
    name = name.strip('"')
    if "\\n" in name:
        return False
    if all(c in "\\nrt" for c in name):
        return False
    return True

def is_split_mc_name(name):
    name = name.strip('"')
    return re.match(r'^MC_[^_]+_[a-z]$', name)

def get_base_mc_name(name):
    name = name.strip('"')
    match = re.match(r'^(MC_[^_]+)_([a-z])$', name)
    return match.group(1) if match else name

def recombine_mc_nodes(graph):
    connection_remap = {}
    for parent in [graph] + graph.get_subgraphs():
        nodes = parent.get_nodes()
        split_mc_groups = defaultdict(list)
        preserved_nodes = []

        for node in nodes:
            name = node.get_name()
            if is_split_mc_name(name):
                base_name = get_base_mc_name(name)
                split_mc_groups[base_name].append(node)
            else:
                preserved_nodes.append(node)

        merged_nodes = []
        for base_name, split_nodes in split_mc_groups.items():
            all_inputs = []
            all_outputs = []
            base_attrs = {}
            remap_ports = {}

            for node in split_nodes:
                attrs = node.get_attributes()
                in_field = attrs.get("in") or attrs.get('"in"')
                out_field = attrs.get("out") or attrs.get('"out"')

                node_name = node.get_name().strip('"')

                if in_field:
                    ports = in_field.strip('"').split()
                    for p in ports:
                        all_inputs.append(p)
                        port_name = p.split(":")[0]
                        remap_ports[(node_name, port_name)] = (base_name, f"in{len(all_inputs)}")

                if out_field:
                    ports = out_field.strip('"').split()
                    for p in ports:
                        all_outputs.append(p)
                        port_name = p.split(":")[0]
                        remap_ports[(node_name, port_name)] = (base_name, f"out{len(all_outputs)}")

                if not base_attrs:
                    base_attrs = {
                        k: v for k, v in attrs.items()
                        if k.strip('"') not in {"in", "out"}
                    }

            in_parts = []
            out_parts = []
            for idx, port in enumerate(all_inputs):
                port_suffix = port.split(":")[1]
                in_parts.append(f"in{idx+1}:{port_suffix}")
            for idx, port in enumerate(all_outputs):
                port_suffix = port.split(":")[1]
                out_parts.append(f"out{idx+1}:{port_suffix}")

            merged_node = pydot.Node(f'"{base_name}"')
            merged_node.set("type", "MC")
            merged_node.set("in", f'"{" ".join(in_parts)}"')
            merged_node.set("out", f'"{" ".join(out_parts)}"')

            ld_total = 0
            for node in split_nodes:
                attrs = node.get_attributes()
                ld_val = attrs.get("ldcount") or attrs.get('"ldcount"')
                try:
                    ld_total += int(ld_val.strip('"')) if ld_val else 0
                except ValueError:
                    pass
            merged_node.set("ldcount", str(ld_total))

            for k, v in base_attrs.items():
                k_clean = k.strip('"')
                if k_clean in unquoted_fields:
                    merged_node.set(k, v.strip('"'))
                else:
                    merged_node.set(k, '"' + v.strip('"') + '"')

            for node in split_nodes:
                parent.del_node(node.get_name())
            parent.add_node(merged_node)

            for (old_node, old_port), (new_node, new_port) in remap_ports.items():
                connection_remap[(old_node, old_port)] = (new_node, new_port)

    return connection_remap

def rebuild_graph_ordered(original_graph, connection_remap):
    new_graph = pydot.Dot(graph_type=original_graph.get_type())

    for k, v in original_graph.get_attributes().items():
        new_graph.set(k, v)

    for subgraph in original_graph.get_subgraphs():
        clean_subgraph = pydot.Subgraph(graph_name=subgraph.get_name())
        for attr_key, attr_val in subgraph.get_attributes().items():
            clean_subgraph.set(attr_key, attr_val)
        for node in subgraph.get_nodes():
            if is_valid_node_name(node.get_name()):
                clean_subgraph.add_node(node)
        new_graph.add_subgraph(clean_subgraph)

    for node in original_graph.get_nodes():
        if is_valid_node_name(node.get_name()):
            new_graph.add_node(node)

    for edge in original_graph.get_edges():
        src = edge.get_source().strip('"')
        dst = edge.get_destination().strip('"')
        attrs = edge.get_attributes()
        from_attr = attrs.get("from") or attrs.get('"from"')
        to_attr = attrs.get("to") or attrs.get('"to"')

        if from_attr:
            from_port = from_attr.strip('"')
            key = (src, from_port)
            if key in connection_remap:
                src, from_port = connection_remap[key]
                attrs["from"] = f'"{from_port}"'

        if to_attr:
            to_port = to_attr.strip('"')
            key = (dst, to_port)
            if key in connection_remap:
                dst, to_port = connection_remap[key]
                attrs["to"] = f'"{to_port}"'

        new_edge = pydot.Edge(f'"{src}"', f'"{dst}"', **attrs)
        new_graph.add_edge(new_edge)

    return new_graph

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

def first_bitwidth(s):
    return s.split()[0].split(':')[1]

def translate_tagger(nx_graph, tag_num):
    # Find the tagger node:
    tagger_node = None
    tagger_data = None
    for node, data in nx_graph.nodes(data=True):
        if data["type"] == "\"TaggerUntagger\"":
            tagger_node = node
            tagger_data = data
            break
    else: return

    tagger_bitwidth = first_bitwidth(tagger_data["in"])
    tagger_bbID = tagger_data["bbID"]

    in_edges = nx_graph.in_edges(tagger_node, data=True)
    out_edges = nx_graph.out_edges(tagger_node, data=True)

    edge_in1 = [(x[0], x[2]["from"]) for x in in_edges if x[2]["to"] == "\"in1\""][0]
    edge_in2 = [(x[0], x[2]["from"]) for x in in_edges if x[2]["to"] == "\"in2\""][0]
    edge_out1 = [(x[1], x[2]["to"]) for x in out_edges if x[2]["from"] == "\"out1\""][0]
    edge_out2 = [(x[1], x[2]["to"]) for x in out_edges if x[2]["from"] == "\"out2\""][0]

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

def get_sizes(data, inout):
    [x.split(":")[1] for x in data[inout].split()]

def get_size_0(data, inout):
    if data[inout].split()[0].split(":")[1] == "0":
        return (f'"{inout}1"', f'"{inout}2"', data[inout].split()[1].split(":")[1])
    elif data[inout].split()[1].split(":")[1] == "0":
        return (f'"{inout}2"', f'"{inout}1"', data[inout].split()[0].split(":")[1])
    else:
        return None

def concat0_to_sink(nx_graph):
    for node, data in list(nx_graph.nodes(data=True)):
        if data["type"] == "\"Concat\"":
            size_0 = get_size_0(data, "in")
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
            size_0 = get_size_0(data, "out")
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

def remove_MC_tags(nx_graph):
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

def process_dot(tag_num, input_path, output_path):
    graphs = pydot.graph_from_dot_file(input_path)
    if not graphs:
        raise ValueError("Could not parse DOT file.")
    graph = graphs[0]

    connection_remap = recombine_mc_nodes(graph)
    final_graph = rebuild_graph_ordered(graph, connection_remap)
    nx_graph = nx.MultiDiGraph(nx.drawing.nx_pydot.from_pydot(final_graph))
    find_all_bbID(nx_graph)
    add_tagger_info(nx_graph)
    translate_tagger(nx_graph, tag_num)
    concat0_to_sink(nx_graph)
    split0_to_fork(nx_graph)
    remove_MC_tags(nx_graph)
    nx.relabel_nodes(nx_graph, lambda x: f'"{x}"' if x[0] != '"' else x, copy=False)
    final_graph = nx.drawing.nx_pydot.to_pydot(nx_graph)
    final_graph.set_strict(False)
    # These are left over from using a MultiDiGraph
    for edge in final_graph.get_edges():
        if 'key' in edge.obj_dict.get('attributes', {}):
            del edge.obj_dict['attributes']['key']
    final_graph.write_raw(output_path)
    result = subprocess.run(['sed', '-i', 's/tagger_id="-1"/tagger_id=-1/g', output_path])

if __name__ == "__main__":
    process_dot(int(sys.argv[1]), sys.argv[2], sys.argv[3])
