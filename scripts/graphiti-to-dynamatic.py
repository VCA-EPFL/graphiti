import pydot
import re
from collections import defaultdict
import sys

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

def process_dot(input_path, output_path):
    graphs = pydot.graph_from_dot_file(input_path)
    if not graphs:
        raise ValueError("Could not parse DOT file.")
    graph = graphs[0]

    connection_remap = recombine_mc_nodes(graph)
    final_graph = rebuild_graph_ordered(graph, connection_remap)
    final_graph.set_strict(False)
    final_graph.write_raw(output_path)

if __name__ == "__main__":
    process_dot(sys.argv[1], sys.argv[2])
