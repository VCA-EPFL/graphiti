import pydot
import sys

def is_valid_node_name(name):
    name = name.strip('"')
    if "\\n" in name:
        return False
    if all(c in "\\nrt" for c in name):
        return False
    return True

def split_mc_nodes(graph):
    unquoted_fields = {
        "stcount", "bbcount", "ldcount", "bbID", "delay",
        "tagged", "taggers_num", "tagger_id"
    }

    connection_map = {}

    for parent in [graph] + graph.get_subgraphs():
        original_nodes = parent.get_nodes()
        new_nodes = []

        for node in original_nodes:
            node_name = node.get_name().strip('"')
            attrs = node.get_attributes()
            node_type = attrs.get("type") or attrs.get('"type"')
            node_type = node_type.strip('" ') if node_type else ""

            if not is_valid_node_name(node_name):
                continue

            if node_type != "MC":
                new_nodes.append(node)
                continue

            in_field = attrs.get("in") or attrs.get('"in"')
            out_field = attrs.get("out") or attrs.get('"out"')
            if not in_field or not out_field:
                new_nodes.append(node)
                continue

            raw_inputs = in_field.strip('"').split()
            raw_outputs = out_field.strip('"').split()

            l_inputs = [inp for inp in raw_inputs if 'l' in inp]
            non_l_inputs = [inp for inp in raw_inputs if 'l' not in inp]

            l_outputs = [outp for outp in raw_outputs if 'l' in outp]
            non_l_outputs = [outp for outp in raw_outputs if 'l' not in outp]

            if len(l_inputs) <= 1:
                new_nodes.append(node)
                continue

            print(f"Splitting MC node: {node_name}")

            inherited_attrs = {
                k: v.strip('"') for k, v in attrs.items()
                if k.strip('"') not in {"in", "out", "ldcount"}
            }

            for i, l_input in enumerate(l_inputs):
                new_node_name_raw = f"{node_name}_{chr(97 + i)}"
                new_node_name_quoted = f'"{new_node_name_raw}"'
                new_node = pydot.Node(new_node_name_quoted)
                new_node.set("type", "MC")

                combined_inputs = non_l_inputs + [l_input] if i == 0 else [l_input]

                new_in_parts = []
                for idx, val in enumerate(combined_inputs):
                    port = val.split(":")[1]
                    port_label = f"in{idx + 1}"
                    new_in_parts.append(f"{port_label}:{port}")
                    connection_map[(node_name, val.split(":")[0])] = (new_node_name_raw, port_label)

                combined_outputs = []
                if i == 0:
                    combined_outputs += non_l_outputs
                if i < len(l_outputs):
                    combined_outputs.append(l_outputs[i])

                new_out_parts = []
                for idx, val in enumerate(combined_outputs):
                    port = val.split(":")[1]
                    port_label = f"out{idx + 1}"
                    new_out_parts.append(f"{port_label}:{port}")
                    connection_map[(node_name, val.split(":")[0])] = (new_node_name_raw, port_label)

                new_node.set("in", f'"{" ".join(new_in_parts)}"')
                new_node.set("out", f'"{" ".join(new_out_parts)}"')

                for k, v in inherited_attrs.items():
                    k_clean = k.strip('"')
                    if k_clean in unquoted_fields:
                        new_node.set(k, v)
                    else:
                        decoded_val = bytes(v, "utf-8").decode("unicode_escape")
                        new_node.set(k, f'"{decoded_val}"')

                new_node.set("ldcount", "1")

                new_nodes.append(new_node)

            default_target = (f"{node_name}_a", None)
            for val in raw_inputs:
                port = val.split(":")[0]
                if (node_name, port) not in connection_map:
                    connection_map[(node_name, port)] = default_target
            for val in raw_outputs:
                port = val.split(":")[0]
                if (node_name, port) not in connection_map:
                    connection_map[(node_name, port)] = default_target

        for old_node in parent.get_nodes()[:]:
            parent.del_node(old_node.get_name())
        for new_node in new_nodes:
            parent.add_node(new_node)

    return connection_map


def rebuild_graph_ordered(original_graph, connection_map):
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

        src_port = attrs.get("from", "").strip('"')
        dst_port = attrs.get("to", "").strip('"')

        new_src, new_src_port = connection_map.get((src, src_port), (src, src_port))
        new_dst, new_dst_port = connection_map.get((dst, dst_port), (dst, dst_port))

        if new_src_port:
            attrs["from"] = f'"{new_src_port}"'
        if new_dst_port:
            attrs["to"] = f'"{new_dst_port}"'

        new_edge = pydot.Edge(f'"{new_src}"', f'"{new_dst}"', **attrs)
        new_graph.add_edge(new_edge)

    return new_graph


def process_dot(input_path, output_path):
    graphs = pydot.graph_from_dot_file(input_path)
    if not graphs:
        raise ValueError("Could not parse DOT file.")
    original = graphs[0]

    connection_map = split_mc_nodes(original)
    final_graph = rebuild_graph_ordered(original, connection_map)
    final_graph.write_raw(output_path)

if __name__ == "__main__":
    process_dot(sys.argv[1], sys.argv[2])
