from tree_sitter import Language, Parser
import os, pathlib
import re, json
import argparse

Language.build_library('build/languages.so', ['./tree-sitter-java'])

J_LANGUAGE = Language('build/languages.so', 'java')
parser = Parser()
parser.set_language(J_LANGUAGE)

extract_class_name_query = J_LANGUAGE.query("""
(class_declaration
(modifiers)* @class-modifier
  name: (identifier) @class-name)
""")

extract_interface_name_query = J_LANGUAGE.query("""
(interface_declaration
  (identifier) @interface-name)
""")

extract_enum_query = J_LANGUAGE.query("""
(package_declaration)* @package-name
(class_declaration
  name: (identifier) @class-name)*
(enum_declaration
  name: (identifier) @enum-name)
(enum_body
(enum_constant) @enum-const)
""")

enum_list = []


def get_package_class(package_name, class_name):
    if package_name:
        class_name = package_name + '.' + class_name
    return class_name


def get_text(node, src):
    text = ''
    if src[node[0].start_point[0]] == src[node[0].end_point[0]]:
        text = (src[node[0].start_point[0]])[node[0].start_point[1]:node[0].end_point[1]]
    else:
        text = (src[node[0].start_point[0]])[node[0].start_point[1]:]
        for row in range(node[0].start_point[0] + 1, node[0].end_point[0] + 1):
            if row == src[node[0].end_point[0]]:
                text = text + src[[row][:node[0].end_point[1]]]
            else:
                text = text + src[row]
    text = re.sub("{", "", text)
    return text


def get_parent_class_name(node, src, name):
    parent = node.parent
    if parent == None or parent.type == 'program':
        return name
    else:
        if parent.type == 'class_body':
            parent = parent.parent
        parent_name = list(
            filter(lambda x: x[1] == 'class-name',
                   [i for i in extract_class_name_query.captures(parent)]))
        if not parent_name:
            parent_name = list(
                filter(lambda x: x[1] == 'interface-name',
                       [i for i in extract_interface_name_query.captures(parent)]))
        if not parent_name:
            return name
        else:
            parent_name = get_text(parent_name[0], src)
            return get_parent_class_name(parent, src, parent_name + '$' + name)


def get_enum(node, src):
    match_list = extract_enum_query.captures(node)
    package_name = ''
    enum_name = ''
    for i in match_list:
        text = get_text(i, src)
        if i[1] == 'package-name':
            package_name = text.replace('package', '', 1).replace(';', '', 1).strip()
        elif i[1] == 'enum-name':
            parent_name = get_parent_class_name(i[0].parent, src, '')
            enum_name = get_package_class(package_name, parent_name + text)
        elif i[1] == 'enum-const':
            enum_list.append({
                'enum': enum_name,
                'const': re.sub("\([^)]*\)[\),;]*", "", text, re.MULTILINE).strip()
            })


def one_file_enum_info(src, encoding):
    src_lines = []
    with open(src, 'r', encoding=encoding) as f:
        src_lines = f.readlines()

    def read_callable(byte_offset, point):
        (row, column) = point
        if row >= len(src_lines) or column >= len(src_lines[row]):
            return None
        return (src_lines[row])[column:].encode('utf8')

    tree = parser.parse(read_callable)
    get_enum(tree.root_node, src_lines)


def all_files_enum_info(project_dir, encoding):
    for dirpath, dirnames, filenames in os.walk(project_dir):
        for filename in filenames:
            if filename.endswith(".java"):
                one_file_enum_info(os.path.join(dirpath, filename), encoding)


def mk_json_file(project_dir):
    prop_dir = os.path.join(project_dir, "unitcon_properties")
    if not os.path.isdir(prop_dir):
        os.makedirs(prop_dir)
    with open(os.path.join(prop_dir, "enum_info.json"), 'w', encoding='utf-8') as json_file:
        json.dump(enum_list, json_file, indent=2)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("project",
                        type=pathlib.Path,
                        default=None,
                        help='Project directory where need to obtain enum information')
    parser.add_argument("--encoding", type=str, default="utf-8", help='Encoding type of project')
    args = parser.parse_args()
    all_files_enum_info(args.project, args.encoding)
    mk_json_file(args.project)


if __name__ == "__main__":
    main()
