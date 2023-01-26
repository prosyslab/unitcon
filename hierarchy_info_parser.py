from tree_sitter import Language, Parser
import os
import sys
import json

Language.build_library('build/languages.so', ['./tree-sitter-java'])

J_LANGUAGE = Language('build/languages.so', 'java')
parser = Parser()
parser.set_language(J_LANGUAGE)

extends_class_query = \
    J_LANGUAGE.query("""
(class_declaration
  name: (identifier) @class-name
  (superclass) @class-list)
""")

implements_interface_query = \
    J_LANGUAGE.query("""
(class_declaration
  name: (identifier) @class-name
  (super_interfaces) @interface-list)
""")

extends_interface_query = \
    J_LANGUAGE.query("""
(interface_declaration
  (identifier) @interface-name
  (extends_interfaces) @interface-list)
""")

extends_class_list = []
implements_interface_list = []
extends_interface_list = []


def get_extends_class(node, src):
    match_list = extends_class_query.captures(node)
    class_name = ''
    super_class_list = []
    for i in match_list:
        text = \
            (src[i[0].start_point[0]])[i[0].start_point[1]:i[0].end_point[1]]
        if i[1] == 'class-name':
            class_name = text
        elif i[1] == 'class-list':
            text = text.replace('extends', '', 1)
            super_class_list = [super_class.strip() for super_class in
                                text.split(',')]
            extends_class_list.append({'child': class_name,
                    'super': super_class_list})


def get_implements_interface(node, src):
    match_list = implements_interface_query.captures(node)
    class_name = ''
    super_interface_list = []
    for i in match_list:
        text = \
            (src[i[0].start_point[0]])[i[0].start_point[1]:i[0].end_point[1]]
        if i[1] == 'class-name':
            class_name = text
        elif i[1] == 'interface-list':
            text = text.replace('implements', '', 1)
            super_interface_list = [super_interface.strip()
                                    for super_interface in
                                    text.split(',')]
            implements_interface_list.append({'child': class_name,
                    'super': super_interface_list})


def get_extends_interface(node, src):
    match_list = extends_interface_query.captures(node)
    interface_name = ''
    super_interface_list = []
    for i in match_list:
        text = \
            (src[i[0].start_point[0]])[i[0].start_point[1]:i[0].end_point[1]]
        if i[1] == 'interface-name':
            interface_name = text
        elif i[1] == 'interface-list':
            text = text.replace('extends', '', 1)
            super_interface_list = [super_interface.strip()
                                    for super_interface in
                                    text.split(',')]
            extends_interface_list.append({'child': interface_name,
                    'super': super_interface_list})


def one_file_hierarchy_info(src):
    f = open(src, 'r')
    src_lines = f.readlines()

    def read_callable(byte_offset, point):
        (row, column) = point
        if row >= len(src_lines) or column >= len(src_lines[row]):
            return None
        return (src_lines[row])[column:].encode('utf8')

    tree = parser.parse(read_callable)
    get_extends_class(tree.root_node, src_lines)
    get_implements_interface(tree.root_node, src_lines)
    get_extends_interface(tree.root_node, src_lines)


def all_file_hierarchy_info(dirname):
    filenames = os.listdir(dirname)
    for filename in filenames:
        full_filename = os.path.join(dirname, filename)
        if os.path.isdir(full_filename):
            all_file_hierarchy_info(full_filename)
        else:
            ext = os.path.splitext(full_filename)[-1]
            if ext == '.java':
                one_file_hierarchy_info(full_filename)


hierarchy_info = []
dir_path = sys.argv[1]
all_file_hierarchy_info(dir_path)
hierarchy_info.append({'extends_class': extends_class_list,
                      'implements_interface': implements_interface_list,
                      'extends_interface': extends_interface_list})

hierarchy_info_json = json.dumps(hierarchy_info)

with open(dir_path + '/hierarchy_info.json', 'w', encoding='utf-8') as \
    json_file:
    json.dump(hierarchy_info, json_file, indent=2)
