from tree_sitter import Language, Parser
import os
import sys
import json
import re

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

extends_class_name_query = J_LANGUAGE.query("""
(class_declaration
  name: (identifier) @class-name
  (superclass) @class-list)
""")

implements_interface_name_query = J_LANGUAGE.query("""
(class_declaration
  name: (identifier) @class-name
  (super_interfaces) @interface-list)
""")

extends_interface_name_query = J_LANGUAGE.query("""
(interface_declaration
  (identifier) @interface-name
  (extends_interfaces) @interface-list)
""")

extract_class_query = J_LANGUAGE.query("""
(package_declaration)* @package-name
(class_declaration) @class
""")

extract_interface_query = J_LANGUAGE.query("""
(package_declaration)* @package-name
(interface_declaration) @interface
""")

class_and_interface_list = []
extends_class_list = []
implements_interface_list = []
extends_interface_list = []


def get_text(node, src):
    text = ''
    if src[node[0].start_point[0]] == src[node[0].end_point[0]]:
        text = (src[node[0].start_point[0]]
                )[node[0].start_point[1]:node[0].end_point[1]]
    else:
        text = (src[node[0].start_point[0]])[node[0].start_point[1]:]
        for row in range(node[0].start_point[0] + 1, node[0].end_point[0] + 1):
            if row == src[node[0].end_point[0]]:
                text = text + src[[row][:node[0].end_point[1]]]
            else:
                text = text + src[row]
    text = re.sub("<.*>", "", re.sub("{", "", text))
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
        parent_name = get_text(parent_name[0], src)
        name = get_parent_class_name(parent, src, parent_name + '$' + name)
        return name


def get_parent_interface_name(node, src, name):
    parent = node.parent
    if parent == None or parent.type == 'program':
        return name
    else:
        if parent.type == 'interface_body':
            parent = parent.parent
        parent_name = list(
            filter(lambda x: x[1] == 'interface-name',
                   [i for i in extract_interface_name_query.captures(parent)]))
        parent_name = get_text(parent_name[0], src)
        name = get_parent_interface_name(parent, src, parent_name + '$' + name)
        return name


def get_class_name(node, src, package_name):
    match_list = extract_class_name_query.captures(node)
    class_name = ''
    class_modifier = []
    for i in match_list:
        text = get_text(i, src)
        if i[1] == 'class-modifier':
            modifier_list = list(
                filter(lambda x: x == 'static' or x == 'abstract',
                       [modifier.strip() for modifier in text.split(' ')]))
            if len(modifier_list) == 0:
                class_modifier = []
            else:
                class_modifier = modifier_list
        elif i[1] == 'class-name':
            class_name = re.sub("\$$", "",
                                get_parent_class_name(i[0], src, ''))
            class_and_interface_list.append({
                'package': package_name,
                'name': class_name,
                'type': class_modifier
            })
            class_modifier = []


def get_nested_class_name(node, src):
    package_name = ''
    for i in node.children:
        match_list = extract_class_query.captures(i)
        class_name = ''
        for j in match_list:
            text = get_text(j, src)
            if j[1] == 'package-name':
                package_name = text.replace('package', '',
                                            1).replace(';', '', 1).strip()
            elif j[1] == 'class':
                get_class_name(j[0], src, package_name)


def get_interface_name(node, src, package_name):
    match_list = extract_interface_name_query.captures(node)
    interface_name = ''
    for i in match_list:
        text = get_text(i, src)
        if i[1] == 'interface-name':
            interface_name = re.sub("\$$", "",
                                    get_parent_interface_name(i[0], src, ''))
            class_and_interface_list.append({
                'package': package_name,
                'name': interface_name,
                'type': ["interface"]
            })


def get_nested_interface_name(node, src):
    package_name = ''
    for i in node.children:
        match_list = extract_interface_query.captures(i)
        interface_name = ''
        for j in match_list:
            text = get_text(j, src)
            if j[1] == 'package-name':
                package_name = text.replace('package', '',
                                            1).replace(';', '', 1).strip()
            elif j[1] == 'interface':
                get_interface_name(j[0], src, package_name)


def get_extends_class_name(node, src):
    match_list = extends_class_name_query.captures(node)
    class_name = ''
    super_class_list = []
    for i in match_list:
        text = get_text(i, src)
        if i[1] == 'class-name':
            class_name = re.sub("\$$", "",
                                get_parent_class_name(i[0], src, ''))
        elif i[1] == 'class-list':
            text = text.replace('extends', '', 1)
            super_class_list = [
                super_class.strip() for super_class in text.split(',')
            ]
            extends_class_list.append({
                'child': class_name,
                'super': super_class_list
            })


def get_nested_extends_class_name(node, src):
    for i in node.children:
        match_list = extract_class_query.captures(i)
        class_name = ''
        for j in match_list:
            text = get_text(j, src)
            if j[1] == 'class':
                get_extends_class_name(j[0], src)


def get_implements_interface_name(node, src):
    match_list = implements_interface_name_query.captures(node)
    class_name = ''
    super_interface_list = []
    for i in match_list:
        text = get_text(i, src)
        if i[1] == 'class-name':
            class_name = re.sub("\$$", "",
                                get_parent_class_name(i[0], src, ''))
        elif i[1] == 'interface-list':
            text = text.replace('implements', '', 1)
            super_interface_list = [
                super_interface.strip() for super_interface in text.split(',')
            ]
            implements_interface_list.append({
                'child': class_name,
                'super': super_interface_list
            })


def get_nested_implements_interface_name(node, src):
    for i in node.children:
        match_list = extract_class_query.captures(i)
        class_name = ''
        for j in match_list:
            text = get_text(j, src)
            if j[1] == 'class':
                get_implements_interface_name(j[0], src)


def get_extends_interface_name(node, src):
    match_list = extends_interface_name_query.captures(node)
    match_list = []
    interface_name = ''
    super_interface_list = []
    for i in match_list:
        text = get_text(i, src)
        if i[1] == 'interface-name':
            interface_name = re.sub("\$$", "",
                                    get_parent_interface_name(i[0], src, ''))
        elif i[1] == 'interface-list':
            text = text.replace('extends', '', 1)
            super_interface_list = [
                super_interface.strip() for super_interface in text.split(',')
            ]
            extends_interface_list.append({
                'child': interface_name,
                'super': super_interface_list
            })


def get_nested_extends_interface_name(node, src):
    for i in node.children:
        match_list = extract_interface_query.captures(i)
        interface_name = ''
        for j in match_list:
            text = get_text(j, src)
            if j[1] == 'interface':
                get_extends_interface_name(j[0], src)


def one_file_hierarchy_info(src, encoding):
    f = open(src, 'r', encoding=encoding)
    src_lines = f.readlines()

    def read_callable(byte_offset, point):
        (row, column) = point
        if row >= len(src_lines) or column >= len(src_lines[row]):
            return None
        return (src_lines[row])[column:].encode('utf8')

    tree = parser.parse(read_callable)
    get_nested_class_name(tree.root_node, src_lines)
    get_nested_interface_name(tree.root_node, src_lines)
    get_nested_extends_class_name(tree.root_node, src_lines)
    get_nested_implements_interface_name(tree.root_node, src_lines)
    get_nested_extends_interface_name(tree.root_node, src_lines)


def all_file_hierarchy_info(dirname, encoding):
    filenames = os.listdir(dirname)
    for filename in filenames:
        full_filename = os.path.join(dirname, filename)
        if os.path.isdir(full_filename):
            all_file_hierarchy_info(full_filename, encoding)
        else:
            ext = os.path.splitext(full_filename)[-1]
            if ext == '.java':
                one_file_hierarchy_info(full_filename, encoding)


if len(sys.argv) != 3:
    print("Usage: directory_path encoding")
    sys.exit()

hierarchy_info = []
dir_path = sys.argv[1]
encoding = sys.argv[2]

all_file_hierarchy_info(dir_path, encoding)

hierarchy_info.append({
    'class_and_interface':
    list({name['name']: name
          for name in class_and_interface_list}.values()),
    'extends_class':
    list({name['child']: name
          for name in extends_class_list}.values()),
    'implements_interface':
    list({name['child']: name
          for name in implements_interface_list}.values()),
    'extends_interface':
    list({name['child']: name
          for name in extends_interface_list}.values())
})
hierarchy_info_json = json.dumps(hierarchy_info)

name = ''
if dir_path[-1] == '/':
    name = 'hierarchy_info.json'
else:
    name = '/hierarchy_info.json'

with open(dir_path + name, 'w', encoding='utf-8') as json_file:
    json.dump(hierarchy_info, json_file, indent=2)
