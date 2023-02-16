from tree_sitter import Language, Parser
import os
import sys
import json
import re

Language.build_library('build/languages.so', ['./tree-sitter-java'])

J_LANGUAGE = Language('build/languages.so', 'java')
parser = Parser()
parser.set_language(J_LANGUAGE)

extract_nested_class_query = J_LANGUAGE.query("""
(class_declaration
  (modifiers)* @class-modifier
  name: (identifier) @class-name
  body: (class_body
  (class_declaration)+ @inner-class
  ))
""")

extract_inner_class_query = J_LANGUAGE.query("""
(class_declaration
    (modifiers)* @inner-class-modifier
    (identifier) @inner-class-name)
""")

extract_pure_class_query = J_LANGUAGE.query("""
(class_declaration
  (modifiers)* @class-modifier
  name: (identifier) @class-name)
""")

extract_interface_query = J_LANGUAGE.query("""
(interface_declaration
  (identifier) @interface-name)
""")

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

class_and_interface_list = []
extends_class_list = []
implements_interface_list = []
extends_interface_list = []


def get_nested_class_name(node, src):
    pure_match_list = extract_nested_class_query.captures(node)
    match_list = []
    for node in pure_match_list:
        if node not in match_list:
            match_list.append(node)
    class_name = ''
    class_modifier = []
    inner_class_name = ''
    inner_class_modifier = []
    for i in match_list:
        text = \
            (src[i[0].start_point[0]])[i[0].start_point[1]:i[0].end_point[1]]
        text = re.sub("<.*>", "", text)
        if i[1] == 'class-modifier':
            modifier_list = list(
                filter(lambda x: x == 'static' or x == 'abstract',
                       [modifier.strip() for modifier in text.split(' ')]))
            if len(modifier_list) == 0:
                class_modifier = []
            else:
                class_modifier = modifier_list
        elif i[1] == 'class-name':
            class_name = text
            class_and_interface_list.append({
                'name': class_name,
                'type': class_modifier
            })
        elif i[1] == 'inner-class':
            match_inner_list = extract_inner_class_query.captures(i[0])
            for j in match_inner_list:
                text = \
                    (src[j[0].start_point[0]])[j[0].start_point[1]:j[0].end_point[1]]
                text = re.sub("<.*>", "", text)
                if j[1] == 'inner-class-modifier':
                    modifier_list = list(
                        filter(
                            lambda x: x == 'static' or x == 'abstract',
                            [modifier.strip()
                             for modifier in text.split(' ')]))
                    if len(modifier_list) == 0:
                        inner_class_modifier = []
                    else:
                        inner_class_modifier = modifier_list
                elif j[1] == 'inner-class-name':
                    inner_class_name = class_name + '$' + text
                    class_and_interface_list.append({
                        'name':
                        inner_class_name,
                        'type':
                        inner_class_modifier
                    })


def get_pure_class_name(node, src):
    pure_match_list = extract_pure_class_query.captures(node)
    match_list = []
    for node in pure_match_list:
        if node not in match_list:
            match_list.append(node)
    class_name = ''
    class_modifier = []
    inner_class_name = ''
    inner_class_modifier = []
    for i in match_list:
        text = \
            (src[i[0].start_point[0]])[i[0].start_point[1]:i[0].end_point[1]]
        text = re.sub("<.*>", "", text)
        if i[1] == 'class-modifier':
            modifier_list = list(
                filter(lambda x: x == 'static' or x == 'abstract',
                       [modifier.strip() for modifier in text.split(' ')]))
            if len(modifier_list) == 0:
                class_modifier = []
            else:
                class_modifier = modifier_list
        elif i[1] == 'class-name':
            class_name = text
            class_and_interface_list.append({
                'name': class_name,
                'type': class_modifier
            })


def get_interface_name(node, src):
    match_list = extract_interface_query.captures(node)
    interface_name = ''
    for i in match_list:
        text = \
            (src[i[0].start_point[0]])[i[0].start_point[1]:i[0].end_point[1]]
        text = re.sub("<.*>", "", text)
        if i[1] == 'interface-name':
            interface_name = text
            class_and_interface_list.append({
                'name': interface_name,
                'type': ["interface"]
            })


def get_extends_class(node, src):
    match_list = extends_class_query.captures(node)
    class_name = ''
    super_class_list = []
    for i in match_list:
        text = \
            (src[i[0].start_point[0]])[i[0].start_point[1]:i[0].end_point[1]]
        text = re.sub("<.*>", "", text)
        if i[1] == 'class-name':
            class_name = text
        elif i[1] == 'class-list':
            text = text.replace('extends', '', 1)
            super_class_list = [
                super_class.strip() for super_class in text.split(',')
            ]
            extends_class_list.append({
                'child': class_name,
                'super': super_class_list
            })


def get_implements_interface(node, src):
    match_list = implements_interface_query.captures(node)
    class_name = ''
    super_interface_list = []
    for i in match_list:
        text = \
            (src[i[0].start_point[0]])[i[0].start_point[1]:i[0].end_point[1]]
        text = re.sub("<.*>", "", text)
        if i[1] == 'class-name':
            class_name = text
        elif i[1] == 'interface-list':
            text = text.replace('implements', '', 1)
            super_interface_list = [
                super_interface.strip() for super_interface in text.split(',')
            ]
            implements_interface_list.append({
                'child': class_name,
                'super': super_interface_list
            })


def get_extends_interface(node, src):
    match_list = extends_interface_query.captures(node)
    interface_name = ''
    super_interface_list = []
    for i in match_list:
        text = \
            (src[i[0].start_point[0]])[i[0].start_point[1]:i[0].end_point[1]]
        text = re.sub("<.*>", "", text)
        if i[1] == 'interface-name':
            interface_name = text
        elif i[1] == 'interface-list':
            text = text.replace('extends', '', 1)
            super_interface_list = [
                super_interface.strip() for super_interface in text.split(',')
            ]
            extends_interface_list.append({
                'child': interface_name,
                'super': super_interface_list
            })


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
    get_pure_class_name(tree.root_node, src_lines)
    get_interface_name(tree.root_node, src_lines)
    get_extends_class(tree.root_node, src_lines)
    get_implements_interface(tree.root_node, src_lines)
    get_extends_interface(tree.root_node, src_lines)


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
    extends_class_list,
    'implements_interface':
    implements_interface_list,
    'extends_interface':
    extends_interface_list
})
hierarchy_info_json = json.dumps(hierarchy_info)

name = ''
if dir_path[-1] == '/':
    name = 'hierarchy_info.json'
else:
    name = '/hierarchy_info.json'

with open(dir_path + name, 'w', encoding='utf-8') as \
    json_file:
    json.dump(hierarchy_info, json_file, indent=2)
