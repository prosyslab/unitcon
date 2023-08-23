from tree_sitter import Language, Parser
import os
import sys
import json
import re

Language.build_library('build/languages.so', ['./tree-sitter-java'])

J_LANGUAGE = Language('build/languages.so', 'java')
parser = Parser()
parser.set_language(J_LANGUAGE)

extract_enum_query = J_LANGUAGE.query("""
(enum_declaration
name: (identifier) @enum-name
)
(enum_body
(enum_constant) @enum-const)

""")

enum_list = []


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
    text = re.sub("{", "", text)
    return text


def get_enum(node, src):
    match_list = extract_enum_query.captures(node)
    enum_name = ''
    for i in match_list:
        text = get_text(i, src)
        if i[1] == 'enum-name':
            enum_name = text
        elif i[1] == 'enum-const':
            enum_list.append({
                'enum': enum_name,
                'const': re.sub("\(.*\)", "", text)
            })


def one_file_enum_info(src, encoding):
    f = open(src, 'r', encoding=encoding)
    src_lines = f.readlines()

    def read_callable(byte_offset, point):
        (row, column) = point
        if row >= len(src_lines) or column >= len(src_lines[row]):
            return None
        return (src_lines[row])[column:].encode('utf8')

    tree = parser.parse(read_callable)
    get_enum(tree.root_node, src_lines)


def all_file_enum_info(dirname, encoding):
    filenames = os.listdir(dirname)
    for filename in filenames:
        full_filename = os.path.join(dirname, filename)
        if os.path.isdir(full_filename):
            all_file_enum_info(full_filename, encoding)
        else:
            ext = os.path.splitext(full_filename)[-1]
            if ext == '.java':
                one_file_enum_info(full_filename, encoding)


if len(sys.argv) != 3:
    print("Usage: directory_path encoding")
    sys.exit()

enum_info = []
dir_path = sys.argv[1]
encoding = sys.argv[2]

all_file_enum_info(dir_path, encoding)

name = ''
if dir_path[-1] == '/':
    name = 'enum_info.json'
else:
    name = '/enum_info.json'

with open(dir_path + name, 'w', encoding='utf-8') as json_file:
    json.dump(enum_list, json_file, indent=2)
