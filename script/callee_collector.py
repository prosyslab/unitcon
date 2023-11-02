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
  name: (identifier) @class-name
  body: (class_body) @class-body
)
""")

extract_method_name_query = J_LANGUAGE.query("""
(method_declaration
  name: (identifier) @method-name
  parameters: (formal_parameters) @method-param
  body: (block) @method-body
)
""")

extract_callee_query = J_LANGUAGE.query("""
(method_invocation
  name: (identifier) @callee-name
  arguments: (argument_list) @callee-arg
)
""")

extract_catch_block_query = J_LANGUAGE.query("""
(statement
  (try_statement
    (catch_clause (block) @catch-block)
  )
)
""")

extra_callee = []


def remove_generic(name):
    rename = name
    index_stack = []
    for i in range(len(name)):
        if name[i] == '<':
            index_stack.append(i)
        elif name[i] == '>':
            prev_brk = index_stack.pop()
            add_space = ' ' * (i + 1 - prev_brk)
            rename = rename[0:prev_brk] + add_space + rename[i + 1:]
    return rename


def remove_parentheses(name):
    rename = name
    index_stack = []
    for i in range(1, len(name)):
        if name[i] == '(':
            index_stack.append(i)
        elif name[i] == ')':
            if index_stack == []:
                continue
            prev_brk = index_stack.pop()
            add_space = ' ' * (i + 1 - prev_brk)
            rename = rename[0:prev_brk] + add_space + rename[i + 1:]
    return rename


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


def get_callee_name(node, src, callee_list):
    match_list = extract_callee_query.captures(node)
    callee_name = ""
    num_of_arg = -1
    for i in match_list:
        text = get_text(i, src)
        if i[1] == 'callee-name':
            callee_name = text
        elif i[1] == 'callee-arg':
            if callee_name == '':
                continue
            text = re.sub("[();]", "", remove_parentheses(text)).strip()
            num_of_arg = len(text.split(','))
            if text == "":
                num_of_arg = 0
            callee_list.append({
                'callee': callee_name,
                'num_of_arg': num_of_arg
            })
            callee_name = ""
            num_of_arg = -1
    return callee_list


def get_catch_block(node, src):
    match_list = extract_catch_block_query.captures(node)
    callee_list = []
    for i in match_list:
        text = get_text(i, src)
        if i[1] == 'catch-block':
            callee_list = get_callee_name(i[0], src, callee_list)
    return callee_list


def get_method_name(node, src, class_name):
    match_list = extract_method_name_query.captures(node)
    method_name = ""
    param_types = ""
    for i in match_list:
        text = get_text(i, src)
        if i[1] == 'method-name':
            method_name = text
        elif i[1] == 'method-param':
            param_type_list = [
                p.strip().split(' ')[0]
                for p in remove_generic(text).split(',')
            ]
            param_types = ','.join(param_type_list)
            if not param_types.startswith('('):
                param_types = '(' + param_types
            if not param_types.endswith(')'):
                param_types = param_types + ')'
        elif i[1] == 'method-body':
            callee_list = get_catch_block(i[0], src)
            if method_name == "" or param_types == "" or not callee_list:
                continue
            extra_callee.append({
                'caller': class_name + '.' + method_name + param_types,
                'callee': callee_list
            })
            method_name = ""
            param_types = ""


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
        return get_parent_class_name(parent, src, parent_name + '$' + name)


def get_class_name(node, src):
    match_list = extract_class_name_query.captures(node)
    class_name = ''
    for i in match_list:
        text = get_text(i, src)
        if i[1] == 'class-name':
            class_name = re.sub("\$$", "",
                                get_parent_class_name(i[0], src, ''))
        elif i[1] == 'class-body':
            if class_name == '':
                continue
            get_method_name(i[0], src, class_name)


def one_file_collector(src, encoding):
    src_lines = []
    with open(src, 'r', encoding=encoding) as f:
        src_lines = f.readlines()

    def read_callable(byte_offset, point):
        (row, column) = point
        if row >= len(src_lines) or column >= len(src_lines[row]):
            return None
        return (src_lines[row])[column:].encode('utf8')

    tree = parser.parse(read_callable)
    get_class_name(tree.root_node, src_lines)


def all_files_collector(project_dir, encoding):
    for dirpath, dirnames, filenames in os.walk(project_dir):
        for filename in filenames:
            if filename.endswith(".java"):
                one_file_collector(os.path.join(dirpath, filename), encoding)


def mk_json_file(project_dir):
    prop_dir = os.path.join(project_dir, "unitcon_properties")
    if not os.path.isdir(prop_dir):
        os.makedirs(prop_dir)
    with open(os.path.join(prop_dir, "extra_callee.json"),
              'w',
              encoding='utf-8') as json_file:
        json.dump(extra_callee, json_file, indent=2)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "project",
        type=pathlib.Path,
        default=None,
        help='Project directory where need to create build command files')
    parser.add_argument("--encoding",
                        type=str,
                        default="utf-8",
                        help='Encoding type of project')
    args = parser.parse_args()
    all_files_collector(args.project, args.encoding)
    mk_json_file(args.project)


if __name__ == "__main__":
    main()
