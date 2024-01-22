from tree_sitter import Language, Parser
import os, pathlib
import re, json
import argparse

Language.build_library('build/languages.so', ['./tree-sitter-java'])

J_LANGUAGE = Language('build/languages.so', 'java')
parser = Parser()
parser.set_language(J_LANGUAGE)

extract_class_name_query = J_LANGUAGE.query("""
(package_declaration)* @package-name
(class_declaration
  name: (identifier) @class-name
  body: (class_body) @class-body
)
""")

extract_method_name_query = J_LANGUAGE.query("""
(method_declaration
  name: (identifier) @method-name
  body: (block) @method-body
)
""")

extract_create_object_query = J_LANGUAGE.query("""
(field_declaration
  (modifiers) @variable-modifier
  (_unannotated_type) @variable-type
  (variable_declarator
    (identifier) @variable-name
    (object_creation_expression)
  )
)
""")

extract_return_object_query = J_LANGUAGE.query("""
(field_declaration
  (modifiers) @variable-modifier
  (_unannotated_type) @variable-type
  (variable_declarator
    (identifier) @variable-name
    (method_invocation)
  )
)
""")

extract_assign_primitive_query = J_LANGUAGE.query("""
(field_declaration
  (_unannotated_type) @constant-type
  (variable_declarator
    (_literal) @constant-value
  )
)
""")

# extract string.equals(string)
extract_if_primitive_query = J_LANGUAGE.query("""
(if_statement
  (parenthesized_expression
    (method_invocation
      (string_literal)* @String
      (argument_list
        (string_literal)* @String
      )
    )
  )
)
""")

# predefined type
constant = {
    'int': [],
    'long': [],
    'float': [],
    'double': [],
    'char': [],
    'String': [],
    'Object': []
}


def get_package_class(package_name, class_name):
    if package_name:
        class_name = package_name + '.' + class_name
    return class_name


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


def get_object(node, src, class_name):
    lst = extract_create_object_query.captures(
        node) + extract_return_object_query.captures(node)
    var_modifier = False
    var_type = ''
    for i in lst:
        text = get_text(i, src)
        if i[1] == 'variable-modifier':
            var_modifier = True if all(
                x in text for x in ["public", "static"]) else False
        elif i[1] == 'variable-type':
            var_type = text
        elif i[1] == 'variable-name':
            if not var_modifier:
                var_type = ''
                continue
            if class_name.endswith(var_type):
                constant['Object'].append({'name': class_name, 'value': text})


def get_assign_primitive(node, src, class_name):
    lst = extract_assign_primitive_query.captures(node)
    const_type = ''
    for i in lst:
        text = get_text(i, src)
        if i[1] == 'constant-type':
            const_type = text
        elif i[1] == 'constant-value':
            if const_type in constant:
                constant[const_type].append({
                    'name': class_name,
                    'value': text
                })


def get_if_primitive(node, src, type_name):
    lst = extract_if_primitive_query.captures(node)
    for i in lst:
        text = get_text(i, src)
        if "\"" not in text:
            continue
        elif i[1] == 'String':
            constant['String'].append({'name': type_name, 'value': text})


def get_if_primitive_from_method(node, src, class_name):
    lst = extract_method_name_query.captures(node)
    method_name = ''
    for i in lst:
        text = get_text(i, src)
        if i[1] == 'method-name':
            method_name = re.sub("\(.*", "", text)
        elif i[1] == 'method-body':
            get_if_primitive(i[0], src, class_name + "." + method_name)


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
    package_name = ''
    class_name = ''
    for i in match_list:
        text = get_text(i, src)
        if i[1] == 'package-name':
            package_name = text.replace('package', '', 1).replace(';', '',
                                                                  1).strip()
        elif i[1] == 'class-name':
            class_name = re.sub("\$$", "",
                                get_parent_class_name(i[0], src, ''))
            class_name = get_package_class(package_name, class_name)
        elif i[1] == 'class-body':
            if class_name == '':
                continue
            get_object(i[0], src, class_name)
            get_assign_primitive(i[0], src, class_name)
            get_if_primitive_from_method(i[0], src, class_name)


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
    with open(os.path.join(prop_dir, "extra_constant.json"),
              'w',
              encoding='utf-8') as json_file:
        json.dump(constant, json_file, indent=2)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "project",
        type=pathlib.Path,
        default=None,
        help='Project directory where need to obtain additional constant')
    parser.add_argument("--encoding",
                        type=str,
                        default="utf-8",
                        help='Encoding type of project')
    args = parser.parse_args()
    all_files_collector(args.project, args.encoding)
    mk_json_file(args.project)


if __name__ == "__main__":
    main()
