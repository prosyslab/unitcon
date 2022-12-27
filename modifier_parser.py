from tree_sitter import Language, Parser
import os, sys, json

Language.build_library(
  'build/languages.so',
  [
    './tree-sitter-java'
  ]
)

J_LANGUAGE = Language('build/languages.so', 'java')
parser = Parser()
parser.set_language(J_LANGUAGE)

method_query = J_LANGUAGE.query("""
(class_declaration
  name: (identifier) @class-name
  body: (class_body
    (method_declaration
      (modifiers)* @modifier
      name: (identifier) @method-name
      parameters: (formal_parameters) @parameter)))
""")

constructor_query = J_LANGUAGE.query("""
(class_declaration
  name: (identifier) @class-name
  body: (class_body
    (constructor_declaration
      (modifiers)* @modifier
      parameters: (formal_parameters) @parameter)))
""")

def get_method_info(node, src):
  match_list = method_query.captures(node)
  class_name = ""
  modifier = ""
  method_name = ""
  parameter = ""
  set_modifier = False
  for i in match_list:
    text = src[i[0].start_point[0]][i[0].start_point[1]:i[0].end_point[1]]
    if i[1] == 'class-name':
      class_name = text
    elif i[1] == 'modifier':
      set_modifier = True
      modifier = text
    elif i[1] == 'method-name':
      method_name = text
    elif i[1] == 'parameter':
      parameter = text
      parameter = parameter[1:-1].strip().split(",")
      param = ""
      for i in parameter:
        split_type = i.strip().split(" ")[0].strip()
        param = param+","+split_type
      param = param.lstrip(",")
      param = "("+param+")"

      if set_modifier:
        method_info_list.append({'name': class_name+"."+method_name+param, 'modifier': modifier})
      else:
        method_info_list.append({'name': class_name+"."+method_name+param, 'modifier': "default"})
      set_modifier = False

def get_constructor_info(node, src):
  match_list = constructor_query.captures(node)
  class_name = ""
  modifier = ""
  parameter = ""
  set_modifier = False
  for i in match_list:
    text = src[i[0].start_point[0]][i[0].start_point[1]:i[0].end_point[1]]
    if i[1] == 'class-name':
      class_name = text
    elif i[1] == 'modifier':
      set_modifier = True
      modifier = text
    elif i[1] == 'parameter':
      parameter = text
      parameter = parameter[1:-1].strip().split(",")
      param = ""
      for i in parameter:
        split_type = i.split(" ")[0].strip()
        param = param+","+split_type
      param = param.lstrip(",")
      param = "("+param+")"

      if set_modifier:
        method_info_list.append({'name': class_name+"."+"<init>"+param, 'modifier': modifier})
      else:
        method_info_list.append({'name': class_name+"."+"<init>"+param, 'modifier': "default"})
      set_modifier = False

def one_file_method_info(src):
  f = open(src, 'r')
  src_lines = f.readlines()

  def read_callable(byte_offset, point):
    row, column = point
    if row >= len(src_lines) or column >= len(src_lines[row]):
      return None
    return src_lines[row][column:].encode('utf8')

  tree = parser.parse(read_callable)
  get_method_info(tree.root_node, src_lines)
  get_constructor_info(tree.root_node, src_lines)

def all_file_method_info(dirname):
  filenames = os.listdir(dirname)
  for filename in filenames:
    full_filename = os.path.join(dirname, filename)
    if os.path.isdir(full_filename):
      all_file_method_info(full_filename)
    else:
      ext = os.path.splitext(full_filename)[-1]
      if ext == '.java':
        one_file_method_info(full_filename)


method_info_list = []
dir_path = sys.argv[1]
all_file_method_info(dir_path)

method_info_json = json.dumps(method_info_list)

with open(dir_path+".json", 'w', encoding="utf-8") as json_file:
  json.dump(method_info_list, json_file, indent=2)
