import json
import sys

file_path = sys.argv[1]
f = open(file_path, 'r')

content = f.readlines()
content = [ i.strip() for i in content ]
content = list(filter(None, content))

call_prop = []
is_start = False
is_prop = False
prop_list = []
arg_list = []
caller_name = ""
callee_name = ""

for i in content:
  if i == "{start":
    is_start = True
  elif i == "end}":
    prop_list = list(filter(None, prop_list))
    arg_list = list(filter(None, arg_list))
    call_prop.append({'caller': caller_name, 'callee': callee_name, 'prop': prop_list, 'arg': arg_list})
    caller_name = ""
    callee_name = ""
    prop_list = []
    arg_list = []
    is_prop = False
    is_start = False
  elif "\"caller_pname\"" in i:
    _name = i.split(':')
    _name = _name[1].strip()
    caller_name = _name
  elif "\"callee_pname\"" in i:
    _name = i.split(':')
    _name = _name[1].strip()
    callee_name = _name
  elif "\"prop\"" in i:
    is_prop = True
    _prop = i.replace("\"prop\"", "")
    prop_list.extend([prop.replace("old_", "").strip() for prop in _prop[1].strip().split(';')])
  elif "footprint" in i:
    is_prop = False
  elif "\"args\"" in i:
    _args = i.split(':')
    arg_list = [ arg.strip() for arg in _args[1].strip().split("  ") ]
  elif is_prop:
    props = i.split(';')
    for prop in props:
      if "old_" in prop:
        prev_prop = prop_list[-1].split('=')
        curr_prop = prop.split('=')
        if prev_prop[0].strip() == curr_prop[0].replace("old_", "").strip():
          del prop_list[-1]
      prop = prop.replace("old_", "").strip()
      if prop != "" and prop.strip()[-1] == ':':
        prop = prop[:-1]
      prop_list.append(prop)
 
call_prop_json = json.dumps(call_prop)

with open(file_path+".json", 'w', encoding='utf-8') as json_file:
  json.dump(call_prop, json_file, indent=2)