import json
import sys

file_path = sys.argv[1]

f = open(file_path, 'r')

content = f.readlines()
content = [ i.strip() for i in content]
content = list(filter(None, content))

summary = []
is_start = False
is_prop = False
is_footprint = False
prop_list = []
name = "" # function name
for i in content:
  if i == "{start":
    is_start = True
    continue
  elif i == "end}":
    prop_list = list(filter(None, prop_list))
    summary.append({'method': name, 'prop': prop_list})
    name = ""
    prop_list = []
    is_prop = False
    is_footprint = False
    is_start = False
    continue
  elif "\"function\"" in i:
    _name = i.split(':')
    _name = _name[1].strip()
    name = _name
  elif "\"prop\"" in i:
    is_prop = True
  elif is_prop and ("footprint" in i):
    is_footprint = True
  elif is_footprint:
    props = i.split(';')
    for i in props:
      i = i.replace("old_", '').replace('*', '').strip()
      if i != "" and i.strip()[-1] == ':':
        i = i[:-1]
      prop_list.append(i)

summary_json = json.dumps(summary)

with open(file_path+".json", 'w', encoding="utf-8") as json_file:
  json.dump(summary, json_file, indent=2)
