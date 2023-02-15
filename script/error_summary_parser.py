import json
import sys

file_path = sys.argv[1]

f = open(file_path, 'r')

content = f.readlines()
content = [i.strip() for i in content]
content = list(filter(None, content))

summary = []
is_start = False
is_boitv = False
is_citv = False
is_precond = False
is_postcond = False
boitv = ""
citv = ""
precond = ""
postcond = ""
name = ""  # function name
for i in content:
    if i == "{start":
        is_start = True
        continue
    elif i == "end}":
        summary.append({
            'method': name,
            'BoItv': boitv,
            'CItv': citv,
            'Precond': precond,
            'Postcond': postcond
        })
        name = ""
        boitv = ""
        citv = ""
        precond = ""
        postcond = ""
        is_postcond = False
        is_precond = False
        is_citv = False
        is_boitv = False
        is_start = False
        continue
    elif "procname:" in i:
        _name = i.split(':')
        name = _name[1].strip()
    elif "BoItv:" in i:
        is_boitv = True
        _boitv = i.split(':')
        boitv = _boitv[1].strip()
    elif "CItv:" in i:
        is_citv = True
        is_boitv = False
        _citv = i.split(':')
        citv = _citv[1].strip()
    elif "Precond:" in i:
        is_precond = True
        is_citv = False
        _precond = i.split(':')
        precond = _precond[1].strip()
    elif "Postcond:" in i:
        is_postcond = True
        is_precond = False
        _postcond = i.split(':')
        postcond = _postcond[1].strip()
    elif is_boitv:
        next_boitv = i.strip()
        boitv = boitv + next_boitv
    elif is_citv:
        next_citv = i.strip()
        citv = citv + next_citv
    elif is_precond:
        next_precond = i.strip()
        precond = precond + next_precond
    elif is_postcond:
        next_postcond = i.strip()
        postcond = postcond + next_postcond

summary_json = json.dumps(summary)

with open(file_path + ".json", 'w', encoding="utf-8") as json_file:
    json.dump(summary, json_file, indent=2)
