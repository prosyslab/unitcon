import json
import sys

file_path = sys.argv[1]

f = open(file_path, 'r')

content = f.readlines()
content = [i.strip() for i in content]
content = list(filter(None, content))

summary = []
is_start = False
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
        is_start = False
        continue
    elif "procname:" in i:
        _name = i.split(':')
        _name = _name[1].strip()
        name = _name
    elif "BoItv:" in i:
        _boitv = i.split(':')
        _boitv = _boitv[1].strip()
        boitv = _boitv
    elif "CItv:" in i:
        _citv = i.split(':')
        _citv = _citv[1].strip()
        citv = _citv
    elif "Precond:" in i:
        is_precond = True
        _precond = i.split(':')
        _precond = _precond[1].strip()
        precond = _precond
    elif "Postcond:" in i:
        is_postcond = True
        _postcond = i.split(':')
        _postcond = _postcond[1].strip()
        postcond = _postcond
    elif is_precond and (not is_postcond):
        next_precond = i.strip()
        precond = precond + next_precond
    elif is_postcond:
        next_postcond = i.strip()
        postcond = postcond + next_postcond

summary_json = json.dumps(summary)

with open(file_path + ".json", 'w', encoding="utf-8") as json_file:
    json.dump(summary, json_file, indent=2)
