import json
import sys

file_path = sys.argv[1]
f = open(file_path, 'r')

content = f.readlines()
content = [i.strip() for i in content]
content = list(filter(None, content))

call_prop = []
is_start = False
is_boitv = False
is_citv = False
is_precond = False
is_postcond = False
boitv = ""
citv = ""
precond = ""
postcond = ""
arg_list = []
caller_name = ""
callee_name = ""

for i in content:
    if i == "{start":
        is_start = True
        continue
    elif i == "end}":
        arg_list = list(filter(None, arg_list))
        call_prop.append({
            'Caller': caller_name,
            'Callee': callee_name,
            'BoItv': boitv,
            'CItv': citv,
            'Precond': precond,
            'Postcond': postcond,
            'Arg': arg_list
        })
        caller_name = ""
        callee_name = ""
        boitv = ""
        citv = ""
        precond = ""
        postcond = ""
        arg_list = []
        is_postcond = False
        is_precond = False
        is_citv = False
        is_boitv = False
        is_start = False
    elif "caller:" in i:
        _name = i.split(':')
        caller_name = _name[1].strip()
    elif "callee:" in i:
        _name = i.split(':')
        callee_name = _name[1].strip()
    elif "BoItv:" in i:
        is_boitv = True
        _boitv = i.split(':')
        if "BoItv" in _boitv[1]:
            _boitv = _boitv[2].strip()
        else:
            _boitv = _boitv[1].strip()
        boitv = _boitv
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
    elif "actual:" in i:
        _args = i.split(':')
        arg_list = [arg.strip() for arg in _args[1].strip().split("  ")]
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
    
call_prop_json = json.dumps(call_prop)

with open(file_path + ".json", 'w', encoding='utf-8') as json_file:
    json.dump(call_prop, json_file, indent=2)
