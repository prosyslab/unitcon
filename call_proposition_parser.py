import json
import sys

file_path = sys.argv[1]
f = open(file_path, 'r')

content = f.readlines()
content = [i.strip() for i in content]
content = list(filter(None, content))

call_prop = []
is_start = False
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
        is_start = False
    elif "caller" in i:
        _name = i.split(':')
        _name = _name[1].strip()
        caller_name = _name
    elif "callee" in i:
        _name = i.split(':')
        _name = _name[1].strip()
        callee_name = _name
    elif "BoItv" in i:
        _boitv = i.split(':')
        _boitv = _boitv[2].strip()
        boitv = _boitv
    elif "CItv" in i:
        _citv = i.split(':')
        _citv = _citv[1].strip()
        citv = _citv
    elif "Precond" in i:
        is_precond = True
        _precond = i.split(':')
        _precond = _precond[1].strip()
        precond = _precond
    elif "Postcond" in i:
        is_postcond = True
        _postcond = i.split(':')
        _postcond = _postcond[1].strip()
        postcond = _postcond
    elif "actual" in i:
        _args = i.split(':')
        arg_list = [arg.strip() for arg in _args[1].strip().split("  ")]
    elif is_precond and (not is_postcond):
        next_precond = i.strip()
        precond = precond + next_precond
    elif is_postcond:
        next_postcond = i.strip()
        postcond = postcond + next_postcond
    

call_prop_json = json.dumps(call_prop)

with open(file_path + ".json", 'w', encoding='utf-8') as json_file:
    json.dump(call_prop, json_file, indent=2)
