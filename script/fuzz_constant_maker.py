import os, pathlib
import re, json
import argparse


def get_target_class(proj):
    json_f = os.path.join(proj, "unitcon_properties", "error_summaries.json")
    with open(json_f, 'r') as f:
        data = json.load(f)

    x = data['Procname']
    cls_and_proc = re.sub("\(.*\).*", "", x)
    proc_name = cls_and_proc.split(".")[-1]
    cls_name = re.sub("\." + proc_name, "", cls_and_proc)

    return cls_name


def json_to_normal(proj):
    target_cls = get_target_class(proj)
    json_f = os.path.join(proj, "unitcon_properties", "extra_constant.json")

    with open(json_f, 'r') as f:
        data = json.load(f)

    x = data['String']

    const_set = set()
    for i in x:
        if target_cls in i['name']:
            const_set.add(i['value'])

    with open(os.path.join(proj, "unitcon_properties", "fuzz_constant"), 'w') as f:
        lst = list(const_set)
        lst.sort()
        for i in lst:
            if (len(i) > 10 or i.strip() == 'null' or i.strip() == '' or i.strip() == '\"\"'
                    or "\\" in i or str(i.encode('utf-8')) != 'b\'' + i + '\''):
                continue
            f.write(i + '\n')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("project",
                        type=pathlib.Path,
                        default=None,
                        help='Project directory where need to obtain enum information')
    args = parser.parse_args()
    json_to_normal(args.project)


if __name__ == '__main__':
    main()
