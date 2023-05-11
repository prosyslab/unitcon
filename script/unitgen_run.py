import os, sys, subprocess
from os import path
import shutil, glob
import re


def print_test_case(unitgen_tc):
    print('----------')
    print(unitgen_tc[0])
    print()
    print(unitgen_tc[1])


def modify_tc_file(copied_tc_file, tc_file, unitgen_tc):
    lines = []
    insert_import = False
    insert_tc = False

    with open(copied_tc_file, 'r') as fr:
        lines = fr.readlines()

    with open(tc_file, 'w') as fw:
        for line in lines:
            if ('class' in line) and (not insert_import):
                fw.write(unitgen_tc[0] + '\n')
                insert_import = True
            elif ('@Test' in line) and (not insert_tc):
                fw.write(unitgen_tc[1] + '\n')
                insert_tc = True
            fw.write(line)


def check_one_tc(command, target_test, origin_src_path, copied_tc_file,
                 tc_file, unitgen_tc):
    os.chdir(origin_src_path)  # change the path for running current script
    if os.path.exists(tc_file):
        os.remove(tc_file)  # absolute path

    modify_tc_file(copied_tc_file, tc_file, unitgen_tc)

    # execute shell command & read the result
    # command = command.append("-Dtest=" + target_test)
    result = subprocess.run(command, stdout=subprocess.PIPE, text=True)
    try:
        error_test = result.stdout.split("Tests in error:")[1]
        if "test(" in error_test:
            return True
        else:
            return False
    except:
        return False


def check_all_tc(command, target_test, origin_src_path, copied_tc_file,
                 tc_file, unitgen_tc_file):
    all_tc = ''
    import_and_tc = []

    with open(unitgen_tc_file, 'r') as f:
        line = f.read()
        all_tc = re.sub('Logging to unitgen-out\n', '', line)
        all_tc = re.sub('duration: [0-9]*', '', all_tc)

    tc_list = list(filter(None, all_tc.split('\n\n')))

    try:
        for i in range(0, len(tc_list), 2):
            import_and_tc.append(tc_list[i:i + 2])
        for tc in import_and_tc:
            if check_one_tc(command, target_test, origin_src_path,
                            copied_tc_file, tc_file, tc):
                return (True, tc)
            else:
                continue
        return (False, [])
    except:
        return (False, [])


def main(origin_src_path, tc_file_name, unitgen_path, unitgen_tc_file):
    print('Target Project: ' + origin_src_path)
    copy_folder_path = unitgen_path + '/' + 'TC_tmp'
    copied_tc_file = copy_folder_path + '/' + tc_file_name + '.java'
    tc_file = glob.glob(origin_src_path + '**/' + tc_file_name + '.java',
                        recursive=True)[0]

    if not path.isdir(copy_folder_path):
        os.makedirs(copy_folder_path)

    if not path.exists(copied_tc_file):
        shutil.copy(tc_file, copied_tc_file)

    command = "mvn clean package -V -B -Denforcer.skip=true -Dcheckstyle.skip=true -Dcobertura.skip=true -Drat.skip=true -Dlicense.skip=true -Dfindbugs.skip=true -Dgpg.skip=true -Dskip.npm=true -Dskip.gulp=true -Dskip.bower=true -DskipITs=true -Dpmd.skip=true -DfailIfNoTests=false".split(
        ' ')
    check = check_all_tc(command, tc_file_name, origin_src_path,
                         copied_tc_file, tc_file, unitgen_tc_file)
    if check[0]:
        print('Success')
        print_test_case(check[1])
    else:
        print('Fail')


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4])
