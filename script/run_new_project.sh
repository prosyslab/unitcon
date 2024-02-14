#!/bin/bash

Help() {
	# Display help
	echo "Run Unitcon on a new benchmark in the background"
	echo
	echo "Syntax: $0 [options] <project directory>"
	echo "Options:"
	echo " -h, --help                 Print this help message"
	echo " -v, --version <version>    Set Java version for compilation"
    echo " -e, --encoding             Set file encoding for execution"
	echo
}

SetOptions() {
	arguments=$(getopt --options hv:e: \
                       --longoptions help,version:,encoding: \
                       -- "$@")

    eval set -- "$arguments"

    while true; do
        case "$1" in
            -h | --help)
                Help
                exit 0
                ;;
            -v | --version)
                version=$2
                shift 2
                ;;
            -e | --encoding)
                encoding=$2
                shift 2
                ;;
            --)
                shift
                break
                ;;
            *)
                Help
                exit 1
                ;;
        esac
    done

    shift $((OPTIND-1))
    if [[ $# -le 0 ]]; then
        Help
        exit 1
    else
        project_directory=$1
        project_name=`basename "$project_directory"`
    fi
}


#########################################################################
#                             Main Program                              #
#########################################################################

version=8          # Default version
encoding="utf-8"   # Default encoding

SetOptions "$@"

echo "version='$version'"
echo "encoding='$encoding'"
echo "project_directory='$project_directory'"
echo "project_name='$project_name'"

nohup python3 -u script/new_bench_runner.py "$project_directory" --version $version --encoding $encoding -v > results/"$project_name"_output.txt 2>&1 &

exit 0