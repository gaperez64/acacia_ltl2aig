#!/bin/bash

result_folder="translatedaig/" #"../../experiments/benchmarks/"
export PYTHONPATH="../AbsSynthe/pycosat-0.6.0":"../AbsSynthe/pycudd2.0.2/pycudd":$PYTHONPATH
export DYLD_LIBRARY_PATH="../AbsSynthe/pycudd2.0.2/cudd-2.4.2/lib":$DYLD_LIBRARY_PATH
export LD_LIBRARY_PATH="../AbsSynthe/pycudd2.0.2/cudd-2.4.2/lib":$LD_LIBRARY_PATH
synth_tool="../AbsSynthe/abssynthe.py"

function translate {
  echo "Translating ${folder}${common_pref}${i}${common_suff}_comp${k_bound}"
  python "ltl2aig.py" "${folder}${common_pref}${i}${common_suff}.ltl" "${folder}${common_pref}${i}${common_suff}.part" $k_bound "-c"
  exit_code=$?
  if [[ $exit_code != 10 && $exit_code != 20 && $exit_code != 30 ]]; then
    echo "ERROR: strange exit code ${exit_code}"
    exit
  fi
  # it was realizable
  if [[ $exit_code == 10 ]]; then
    echo "REAL"
    python ${synth_tool} $@ "${folder}${common_pref}${i}${common_suff}_comp${k_bound}_REAL.aag"
    synth=$?
    expect=10
    mv "${folder}${common_pref}${i}${common_suff}_comp${k_bound}_REAL.aag" ${result_folder}
  fi
  # it was unrealizable
  if [[ $exit_code == 20 ]]; then
    echo "UNREAL"
    python ${synth_tool} $@ "${folder}${common_pref}${i}${common_suff}_comp${k_bound}_UNREAL.aag"
    synth=$?
    expect=20
    mv "${folder}${common_pref}${i}${common_suff}_comp${k_bound}_UNREAL.aag" ${result_folder}
  fi
  # acacia did not conclude anything with the negated formula
  if [[ $exit_code == 30 ]]; then
    echo "??? assume UNREAL"
    python ${synth_tool} $@ "${folder}${common_pref}${i}${common_suff}_comp${k_bound}_UNREAL.aag"
    synth=$?
    expect=20
    mv "${folder}${common_pref}${i}${common_suff}_comp${k_bound}_UNREAL.aag" ${result_folder}
  fi
  # check if absynthe and acacia agree
  if [[ $synth != $expect ]]; then
    echo "ERROR: realizability results (${synth} != ${expect}) do not match!"
    exit
  fi
}

# translate all examples for the following k_bounds
for k_bound in `seq 1 10`;
do
folder="examples/demo-lily/"
common_pref="demo-v"
common_suff=""
for i in `seq 1 25`;
do
  translate
done

# translate all the buffer examples using the given k_bound
folder="examples/buffer/"
common_pref="gb_s2_r"
common_suff=""
for i in `seq 2 7`;
do
  translate
done

# translate all the load-balancing examples using the given k_bound
folder="examples/LoadBalancing/load-balancing/"
common_pref="load_full_"
common_suff=""
for i in `seq 2 6`;
do
  translate
done

folder="examples/LoadBalancing/load-balancing-environment/"
common_pref="load_"
common_suff="c_comp"
for i in 2 3;
do
  translate
done

# translate SRA examples
folder="examples/SRA/"
common_pref="sra_"
common_suff=""
for i in 2 3;
do
  translate
done

# translate LTL2DBA examples
folder="examples/LTL2DBA/"
common_pref="ltl2dba_0"
common_suff=""
for i in `seq 4 9`;
do
  translate
done
common_pref="ltl2dba_"
for i in `seq 10 27`;
do
  translate
done

# translate LTL2DBA examples
folder="examples/LTL2DPA/"
common_pref="ltl2dpa_0"
common_suff=""
for i in `seq 1 9`;
do
  translate
done
common_pref="ltl2dpa_"
for i in `seq 10 23`;
do
  translate
done
done # and the k_bound loop
