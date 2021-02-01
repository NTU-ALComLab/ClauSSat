import sys
from os import listdir, system, makedirs
from os.path import isfile, join, splitext

timeLim = '1000s'
TIME = '/usr/bin/time -v'
TIMEOUT = 'timeout {}'.format(timeLim)

SOLVER = 'qesto'
EXEC = './qesto -uwsc'
FORM = 'sdimacs'

LOG_DIR = 'logs/'

print('Solving with {}'.format(EXEC[2:]))

# uncomment to run benchmark
SSAT_DIR = [
                # 2-level
                # 'benchmarks/ssatER/MPEC/'+FORM ,
                # 'benchmarks/ssatER/planning/ToiletA/'+FORM ,
                # 'benchmarks/ssatER/planning/conformant/'+FORM ,
                # 'benchmarks/ssatER/planning/sand-castle/'+FORM ,
                # 'benchmarks/ssatER/planning/tiger/'+FORM ,
                # 'benchmarks/ssatER/MaxCount/'+FORM ,

                # 'benchmarks/ssatRE/PEC/'+FORM ,
                # 'benchmarks/ssatRE/stracomp/'+FORM ,

                # Multilevel
                # 'benchmarks/Connect2/'+FORM ,
                # 'benchmarks/gttt_3x3/'+FORM ,
                # 'benchmarks/k_branch_n/'+FORM ,
                # 'benchmarks/Tree/'+FORM ,
                # 'benchmarks/RobotsD2/'+FORM ,
                # 'benchmarks/ev-pr-4x4-log/'+FORM ,
                # 'benchmarks/arbiter/'+FORM ,
                # 'benchmarks/Planning-CTE/depots/'+FORM,
                # 'benchmarks/Planning-CTE/pipesnotankage/'+FORM ,
                # 'benchmarks/k_ph_p/'+FORM ,
                # 'benchmarks/Counter/'+FORM ,
                # 'benchmarks/tlc/'+FORM ,
                # 'benchmarks/Adder/'+FORM
               ]



for directory in SSAT_DIR:
    files = [ join(directory,f) for f in listdir(directory) if isfile(join(directory,f)) ]
    log_path = LOG_DIR + directory[11:]
    makedirs(log_path, exist_ok=True)
    for f in files[2:]:
        fileName, fileExt = splitext(f)
        LOG_FILE = LOG_DIR+fileName[11:]+'.log'
        cmd = '{} {} {} {} > {} 2>> {}'.format(TIME, TIMEOUT, EXEC, f, LOG_FILE, LOG_FILE)
        print('Running {}'.format(cmd))
        system(cmd)

