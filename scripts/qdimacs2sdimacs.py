import sys
import os
import random

filenames = sys.argv[1:]

for filename in filenames:
    if filename.find('.qdimacs') == -1: continue
    lines = open(filename, 'r')
    sdimacsFile = filename.replace('.qdimacs', '.sdimacs')
    outFile = open(sdimacsFile, 'w')

    for line in lines:
        # print(line)
        if line[0] != 'a': outFile.write(line)
        else:
            prob = round(random.random(), 3)
            outFile.write('r {}'.format(prob))
            outFile.write(line[1:])

    outFile.close()        

