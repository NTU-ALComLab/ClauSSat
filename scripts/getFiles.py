import sys
from os import system, makedirs, remove
from os.path import basename

url = sys.argv[1]

cmd = 'wget -q {}'.format(url)
system(cmd)
webpage = basename(url)
cmd = 'grep \'^<span>\' {} > tmp'.format(webpage)
system(cmd)
remove(webpage)
makedirs(webpage)

filenames = [ line[6:-8] for line in open('tmp', 'r').readlines()[1:] ]
url = url.replace('tree', 'raw')

for filename in filenames:
    cmd = 'wget -q -P {} {}/{}'.format(webpage, url, filename)
    print(cmd)
    system(cmd)

cmd = 'gunzip {}/*'.format(webpage)
