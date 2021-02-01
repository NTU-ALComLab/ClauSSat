import sys


def main(argv):
    filenames = argv[1:]
    for filename in filenames:
        if filename.find('.sdimacs') == -1: continue
        outfile = filename.replace('.sdimacs', '.ssat')
        f = open(filename, 'r')
        lines = f.readlines()
        f.close()
        ln = 0

        f = open(outfile, 'w')

        while True:
            par = lines[ln].strip().split(' ')
            if par[0] != 'c': break
            ln += 1

        par = lines[ln].strip().split(' ')
        var_num, c_num = par[2], par[3]
        f.write('%s\n' % var_num)
        f.write('%s\n' % c_num)
        ln += 1

        var = [str(i) for i in range(1, int(var_num)+1)]

        while True:
            par = lines[ln].strip().split(' ')
            if par[0] == 'r':
                for v in par[2:-1]:
                    f.write('%s %s R %s\n' % (v, 'x'+v, par[1]))
                    var.remove(v)
            elif par[0] == 'e':
                for v in par[1:-1]:
                    f.write('%s %s E\n' % (v, 'x'+v))
                    var.remove(v)
            else: break
            ln += 1

        for v in var:
            f.write('%s %s E\n' % (v, 'x'+v))

        for line in lines[ln:]:
            f.write('%s' % line)
        f.close()
            
            
        # for line in lines:
        #     par = line.strip().split(' ')
        #     if par[0] == 'p':
        #         var_num = par[2]
        #         c_num = par[3]
        #         f.write('%s\n' % var_num)
        #         f.write('%s\n' % c_num)
        #     elif par[0] == 'r':
        #         for v in par[2:-1]:
        #             f.write('%s %s R %s\n' % (v, 'x'+v, par[1]))
        #     elif par[0] == 'e':
        #         for v in par[1:-1]:
        #             f.write('%s %s E\n' % (v, 'x'+v))
        #     else:
        #         f.write('%s' % line)
        # f.close()


if __name__ == "__main__":
    main(sys.argv)
