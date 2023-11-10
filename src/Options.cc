#include <iostream>
#include <stdlib.h>
#include <getopt.h>
#include <stdio.h>
using std::ostream;
using std::endl;
#include "Options.hh"
bool Options::parse(int argc,char **argv) {
  static struct option long_options[] = {{0, 0, 0, 0}};
  int c;
  bool return_value = true;
  while (1) {
    int option_index = 0;
    c = getopt_long(argc, argv, "vhegyupnwkmsctdx", long_options, &option_index);
    if (c == -1) break;
    switch (c) {
    case 'v':
      ++verbose;
      break;
    case 'h':
      ++help;
      break;
    case 'e':
      ++ex_inst;
      break;
    case 'g':
      ++groups;
      break;
    case 'y':
      ++lazy;
      break;
    case 'u':
      ++pin;
      break;
    case 'p':
      ++weak_pri;
      break;
    case 'n':
      ++strong_pri;
      break;
    case 'w':
      ++pin_pol;
      break;
    case 'k':
      ++cert;
      break;
    case 'm':
      ++cert2Mfs;
      break;
    case 's':
      ++ssat;
      break;
    case 'c':
      ++cache;
      break;
    case 't':
      ++partial;
      break;
    case 'd':
      ++dynamic;
      break;
    case 'x':
      ++extra_verb;
      break;
    case '?':
      // if (isprint(optopt)) fprintf (stderr, "Unknown option -%c.\n", optopt);
      return_value = false;
      break;
    }
  }
  for (int i=optind; i<argc; ++i) rest.push_back(argv[i]);
  return return_value;
}
ostream& Options::print(ostream& out) const {
  out<< " -v ";
  out<< "    "<<" verbosity level ";
  out<< endl;
  out<< " -h ";
  out<< "    "<<" print help ";
  out<< endl;
  out<< " -e ";
  out<< "    "<<" use existential instantiation ";
  out<< endl;
  out<< " -g ";
  out<< "    "<<" merge clauses into groups ";
  out<< endl;
  out<< " -y ";
  out<< "    "<<" lazy var encoding ";
  out<< endl;
  out<< " -u ";
  out<< "    "<<" cube distribution please combind this command with -w ";
  out<< endl;
  out<< " -p ";
  out<< "    "<<" weak decision priority ";
  out<< endl;
  out<< " -n ";
  out<< "    "<<" universal analysis strengthening ";
  out<< endl;
  out<< " -w ";
  out<< "    "<<" please combined this command with -u ";
  out<< endl;
  out<< " -k ";
  out<< "    "<<" generate certification function (_s.blif/_h.blif) ";
  out<< endl;
  out<< " -m ";
  out<< "    "<<" generate onsets and caresets of certification function (_ms.blif/_mf.blif) ";
  out<< endl;
  out<< " -s ";
  out<< "    "<<" ssat solving with clause selection ";
  out<< endl;
  out<< " -c ";
  out<< "    "<<" enable caching results ";
  out<< endl;
  out<< " -t ";
  out<< "    "<<" enable partial assignment pruning ";
  out<< endl;
  out<< " -d ";
  out<< "    "<<" enable dynamic dropping ";
  out<< endl;
  out<< " -x ";
  out<< "    "<<" enable extra verbose information at existential QLev 0 ";
  out<< endl;
  return out;
}
ostream& operator << (ostream& out, const Options& opt) {
  out << "c options: ";
  if(opt.get_verbose()) out << "-v ";
  if(opt.get_help()) out << "-h ";
  if(opt.get_ex_inst()) out << "-e ";
  if(opt.get_groups()) out << "-g ";
  if(opt.get_lazy()) out << "-y ";
  if(opt.get_pin()) out << "-u ";
  if(opt.get_weak_pri()) out << "-p ";
  if(opt.get_strong_pri()) out << "-n ";
  if(opt.get_pin_pol()) out << "-w ";
  if(opt.get_cert()) out << "-k ";
  if(opt.get_cert2Mfs()) out << "-m ";
  if(opt.get_ssat()) out << "-s ";
  if(opt.get_cache()) out << "-c ";
  if(opt.get_partial()) out << "-t ";
  if(opt.get_dynamic()) out << "-d ";
  if(opt.get_extra_verb()) out << "-x ";
  return out;
}
