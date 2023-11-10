#ifndef Options_HH
#define Options_HH
#include <string>
#include <vector>
#include <ostream>
using std::string;
class Options {
public:
bool parse(int argc,char **argv);
  Options ()
  : verbose ( 0 )
  , help ( 0 )
  , ex_inst ( 0 )
  , groups ( 0 )
  , lazy ( 0 )
  , pin ( 0 )
  , weak_pri ( 0 )
  , strong_pri ( 0 )
  , pin_pol ( 0 )
  , cert ( 0 )
  , cert2Mfs ( 0 )
  , ssat ( 0 )
  , cache ( 0 )
  , partial ( 0 )
  , dynamic ( 0 )
  , extra_verb ( 0 )
  {}
  const std::vector<string>&    get_rest() const { return rest; }
  std::ostream&                 print(std::ostream& out) const;
  int                         get_verbose() const { return verbose ;}
  int                         get_help() const { return help ;}
  int                         get_ex_inst() const { return ex_inst ;}
  int                         get_groups() const { return groups ;}
  int                         get_lazy() const { return lazy ;}
  int                         get_pin() const { return pin ;}
  int                         get_weak_pri() const { return weak_pri ;}
  int                         get_strong_pri() const { return strong_pri ;}
  int                         get_pin_pol() const { return pin_pol ;}
  int                         get_cert() const { return cert ;}
  int                         get_cert2Mfs() const { return cert2Mfs ;}
  int                         get_ssat() const { return ssat ;}
  int                         get_cache() const { return cache ;}
  int                         get_partial() const { return partial ;}
  int                         get_dynamic() const { return dynamic ;}
  int                         get_extra_verb() const { return extra_verb ;}
  friend std::ostream& operator << (std::ostream& out, const Options& opt);
private:
  std::vector<string> rest;
  int verbose ;
  int help ;
  int ex_inst ;
  int groups ;
  int lazy ;
  int pin ;
  int weak_pri ;
  int strong_pri ;
  int pin_pol ;
  int cert ;
  int cert2Mfs ;
  int ssat ;
  int cache ;
  int partial ;
  int dynamic ;
  int extra_verb ;
};
#endif
