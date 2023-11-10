
#ifndef QESTOGROUPS_HH
#define QESTOGROUPS_HH

#include "Options.hh"
#include "Groups.hh"
#include "DataStructures.hh"
#include "LevelInfo.hh"
#include "GroupInversion.hh"
#include "Cache.hh"
#include "Profiler.hh"
#include "MiniSatExt.hh"
#include <iostream>
#include <sstream>
#include <fstream>
#include <utility>
#include <map>
using std::pair;

typedef size_t EncGrp;
typedef std::map<double, vector<vector<EncGrp>>, std::greater<double> > ProbMap;

inline EncGrp encode_sel(size_t gi, bool selected) { return (gi << 1) + (size_t)selected; }
inline bool get_select(EncGrp enc_g) { return enc_g & 01; }
inline size_t get_group(EncGrp enc_g) { return enc_g >> 1; }

extern Profiler profiler;

class QestoGroups {
public: 

QestoGroups(const Options& opt,
            const LevelInfo& levs,
            Groups& groups);
~QestoGroups();
bool solve( const string& skolemName, const string& herbrandName, bool );
lbool solve(size_t confl_budget, std::ofstream&, std::ofstream& );
// Perry
double solve_ssat(const string&, bool);
void output_ssat_sol(bool interrupted = false);


inline size_t get_btcount() const {return tot_bt_count;}

private: 

const Options& opt;
const size_t verb;
const LevelInfo& levs;
size_t tot_bt_count;
Groups& groups;
bool debug;

SATSPC::MiniSatExt* abstractions;

vector<bool> is_encoded;

vector<std::pair<size_t, vector<Lit> > > waitForCert_rules_exists;


vector<unsigned> onsetId;
vector<unsigned> offsetId;
vector<unsigned> definedId;
vector<unsigned> blockId;
unsigned sk_situationId;
unsigned he_situationId;

struct PInfo {
  size_t qlev;
  size_t group;
};


vector<size_t> clauseInfluencedByInstE;

vector<Var> svars; //selection vars
// Hank
vector<vector<PInfo> > infos;
vector<Var> pinVars;
// Perry
vector<Var> tvars; // local selection vars
vector<Var> pvars;
vector<size_t> pv2gr;
vector<Cache> sel_caches;
vector<double> ret_prob;
vector<ProbMap> prob2Learnts;


private: 

inline Var s(size_t quant_level,size_t group_index) const;
inline Var t(size_t quant_level,size_t group_index) const;
inline Var p(size_t quant_level,size_t group_index) const;
inline Var pinVar( size_t quant_level, size_t pin_index) const;


inline bool svalue( size_t gi ) const;
inline bool tvalue( size_t gi ) const;


inline PInfo get_pinfo(size_t qlev,Var p) const;
inline string getSolverName(int lev ) const;


inline QuantifierType group_type(size_t gid) {
  return level_type(groups.qlev(gid)); }


inline QuantifierType level_type(size_t qlev) const {
  assert(qlev<=levs.lev_count());
  return qlev<levs.lev_count() ? levs.level_type(qlev) : UNIVERSAL;
}


void init();
bool analyze(size_t qlev, size_t& bt_qlev, vector<size_t>& conflict_groups, std::ofstream&, std::ofstream& );
bool analyze_univ(size_t qlev, size_t& bt_qlev, vector<size_t>&, std::ofstream&);
bool analyze_exists(size_t qlev,size_t& bt_qlev,vector<size_t>&, std::ofstream&);
void analyze_cert_pin( size_t qlev, size_t bt_qlev, const vector<size_t>& conflict_groups, std::ofstream& file, bool ret );
void analyze_cert( size_t qlev, size_t bt_qlev, const vector<size_t>& conflict_groups, std::ofstream& file, bool skol, bool ret, const vector<size_t>& low_conflict_groups );
void analyze_cert_extract_move( size_t,size_t, const vector<size_t>&, std::ofstream&, bool, bool, vector<vector<Lit> >&, const vector<size_t>& low_conflict_groups );
void analyze_cert( std::ofstream&, bool, const vector<vector<Lit> >&, const std::vector<size_t>& );
size_t find_parent(size_t , size_t );
bool find_sat_lit(size_t, Lit& );
void allocate_selectors();
void inst_e();
void inst_e(size_t group);
void inst_e(const Groups::Node* n, vector<const Groups::Node*>& accum, vector<Groups::Edge>& eaccum);
void init_game_rules();
void init_svars(const GroupInversion* gin);
void init_game_rules_exists( );
bool init_game_rules_exists(size_t group, vector<Lit>& );
void init_game_rules_univ();
void init_game_rules_ssat(); // Perry
void assign_pure_lits(); // Perry
bool find_first_udesel(size_t group, size_t& ql);
bool find_last_sat_elit(size_t group,size_t& ql);
bool is_disselected_by( size_t group, size_t ql );
void encode_group(size_t qlev,size_t g,vector<Lit>& saux, int flag );
void certification_open( std::ofstream& skolemFile, std::ofstream& herbrandFile );
void certification_close( std::ofstream&, bool skol );
int fillChildren( size_t gid, vector<bool>& mark, size_t qlev );


// Perry
double solve_ssat_recur(size_t qlev, std::ofstream& skolemFile);
bool solve_selection(size_t qlev, const vec<Lit>& assump);
void get_parent_selection(size_t qlev, vec<Lit>& parSel);
void get_learnt_clause_e(size_t qlev, vector<EncGrp>& enc_groups, bool isZero);
void get_learnt_clause_r(size_t qlev, vector<EncGrp>& enc_groups, bool isZero);
void add_learnt_clause_e(size_t qlev, vector<EncGrp>& enc_groups, vec<Lit>& assump, bool always_enable);
void add_learnt_clause_r(size_t qlev, vector<EncGrp>& enc_groups, vec<Lit>& assump, bool always_enable);
void partial_assignment_pruning(size_t qlev, vector<EncGrp>& enc_groups, double prob, std::ofstream& skolemFile);
void push_unsat_core(size_t qlev, vector<EncGrp>& enc_groups, vec<Lit>& tmpLits);
int  sort_clause(size_t qlev, vector<EncGrp>& enc_groups) const;
void remove_lits(vector<EncGrp>& enc_groups, bool selected);
bool minimal_selection_e(size_t qlev, size_t param, vec<Lit>& parent_selection);
void mini_unsat_core(size_t qlev);
double get_ret_prob(int qlev) const { return qlev < 0? 0 : ret_prob[qlev]; }
void remove_duplicate_lits(size_t qlev, vec<Lit>& cla);
//void recycle_solver(size_t qlev);

//wwfug, certificate
void ssat_certification_open(std::ofstream& );
void ssat_certification_close(std::ofstream& , double);
void ssat_cert(std::ofstream& skolemFile, vector<EncGrp>& enc_groups, size_t qlev, bool unsat);
void ssat_cert_sel(std::ofstream& skolemFile, vector<EncGrp>& enc_groups, size_t qlev);
void ssat_cert_pin(std::ofstream& skolemFile, vector<EncGrp>& enc_groups, size_t qlev);
// used by clause selection
void ssat_write_strategy(std::ofstream& skolemFile, vector<Lit>& moveLit, vector<EncGrp>& condition_grp, size_t qlev);
// used by cube distribution
void ssat_write_strategy(std::ofstream& skolemFile, vector<pair<Pin*, size_t>>& pin_grp_pair, size_t qlev); 
void ssat_write_condition(std::ofstream& skolemFile, vector<EncGrp>& condition_grp, size_t qlev, bool close);
void ssat_extract_move_from_pin(vector<pair<Pin*, size_t>>& pin_grp_pair, size_t qlev);


// Model counting
std::pair<double, double> calculate_prob(size_t qlev, const ProbMap& prob2learnt, bool countZero = false);
double selection_WMC(size_t qlev, const vector< vector<EncGrp> >& enc_learnts);
void to_dimacs_weighted(FILE * f, size_t qlev, const vector< vector<EncGrp> >& enc_learnts);

// Caching
bool lookup(size_t qlev, const vec<Lit>& parent_selection, double& prob);
bool record(size_t qlev, const vec<Lit>& parent_selection, double& prob);
};

inline Var QestoGroups::p(size_t qlev,size_t group) const{
  assert(qlev);
  assert(qlev<=levs.lev_count());
  assert(groups.qlev(group)==qlev-1);
  assert(group<pvars.size());
  return pvars[group];
}


inline Var QestoGroups::s(size_t qlev,size_t group) const{
  assert(qlev<levs.lev_count());
  assert(groups.qlev(group)==qlev);
  assert(group<svars.size());
  return svars[group];
}

inline Var QestoGroups::t(size_t qlev,size_t group) const{
  assert(qlev<levs.lev_count());
  assert(groups.qlev(group)==qlev);
  assert(group<svars.size());
  return tvars[group];
}


inline bool QestoGroups::svalue( size_t gi ) const {
    size_t lv = groups.qlev( gi );
    assert( abstractions[ lv ].model[ s( lv, gi ) ] != l_Undef );
    return ( abstractions[ lv ].model[ s( lv, gi ) ] == l_True );
}

inline bool QestoGroups::tvalue(size_t gi) const {
    size_t lv = groups.qlev( gi );
    assert( abstractions[ lv ].model[ t( lv, gi ) ] != l_Undef );
    return ( abstractions[ lv ].model[ t( lv, gi ) ] == l_True );
}


inline Var QestoGroups::pinVar(size_t qlev, size_t pid) const {
  assert( qlev < levs.lev_count() );
  assert( groups.getPins()[pid]->qlev == qlev);
  assert( pid < pinVars.size() );
  return pinVars[pid];
}



inline QestoGroups::PInfo QestoGroups::get_pinfo(size_t qlev,Var pv) const {
  //const bool ve=opt.get_varelim()&&level_type(qlev)==UNIVERSAL;
  const bool ve=false;
  assert(ve || pv>levs.maxv());
  const size_t inx=ve ? pv : pv-levs.maxv()-1;
  auto& ql_infos=infos[qlev];
  assert(inx<ql_infos.size());
  return ql_infos[inx];
}


inline string QestoGroups::getSolverName( int lev ) const {  // Hank
    std::ostringstream ss;
    QuantifierType qt = level_type(lev);
    ss << ( ( qt==EXISTENTIAL ) ? "E" : (qt==UNIVERSAL?"A" : "R") );
    ss << lev;
    return ss.str();
}



#endif

