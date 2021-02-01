
#ifndef LEVELINFO_HH
#define LEVELINFO_HH
#include "DataStructures.hh"
class LevelInfo {
public:
  LevelInfo(const Prefix& pref, const vector<double>& prob);
  inline size_t level(Var v) const {
    assert(v>=0);
    const auto vi=(size_t)v;
    assert(vi<vis.size());
    return vis[vi].second;
  }

  inline QuantifierType type(Var v) const {
    assert(v>=0);
    const auto vi=(size_t)v;
    assert(vi<vis.size());
    return vis[vi].first;
  }

  inline size_t lev_count() const {return pref.size();}
  inline Var maxv() const {return mxv;}
  inline size_t qlev(Lit l) const {return level(var(l));}
  inline const VarVector& level_vars(size_t lev) const {
    assert(lev<pref.size());
    return pref[lev].second;
  }
  inline QuantifierType level_type(size_t lev) const {
    assert(lev<pref.size());
    return pref[lev].first;
  }

  inline QuantifierType type(Lit l) const {return type(var(l));}

  inline size_t max_qlev(const vector<Lit>& v) const {
    assert(v.size());
    size_t r=qlev(v[0]);
    for(size_t i=1;i<v.size();++i){
      const auto q=qlev(v[i]);
      if(q>r) r=q;
    }
    return r;
  }

  inline const vector<double>& get_probs() const { return prob; }

private:
  const Prefix pref;
  const vector<double> prob; // Perry
  Var mxv;
  vector<std::pair<QuantifierType, size_t> > vis;
  LevelInfo(const LevelInfo& o) {assert(0);}
};

struct LevCmp {
  const LevelInfo* li;
  LevCmp(const LevelInfo* li):li(li){ }
  inline bool operator () (const Lit x, const Lit& y) const 
  { return li->qlev(x)<li->qlev(y); }
};
#endif

