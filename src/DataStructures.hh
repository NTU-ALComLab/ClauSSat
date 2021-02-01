
#ifndef DATASTRUCTURES_HH
#define DATASTRUCTURES_HH

#include "auxiliary.hh"
#include "LitSet.hh"
#include "VarSet.hh"
#include "VarVector.hh"
#include <vector>

enum    QuantifierType                      {UNIVERSAL=0,EXISTENTIAL=1,RANDOM=2};
typedef std::pair<QuantifierType,VarVector> Quantification;
typedef std::vector<Quantification>         Prefix;
struct QFla {
  Prefix                pref;
  vector<LitSet>        cnf;
  vector<double>        prob;
};

inline std::ostream& operator << (std::ostream& outs, QuantifierType qt) {
  switch(qt) {
    case UNIVERSAL: return outs<<"U";
    case EXISTENTIAL: return outs<<"E";
    case RANDOM: return outs<<"R";
  }
  assert(0);
  return outs;
}

inline std::ostream& operator << (std::ostream& outs, const VarSet& vs) {
  bool f=true;
  outs<<'[';
  FOR_EACH(vi,vs){
    if(!f) outs<<',';
    else f=false;
    outs<<*vi;
  }
  return outs<<']';
}

inline std::ostream& operator << (std::ostream& outs, const Prefix& p) {
  FOR_EACH(qi,p) {
    outs << '[';
    // Perry
    switch (qi->first) {
      case UNIVERSAL: outs << 'a'; break;
      case EXISTENTIAL: outs << 'e'; break;
      case RANDOM: outs << 'r'; break;
    }
    outs << " " << qi->second;
    outs << ']' ;
  }
  return outs;
}

inline std::ostream & operator << (std::ostream& outs, const QFla& f) {
  // Perry
  for (size_t i = 0; i < f.prob.size(); ++i)
    if (f.prob[i] != -1) outs << "(" << i << ", " << f.prob[i] << ") ";
  outs << '\n';

  outs << "[" << f.pref << "]"  << "[" ;
  for(size_t i=0;i<f.cnf.size();++i){
    if (i) outs << ", ";
    outs << f.cnf[i];
  }
  return outs << "]" ;
}

inline Var max(const VarVector& variables) {
  Var max_id = -1;
  FOR_EACH(variable_index, variables) {
    const Var v = *variable_index;
    assert (v>=0);
    if (max_id < v) max_id = v;
  }
  return max_id;
}

inline Var max(const Prefix& pref) {
  Var max_id = -1;
  FOR_EACH(i,pref) {
    max_id=std::max(max_id,max(i->second));
  }
  return max_id;
}

inline QuantifierType neg(QuantifierType q) {
  switch(q) {
    case UNIVERSAL: return EXISTENTIAL;
    case EXISTENTIAL: return UNIVERSAL;
    case RANDOM: assert(0); break;
  }
  assert(0);
  return EXISTENTIAL;
}

inline VarVector append(const VarVector& a, const VarVector& b) {
  if (a.empty()) return b;
  if (b.empty()) return a;
  std::vector<Var> vs;
  FOR_EACH(vi,a) vs.push_back(*vi);
  FOR_EACH(vi,b) vs.push_back(*vi);
  return VarVector(vs);
}

inline VarVector append(const VarVector& a, const std::vector<Var>& b) {
  if (b.size()) {
    std::vector<Var> vs;
    FOR_EACH (vi, a) vs.push_back(*vi);
    FOR_EACH (vi, b) vs.push_back(*vi);
    return VarVector(vs);
  } else {
    return a;
  }
}



#endif

