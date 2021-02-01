/*
 * File:   minisat_aux.hh
 * Author: mikolas
 *
 * Created on October 21, 2010, 2:10 PM
 */
#ifndef MINISAT_AUX_HH
#define	MINISAT_AUX_HH
#include <ostream>
#include "auxiliary.hh"
#include "MiniSatExt.hh"
#include <string>
using std::ostream;
using std::vector;
using std::cout; // Hank
using std::endl; // Hank
using SATSPC::Solver;
using SATSPC::lbool;
using SATSPC::mkLit;
using SATSPC::sign;
using SATSPC::var;
using SATSPC::vec;
using SATSPC::Lit;
using SATSPC::Var;
using SATSPC::lit_Undef;
typedef std::vector<Lit>                      LiteralVector;

ostream& print_model(ostream& out, const vec<lbool>& lv);
ostream& print_model(ostream& out, const vec<lbool>& lv, int l, int r);
ostream& print(ostream& out, const vec<Lit>& lv);
ostream& print(ostream& out, const vector<Lit>& lv);
ostream& print(ostream& out, Lit l);
//ostream& operator << (ostream& outs, Lit lit);
ostream& operator << (ostream& outs, lbool lb);
ostream& operator << (ostream& outs, LiteralVector ls);

inline ostream& operator << (ostream& outs, const vec<Lit>& lv) {
  return print(outs, lv);
}

inline Lit to_lit(Var v, lbool val) { assert( val != l_Undef ); return val==l_True ? mkLit(v) : ~mkLit(v);}

inline Lit to_lit(const vec<lbool>& bv, Var v) {
  return (v<bv.size()) && (bv[v]==l_True) ? mkLit(v) : ~mkLit(v);
}

inline lbool eval(Lit l,const vec<lbool>& vals) {
  // l_True/l_False if vals contains l/-l. Else l_Undef. 
  const Var v=var(l);
  if( v >= vals.size() ) return l_Undef;
  const lbool vv=vals[v];
  if( vv == l_Undef ) return l_Undef;
  return ( vv == l_False ) == ( sign(l) ) ? l_True : l_False;
}

inline void to_lits(const vec<lbool>& bv, vec<Lit>& output, int s, const int e) {
  // Ex. bv={t,f,u,f,t,t,f,u},s=2,e=6. output={ufttf}={3',4,5,6'}
  for (int index = s; index <= e; ++index) {
    if( bv[index]== l_True ) output.push( mkLit( (Var)index) );
    else if( bv[index] == l_False ) output.push( mkLit( (Var)index, true ) );
  }
}

// representative -> AND l_i
inline void
encode_and_pos(SATSPC::MiniSatExt& solver,Lit representative, const vector<Lit>& rhs) {
	assert(0);
  // Ex. representative = 3, rhs = {1,6,8} solver.add(3'+1)(3'+6)(3'+8)
  for(size_t i=0;i<rhs.size();++i)
    solver.addClause(~representative,rhs[i]);
}

// AND l_i -> representative
inline void
encode_and_neg(SATSPC::MiniSatExt& solver,Lit representative, const vector<Lit>& rhs) {
	assert(0);
  // Ex. representative = 3, rhs = {1,6,8} solver.add(1'+6'+8'+3)
  vec<Lit> ls(rhs.size()+1);
  for(size_t i=0;i<rhs.size();++i)
    ls[i]=~rhs[i];
  ls[rhs.size()]=representative;
  cout << "encode_and_neg(" << representative << "," << rhs << ")" << endl;
  solver.addClause_(ls);
}

#ifndef NDEBUG
inline void encode_and(SATSPC::MiniSatExt& solver,Lit representative, Lit lev_representative, const vector<Lit>& rhs, std::string solverName ) {
  // Ex. representative = 3, rhs = {1,6,8} solver.add(3'+1)(3'+6)(3'+8)(1'+6'+8'+3)
  	//assert( rhs.size() > 0 );
  	cout << solverName << ".addClause(";
	if( rhs.empty() ) cout << representative;
	else cout << ~representative << " = ";
    if (rhs[0] != lit_Undef) cout << ~rhs[0];
  	for( size_t i = 1; i < rhs.size(); ++i ) cout << "+" << ~rhs[i];
  	cout << ")" << endl;
#else
inline void encode_and(SATSPC::MiniSatExt& solver,Lit representative, Lit lev_representative, const vector<Lit>& rhs) {
#endif
  /* vec<Lit> ls(rhs.size()+1); */
  /* for(size_t i=0;i<rhs.size();++i) { */
  /*   ls[i]=~rhs[i]; */
  /*   solver.addClause(~representative,rhs[i]); */
  /* } */
  /* ls[rhs.size()]=representative; */
  /* solver.addClause_(ls); */

  // Perry
  // rhs[0] is parent selector
  vec<Lit> ls(rhs.size());
  for(int i=0, n=rhs.size()-1;i<n;++i) {
    ls[i]=~rhs[i+1];
    solver.addClause(~lev_representative,rhs[i+1]);
  }
  ls[rhs.size()-1]=lev_representative;
  solver.addClause_(ls);

  if (rhs[0] != lit_Undef) {
    solver.addClause(~rhs[0], ~lev_representative, representative);
    solver.addClause(rhs[0], ~representative);
  }
  else solver.addClause(~lev_representative, representative);
  solver.addClause(lev_representative, ~representative);
}

class Lit_equal {
public:
  inline bool operator () (const Lit& l1,const Lit& l2) const { return l1==l2; }
};

class Lit_hash {
public:
  inline size_t operator () (const Lit& l) const { return SATSPC::toInt(l); }
};


inline size_t literal_index(Lit l) {
  assert(var(l) > 0);
  const size_t v = (size_t) var(l);
  return sign(l) ? v<<1 : ((v<<1)+1);
}

inline Lit index2literal(size_t l) {
  const bool positive = (l&1);
  const Var  variable = l>>1;
  return positive ? mkLit(variable) : ~mkLit(variable);
}
#endif	/* MINISAT_AUX_HH */
