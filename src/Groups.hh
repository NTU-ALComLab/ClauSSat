
#ifndef GROUPS_NW_25825
#define GROUPS_NW_25825

#include "Options.hh"
#include "DataStructures.hh"
#include "LevelInfo.hh"
#include "LitBitSet.hh"
#include <utility>
#include "MiniSatExt.hh"
#include <iostream>
#include <map>
#include <sstream> // Hank
#include <string>


struct Pin {
	Pin( Lit l, size_t pid, size_t lv ): lit(l), id(pid), qlev(lv), mark(false) {};
	Pin() { assert(0); }
	Lit lit;
	size_t id;
	size_t qlev;
	mutable bool mark;
	std::map<size_t,Pin*> connectedPins;
	inline string getName() const { std::ostringstream o; o << 'p' << id; return o.str(); }
};

class Groups{public:

Groups(const Options& opt, const LevelInfo& levs,const QFla& fla)

:opt(opt)
,levs(levs)
,fla(fla)
,group_count(0)
,grouped_levels(levs.lev_count())


, children_computed(false)


{
  for(size_t index = 0; index<fla.cnf.size(); ++index)
    add_clause(index);
  gen_groups();
  if( opt.get_pin() ) gen_pins();
  
  if( !opt.get_pin() ) cout << "c nGroup = " << group_count << endl;
  else {
    size_t nEdge = 0;
    for( Pin* pP : pins ) nEdge += pP->connectedPins.size();
    cout << "c nGroup/nPin/nEdge = "<< group_count << "/" << pins.size() << "/" << nEdge << endl;
  }
  //std::cerr<<"c groups init "<<read_cpu_time()<<std::endl;
}



inline size_t parent(size_t gid) const;
inline size_t grandparent(size_t gid) const;
inline bool is_end(size_t gid) const;
inline const vector<size_t>& groups(size_t qlev) const;
inline const LitSet& lits(size_t gid) const;
inline size_t qlev(size_t gid) const;
inline const vector<size_t>& get_children(size_t group);
inline void print() const;
inline const vector<Pin*>& getPins();
inline Pin* pin( size_t pid );
inline const vector<Pin*>& getPins( size_t gid ) const;


struct Node;


struct Edge {
  Edge():l(SATSPC::lit_Error),n(NULL),ql(-1) { }
  Edge(Lit l, Node* n, size_t ql):l(l),n(n),ql(ql) { }
  Edge(const Edge& o) : l(o.l),n(o.n),ql(o.ql) { }
  Lit l; Node* n;
  size_t ql;
};


struct Node {
  Node():is_end(false),gid(-1) { }
  bool is_end;
  size_t gid;
  std::vector<Edge> es;
};


inline const LevelInfo& get_levs() const {return levs;}
inline const Node* get_groups() const {return &root;}
inline size_t get_group_count() const {return group_count;}
inline bool is_group(const Node& n) const {return (n.gid)<group_count;}
inline ~Groups() { for( Pin* pP : pins ) { assert( pP != NULL ); delete pP;  } }
inline void setWaitingForBlifWritting( size_t gid, bool skol ) { gr2blifWrittingWaiting[skol][ gid ] = true; }
inline bool isWaitingForBlifWritting( size_t gid, bool skol ) { return gr2blifWrittingWaiting[skol][ gid ]; }
inline string getName( size_t gid ) const { std::ostringstream ss; ss << "g" << gid; return ss.str(); }

inline bool is_select(size_t gid) const { assert(gid<group_count); return gr2s[gid]; }
inline bool is_lev_select(size_t gid) const { assert(gid<group_count); return gr2t[gid]; }
inline void set_select(size_t gid, bool b) { assert(gid<group_count); gr2s[gid] = b; }
inline void set_lev_select(size_t gid, bool b) { assert(gid<group_count); gr2t[gid] = b; }

             private:

const Options& opt;
const LevelInfo& levs;
const QFla& fla;
Node root;
size_t group_count;
vector<LitSet> gr2lits;
vector<bool> gr2end;
vector<size_t> gr2parent;
vector<size_t> gr2qlev;
vector<vector<size_t> >  grouped_levels;
vector<vector<Pin*> > gr2pins;
vector<Pin*> pins; //distributor
vector<vector<bool> > gr2blifWrittingWaiting;
// Perry
vector<bool> gr2s;
vector<bool> gr2t;


bool children_computed;
vector<vector<size_t> > children;

bool add_clause(size_t clause_index);
void del_subtree(Node* n);
void gen_groups();
void gen_groups(Node& n, size_t ql, size_t parent_group, vector<Lit>& accum);
size_t add_group(bool is_end, LitSet ls, size_t ql, size_t parent_group);
void empty_subtree(Node* n,size_t ql);
void gen_child_relation();
void gen_pins();
void connectBetweenPins( const vector<size_t>& pin2gr, const vector<vector<Pin*> >& pinsOfLit );
void mergePins( const vector<size_t>& pin2gr, const vector<vector<Pin*> >& pinsOfLit );

                                        };

const vector<size_t>& Groups::get_children(size_t group) {
  assert(group<group_count);
  if(!children_computed) gen_child_relation();
  assert(children.size()==group_count);
  return children[group];
}


size_t Groups::parent(size_t gid) const{
  assert(gid<group_count);
  return gr2parent[gid];
}

size_t Groups::grandparent(size_t gid) const{
  assert(gid<group_count);
  assert(gr2parent[gid]<group_count);
  return gr2parent[gr2parent[gid]];
}


const vector<size_t>& Groups::groups(size_t qlev) const {
  assert(qlev<levs.lev_count());
  return grouped_levels[qlev];
}


bool Groups::is_end(size_t gid) const {
  assert(gid<group_count);
  return gr2end[gid];
}


const LitSet& Groups::lits(size_t gid) const {
  assert(gid<group_count);
  return gr2lits[gid];
}


size_t Groups::qlev(size_t gid) const {
  assert(gid<group_count);
  return gr2qlev[gid];
}


const vector<Pin*>& Groups::getPins() {
	return pins;
}


Pin* Groups::pin( size_t pid ) {
	assert( pid < pins.size() && pins[pid]->id == pid );
	return pins[pid];
}


const vector<Pin*>& Groups::getPins( size_t gid ) const {
	return gr2pins[ gid ];
}





void Groups::print() const {
	return;
	using std::cout;
	using std::endl;
	
	for( size_t qlev = 0; qlev < levs.lev_count(); ++qlev ) {
		cout << "lev " << qlev << " : " << groups( qlev ) << endl;
	}

	cout << "gid\tqlev\tparent_gid\tlits\tis_end" << endl; 
	for( size_t gid = 0; gid < group_count; ++gid ) {
		#ifndef DNDEBUG
		if( parent(gid) == gid ) assert( qlev(gid) == 0 );
		if( qlev(gid) == 0 ) assert( parent(gid) == gid ); 
		if( qlev(gid) != 0 ) assert( qlev( parent(gid) ) == qlev(gid) - 1 );
		#endif
		cout << gid << "\t" << qlev(gid) << "\t" << parent(gid) << "\t" << lits(gid) << "\t"; 
		if( is_end(gid) ) cout << "End";
		cout << endl;
	}
}




#endif

