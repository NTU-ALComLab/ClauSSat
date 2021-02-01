
#include "Groups.hh"
#include "mtl/Sort.h"
using SATSPC::lit_Error;
using SATSPC::lit_Undef;

bool Groups::add_clause(size_t clause_index) {
  Node *node = &root;
  vec<Lit> cls;
  FOR_EACH(li,fla.cnf[clause_index]) cls.push(*li);
  LevCmp lc(&levs);
  SATSPC::sort(cls,lc);
  bool is_new=false;
  size_t next_lev=0;
  int i=0;
  const auto clsz=cls.size();
  Node *last_real_node=NULL;
  size_t last_real_lev=-1;
  while(next_lev<=levs.lev_count()){
    if(node->is_end){//subsumtion
      assert(!is_new);
      return false;
    }
    Lit l=lit_Error;
    if((i>=clsz)||(next_lev<levs.qlev(cls[i]))) {
      ++next_lev;//insert fake lit for next lev
      if(next_lev==(levs.lev_count()+1)) break;
      l=lit_Undef;
    }else{
      l=cls[i++];
      next_lev=levs.qlev(l)+1;
    }
    auto& es=node->es;
    const auto sz=es.size();
    size_t j=0;
    while(j<sz&&es[j].l!=l) ++j;//TODO:could be faster by binary
    if(j==sz) {
      is_new=true;
      assert(next_lev>0);
      es.push_back(Edge(l,new Node(),next_lev-1));
    }
    assert(es[j].l==l);
    assert(es[j].ql==(next_lev-1));
    node=es[j].n;
    if(l!=lit_Undef){
      last_real_node=node;
      assert(next_lev>0);
      last_real_lev=next_lev-1;
    }
  }
  if(last_real_node!=NULL) {
    last_real_node->is_end=true;
    empty_subtree(last_real_node,last_real_lev);//remove subsumed
  }
  return is_new;
}


void Groups::gen_groups(){
  if(fla.cnf.empty())return;
  vector<Lit> accum;
  gen_groups(root,0,-1,accum);
  // Perry
  gr2s.resize(group_count, 1);
  gr2t.resize(group_count, 1);
}


void Groups::gen_groups( Node& n, size_t ql, size_t parent_group, vector<Lit>& accum ) {
  assert(ql<levs.lev_count());
  bool new_group=n.es.empty();
  FOR_EACH(i,n.es) {
    assert(i->ql==(ql+1)||i->ql==ql);
    if(i->ql!=ql){
      new_group=true;
      break;
    }
  }
  n.gid=new_group ? add_group(n.is_end,LitSet(accum),ql,parent_group) : -1;
  vector<Lit> new_accum;
  FOR_EACH(i,n.es) {
    if(i->ql!=ql){
      assert(i->ql==ql+1);
      assert(new_group);
      new_accum.clear();
      if(i->l!=lit_Undef)new_accum.push_back(i->l);
      gen_groups(*(i->n),ql+1,n.gid,new_accum);
    } else {
      assert(i->ql==ql);
      if(i->l!=lit_Undef)accum.push_back(i->l);
      gen_groups(*(i->n),ql,parent_group,accum);
      if(i->l!=lit_Undef)accum.pop_back();
     }
  }
}


size_t Groups::add_group(bool is_end, LitSet ls, size_t ql, size_t parent_group){
  const size_t gid=group_count++;
  gr2end.resize(gid+1);
  gr2lits.resize(gid+1);
  gr2parent.resize(gid+1);
  gr2qlev.resize(gid+1);
  gr2end[gid]=is_end;
  gr2lits[gid]=ls;
  gr2parent[gid]=ql?parent_group:gid;
  gr2qlev[gid]=ql;
  grouped_levels[ql].push_back(gid);
  gr2pins.resize( gid+1 );
  gr2blifWrittingWaiting.resize(2);
  gr2blifWrittingWaiting[0].resize( gid+1, false );
  gr2blifWrittingWaiting[1].resize( gid+1, false );
  if( opt.get_verbose()>5){
    std::cerr<<"-----"<<std::endl;
    std::cerr<<"gr: "<<gid<<std::endl;
    std::cerr<<"ls: ["<<gr2lits[gid]<<"]\n";
    std::cerr<<"ql: "<<gr2qlev[gid]<<std::endl;
    std::cerr<<"par: "<<gr2parent[gid]<<std::endl;
    std::cerr<<"-----"<<std::endl;
  }
  return gid;
}


void Groups::empty_subtree(Node* n,size_t ql) {
  auto& es=n->es;
  const auto ml=levs.lev_count()-1;
  assert(es.size()||ql==ml);
  if(ql==ml) {
    del_subtree(n);
    return;
  }
  for(size_t i=1;i<es.size();++i) {
    del_subtree(es[i].n);
    delete es[i].n;
  }
  while(es.size()>1) es.pop_back();
  es[0].l=lit_Undef;
  es[0].ql=ql+1;
  empty_subtree(es[0].n,ql+1);
}


void Groups::del_subtree(Node* n) {
  FOR_EACH(i,n->es) {
    del_subtree(i->n);
    delete i->n;
  }
  n->es.clear();
}


void Groups::gen_child_relation(){
  assert(!children_computed);
  children_computed=true;
  children.resize(group_count);
  for(size_t group=0; group<group_count; ++group) {
     const auto p=parent(group);
     if(p==group) continue;
     children[p].push_back(group);
  }
}



void Groups::gen_pins() {
	assert( pins.empty() && group_count > 0 );
	vector<size_t> pin2gr;
	for( size_t gid = 0; gid < group_count; ++gid ) {
		assert( gr2pins[gid].empty() );
  		if( levs.level_type( qlev(gid) ) != EXISTENTIAL ) continue; 
		if( lits( gid ).empty() ) continue;
		for( const Lit& lit : lits( gid ) ) {
			Pin* pPin = new Pin( lit, pins.size(), qlev(gid) );
			pins.push_back( pPin );
			pin2gr.push_back( gid );
			gr2pins[ gid ].push_back( pPin ); 
			//cout << "Pid/gid/lit = " << pPin->id << "/" << pin2gr[pPin->id] << "/" << lit << endl; 
		}
	}
	assert( pins.size() == pin2gr.size() );
	vector<vector<Pin*> > pinsOfLit;
	for( size_t p = 0; p < pins.size(); ++p ) {
		Pin* pPin = pins[p];
		unsigned x = pPin->lit.x;
		if( x >= pinsOfLit.size()  ) pinsOfLit.resize( ( ( x+2 ) / 2 )*2 );
		pinsOfLit[x].push_back( pPin );
	}
	//cout << "PinOfLit.size = " << pinsOfLit.size() << endl;
	//for( unsigned x = 2; x < pinsOfLit.size(); ++x ) cout << "x=" << x << ".pins.size() =  " << pinsOfLit[x].size() << endl;
	// x = 2*var+sign;	1.x=2,	1'.x=3,
	connectBetweenPins( pin2gr, pinsOfLit );
	mergePins( pin2gr, pinsOfLit );

	for( size_t i = 0; i < pins.size(); ++i ) pins[i]->id = i; 
}


namespace CONNECT_BETWEEN_PINS {
bool overlap( const LitSet& lits0, const LitSet& lits1 ) {
	if( lits0.empty() || lits1.empty() ) return true;
	for( size_t i = 0; i < lits0.size() - 1; ++i ) assert( lits0[i] < lits0[i+1] ); 	
	for( size_t i = 0; i < lits1.size() - 1; ++i ) assert( lits1[i] < lits1[i+1] ); 	
	size_t a = 0, b = 0;
	while( true ) {
		#define lit0 lits0[a]
		#define lit1 lits1[b]
		if( lit0 == ~lit1 ) {
			return false;
		}
		if( lit0 < lit1 ) {
			++a;
			if( a == lits0.size() ) break;
		}
		else {
			++b;
			if( b == lits1.size() ) break;
		}
		#undef lit0
		#undef lit1
	}
	return true;
}
bool overlap( const vector<LitSet>& gr2lits, const vector<size_t>& gr2parent, size_t g1, size_t g2 ) {
	while( 1 ) {
		if( g1 == gr2parent[ g1 ] ) { 
			assert( g2 == gr2parent[ g2 ] ); 
			return true;
		}
		g1 = gr2parent[ g1 ];
		g2 = gr2parent[ g2 ];
		if( !overlap( gr2lits[g1], gr2lits[g2] ) ) {
			return false;
		}
	}
	return true;
}
}


void Groups::connectBetweenPins( const vector<size_t>& pin2gr, const vector<vector<Pin*> >& pinsOfLit ) {
	vector<size_t> alwaysSatisfied;
	using namespace CONNECT_BETWEEN_PINS;
	for( unsigned posX = 2; posX + 1 < pinsOfLit.size(); posX += 2 ) {
		//Var var = Var( posX / 2 );
		//cout << "doing " << var << endl;
		const unsigned negX = posX + 1;
		const vector<Pin*>& posVec = pinsOfLit[ posX ];
		const vector<Pin*>& negVec = pinsOfLit[ negX ];
		for( unsigned pos = 0; pos < posVec.size(); ++pos ) { 
			Pin* pPosPin = posVec[ pos ];
			const size_t posGroup = pin2gr[ pPosPin->id ];
			for( unsigned neg = 0; neg < negVec.size(); ++neg ) { 
				Pin* pNegPin = negVec[ neg ];
				const size_t negGroup = pin2gr[ pNegPin->id ];
				//cout << pPosPin->id << " and " << pNegPin->id << " has conflicting literal." << endl;
				
				if( posGroup == negGroup ) {
					static bool warned = false;
					if( !warned ) {
						cout << "Warning: pos and neg exist lit in same clause. For example( a1 + e1 + e1' + e2)" << endl;
						warned = true;
					}
					alwaysSatisfied.push_back( posGroup );
					continue;
				}
				if( overlap( gr2lits, gr2parent, posGroup, negGroup ) ) {
					//cout << "new a " << var << "edge" << endl;
					pPosPin->connectedPins.insert( std::pair<size_t, Pin*>( negGroup, pNegPin ) );
					pNegPin->connectedPins.insert( std::pair<size_t, Pin*>( posGroup, pPosPin ) );
				}
			}
		}
	}
	
	if( !alwaysSatisfied.empty() ) cout << "groups always satisfied(gid):" << alwaysSatisfied << endl;
	for( size_t gid : alwaysSatisfied ) {
		for( Pin* pFromPin : gr2pins[gid] ) {
			for( std::pair<size_t,Pin*> to : pFromPin->connectedPins ) to.second->connectedPins.erase( gid );
			pFromPin->connectedPins.clear();
		}
	}
}


void Groups::mergePins( const vector<size_t>& pin2gr, const vector<vector<Pin*> >& pinsOfLit ) {
	using std::map;
	map<size_t, Pin*>::const_iterator it;
	#ifndef NDEBUG
	for( Pin* pP : pins ) assert( pP->mark == false );
	cout << "before merging\t#P = " << pins.size() << endl;
	//for( Pin* pP : pins ) cout << pP->id << ",";
	//cout << endl;
	//for( size_t gid : pin2gr ) cout << gid << ",";
	//cout << endl;
	//for( vector<Pin*> pins : gr2pins ) {
	//	for( Pin* pP : pins ) cout << pP->id << ","; 
	//	cout << endl;
	//}
	//cout << endl;
	#endif
	for( const vector<Pin*>& fromPins : pinsOfLit ) {
		if( fromPins.empty() ) continue;
		for( int fp0 = int(fromPins.size()) - 1; fp0 >= 1; --fp0 ) {
			Pin* pFromPin0 = fromPins[fp0];
			const map<size_t, Pin* >& toPins0 = pFromPin0->connectedPins;
			for( size_t fp1 = 0; (int)fp1 < fp0; ++fp1 ) { 
				Pin* pFromPin1 = fromPins[fp1];
				const map<size_t, Pin* >& toPins1 = pFromPin1->connectedPins; 
				if( toPins0 == toPins1 ) {
					// keep pFromPin1, remove pFromPin0
					//cout << "keep " << pFromPin1->id << " and kill " << pFromPin0->id << endl;
					size_t groupFrom0 = pin2gr[pFromPin0->id];
					for( it = toPins0.begin(); it != toPins0.end(); ++it ) it->second->connectedPins.erase( groupFrom0 );
					//cout << "sz = " << gr2pins[ groupFrom0 ].size() << endl;
					for( size_t i = 0; i < gr2pins[ groupFrom0 ].size(); ++i ) {
						//cout << "id = " << gr2pins[ groupFrom0 ][i]->id << endl;
						if( gr2pins[ groupFrom0 ][i] == pFromPin0 ) { gr2pins[ groupFrom0 ][i] = pFromPin1; break; }
					}
					pFromPin0->mark = true;
					break;
				}
			}
		}
	}
	for( Pin*& pP : pins ) {
		if( pP->mark ) {
			delete pP;
			pP = NULL;
		}
	}
	size_t newIt = 0;
	for( size_t oriIt = 0; oriIt < pins.size(); ++oriIt ) {
		if( pins[oriIt] == NULL ) continue;
		pins[ newIt ] = pins[ oriIt ];
		++newIt;
	}
	size_t nPop = pins.size() - newIt;
	for( size_t i = 0; i < nPop; ++i ) pins.pop_back();
}



