#include "QestoGroups.hh"
#include "ClausesInversion.hh"
#include "LitBitSet.hh"
#include <algorithm>
#include <set>
using std::max;
using std::min;
using std::make_pair;
using std::cout;
using std::endl;
using SATSPC::vec;
using SATSPC::Lit;
using SATSPC::lit_Undef;
using std::pair;
using std::map;
using std::ofstream;
using std::ostringstream;
using std::set;
using std::get;

extern Profiler profiler;

QestoGroups::QestoGroups(const Options& opt,
                         const LevelInfo& levs,
                         Groups& groups)
: opt(opt)
, verb(opt.get_verbose())
, levs(levs)
, tot_bt_count(0)
, groups(groups)
#ifndef NDEBUG
, debug(true)
#else
, debug(false)
#endif

, abstractions(new SATSPC::MiniSatExt[levs.lev_count()+1])

,is_encoded(groups.get_group_count(),false)

,onsetId( levs.maxv() + 1, -1 )
,offsetId( levs.maxv() + 1, -1 )
,definedId( levs.lev_count(), 0 )
,blockId( levs.lev_count(), 0)
,sk_situationId( -1 )
,he_situationId( -1 )

,infos(levs.lev_count()+1)

{
  assert(levs.lev_count());
  assert( opt.get_ssat() || level_type(levs.lev_count()-1)==EXISTENTIAL);
  if( !opt.get_ssat() && level_type(levs.lev_count()-1) != EXISTENTIAL ) 
  	cout << "Error: The last level is universal." << endl;
  init();
  if(verb>5){
    for(size_t ul=0;ul<levs.lev_count();++ul){
      const auto& gs=groups.groups(ul);
      size_t c=0;
      FOR_EACH(gi,gs) if(groups.lits(*gi).empty())++c;
      std::cerr<<"gs@l"<<ul<<":"<<gs.size()<<" e:"<<c<<std::endl;
    }
  }
}

void QestoGroups::init(){
	allocate_selectors();
	init_game_rules();
	init_svars( NULL );
    //assign_pure_lits();
	if( !opt.get_ssat() && opt.get_ex_inst() ) { inst_e(); }
    if( opt.get_ssat() ) {
        sel_caches.resize(levs.lev_count());
        ret_prob.resize(levs.lev_count(), 0);
        prob2Learnts.resize(levs.lev_count());
        profiler.init(levs.lev_count());
    }
}

void QestoGroups::init_svars(const GroupInversion* gin) {
	vector<Lit> saux;
	for(size_t qlev=0;qlev<levs.lev_count();++qlev){
		if( opt.get_lazy() && level_type(qlev)==EXISTENTIAL ) continue;
    	const auto& gs=groups.groups(qlev);
    	FOR_EACH(gi,gs) encode_group(qlev,*gi,saux, 2 );
  	}
}

void QestoGroups::encode_group(size_t qlev,size_t g,vector<Lit>& saux, int flag = 0 ){
	if(is_encoded[g]) return;
	switch(flag) {
		//init_game_rules_exists 
		// Only for exist node who has no exist child
		case 1: assert(level_type(qlev)==EXISTENTIAL); break;
		//init_svars
		case 2: break;
		default : assert(0);
	}
	is_encoded[g]=true;
	if(verb>5)std::cerr<<"encode_group "<<g<<"@"<<qlev<<std::endl;
	saux.clear();
	/* if(qlev) saux.push_back(mkLit(p(qlev,groups.parent(g)))); */
	// S_k = S_(k-1) & (l_i')
	saux.push_back(qlev? mkLit(p(qlev,groups.parent(g))) : lit_Undef);
	if( opt.get_pin() && level_type(qlev) == EXISTENTIAL ) {
		const vector<Pin*>  pins = groups.getPins( g ); 
		for( Pin* pP : pins ) saux.push_back( mkLit( pinVar( qlev, pP->id ), true ) );
	}
	else {
		const LitSet& ls=groups.lits(g);
		FOR_EACH(li,ls) saux.push_back(~(*li));
	}
	const Lit sel_lit=mkLit(s(qlev,g));
    const Lit lev_sel_lit=mkLit(t(qlev,g));
	#ifndef NDEBUG
	encode_and(abstractions[qlev],sel_lit,lev_sel_lit,saux, getSolverName(qlev) );
	#else
	encode_and(abstractions[qlev],sel_lit,lev_sel_lit,saux);
	#endif
	// Ex. sel_lit = 3, saux = {1,6,8} solver.add(3'+1)(3'+6)(3'+8)(1'+6'+8'+3) 
	// 						 = ( 3 == 1&6&8 ) = ( !this == !parent.top + {lits} )
}

void QestoGroups::init_game_rules(){
    if (opt.get_ssat())
        init_game_rules_ssat();
    else {
        init_game_rules_univ();
        init_game_rules_exists();
    }

/*
	for( size_t lv = 0; lv < levs.lev_count(); ++lv ) {
		for( size_t gid : groups.groups(lv) ) {
			cout << gid << ":";
			for( Lit lit : groups.lits( gid ) ) cout << lit << ',';
			if( groups.is_end( gid ) ) cout << "[end]";
			cout << endl;
		}
	}
*/
	if( opt.get_pin() ) {
		std::map<size_t,Pin*>::const_iterator connectedIter;
		vec<Lit> clause;
		for( size_t pid = 0; pid < groups.getPins().size(); ++pid ) {
			Pin* p0 = groups.pin(pid);
			for( connectedIter  = p0->connectedPins.begin(); 
				 connectedIter != p0->connectedPins.end(); ++connectedIter ) {
				Pin* p1 = connectedIter->second;
				if( p0->id > p1->id ) continue;
				size_t qlev = p1->qlev;
				clause.clear();
				clause.push( mkLit( pinVar( qlev, p0->id ), true ) );
				clause.push( mkLit( pinVar( qlev, p1->id ), true ) );
				if( debug ) cout << getSolverName(qlev) << ".addClause" << clause << endl;
				abstractions[ qlev ].addClause_( clause );
			}
		}
	}
}

void QestoGroups::init_game_rules_univ() {
  //Hank: Leave at least one for exist player.	
  vec<Lit> aux;
  const auto sz=levs.lev_count();
  for(size_t qlev=0;qlev<sz;++qlev){
    if(level_type(qlev)==EXISTENTIAL) continue;
    vector<size_t> gs=groups.groups(qlev);
    aux.clear();
    FOR_EACH(gi,gs) aux.push(mkLit(s(qlev,*gi)));
	if( debug ) cout << getSolverName(qlev) << ".addClause" << aux << endl; 
	abstractions[qlev].addClause_(aux);
  }
  //dummy level
  vector<size_t> gs=groups.groups(sz-1);
  aux.clear();
  FOR_EACH(gi,gs) aux.push(mkLit(p(sz,*gi)));
  if( debug ) cout << getSolverName(sz) << ".addClause" << aux << endl;
  abstractions[sz].addClause_(aux);
}

void QestoGroups::init_game_rules_exists(){
  FOR_EACH(g,groups.groups(0)) {
      vector<Lit> universalLits;
	  init_game_rules_exists( *g, universalLits );
  }
}

bool QestoGroups::init_game_rules_exists(size_t group, vector<Lit>& universalLits ){
	const vector< size_t >& children = groups.get_children(group);
	if( groups.is_end( group ) ) assert( universalLits.empty() );
  	
	bool all_universal;

	bool anyChildHasNoExiLit = false;
	for( size_t gi : children ) {
		vector<Lit> ul;
		if( init_game_rules_exists( gi, ul ) ) {
			if( opt.get_cert() && ( !anyChildHasNoExiLit || universalLits.size() > ul.size() ) ) 
				universalLits = ul; // record	
			anyChildHasNoExiLit = true; 
		}
	}
	all_universal = children.empty() || anyChildHasNoExiLit;

  	const auto qlev=groups.qlev(group);
  	const auto qt=level_type(qlev);
	vector<Lit> saux;
  	if(all_universal && qt == EXISTENTIAL ) {
		vec<Lit> unitClause(1);
		unitClause[0] = ~mkLit(s(qlev,group));
		if( debug ) cout << getSolverName(qlev) << ".addClause" << unitClause << endl;
    	abstractions[qlev].addClause( unitClause );
    	encode_group(qlev,group,saux, 1);
		if( opt.get_cert() ) {
			//group = C^l_i
			//In situation $-C^{<=l}_i$, has universal move $-C^{>l}_i$. 
			if( !universalLits.empty() )
				waitForCert_rules_exists.push_back( pair<size_t,vector<Lit> >( group, universalLits ) );
		}
  	}
	all_universal &= (qt==UNIVERSAL) || groups.lits(group).empty();
	if( opt.get_cert() && all_universal && qt==UNIVERSAL ) 
		for( Lit lit : groups.lits(group) ) universalLits.push_back(~lit);
  	return all_universal;
}

// A clause must be deselected at the highest level of its literals
void QestoGroups::init_game_rules_ssat() {
    for (size_t qlev = 0; qlev < levs.lev_count(); ++qlev) {
        for (size_t gi : groups.groups(qlev))
            if (groups.is_end(gi))
                abstractions[qlev].addClause( ~mkLit(s(qlev, gi)) );
    }
}

void QestoGroups::assign_pure_lits() {
    if (debug) cout << "Assign pure lits start\n";
    vec<Lit> unitClause(1);
    if (opt.get_pin()) {
        const vector<Pin*>& pins = groups.getPins();
        for (Pin* pP : pins) {
            if (pP->connectedPins.empty()) {
                unitClause[0] = mkLit(pinVar(pP->qlev, pP->id), false);
                abstractions[pP->qlev].addClause(unitClause);
                if (debug) cout << getSolverName(pP->qlev) << ".addClause" << unitClause << endl;
            }
        }
    }
    else {
        vector<bool> pos(levs.maxv()+1);
        vector<bool> neg(levs.maxv()+1);
        for (size_t lv = 0; lv < levs.lev_count(); ++lv) {
            if (levs.level_type(lv) != EXISTENTIAL) continue;
            const vector<size_t>& gps = groups.groups(lv);
            for (size_t gi : gps)
                FOR_EACH(li, groups.lits(gi))
                    sign(*li)? neg[var(*li)] = 1 : pos[var(*li)] = 1;
        }
        for (size_t v = 1; v < pos.size(); ++v)
            if (pos[v] != neg[v]) {
                unitClause[0] = mkLit(v, neg[v]);
                abstractions[levs.level(v)].addClause(unitClause);
                if (debug) cout << getSolverName(levs.level(v)) << ".addClause" << unitClause << endl;
            }
    }

    if (opt.get_ssat()) {
        const vector<double>& probs = levs.get_probs();
        for (Var v = 1; v < levs.maxv()+1; ++v) {
            if (probs[v] == 1.0 || probs[v] == 0.0) {
                unitClause[0] = mkLit(v, probs[v] == 0.0);
                abstractions[levs.level(v)].addClause(unitClause);
                if (debug) cout << getSolverName(levs.level(v)) << ".addClause" << unitClause << endl;
            }
        }
    }
    if (debug) cout << "Assign pure lits end\n";
}

QestoGroups::~QestoGroups() {
	delete [] abstractions;
}

// solving

lbool QestoGroups::solve(size_t confl_budget, ofstream& skolemFile, ofstream& herbrandFile ) {
	//cout << "QestoGroups::solve(cb) :" << endl;
	// callee
	size_t qlev=0;
	vector<size_t> conflict_groups;
	vec<Lit> conflict_clause;
	vec<Lit> decisions;
	vector<Lit> saux;

	#define solveBecausePropagate false // new assump
	#define solveBecauseConflict true //same assump again
	bool solveBecause = solveBecausePropagate;

	while( true ) {
    	//if(verb>5)std::cerr<<"svals "<<svals<<std::endl;
    	assert( qlev <= levs.lev_count() );
		if(opt.get_lazy()&&level_type(qlev)==EXISTENTIAL) {
			const vector<size_t>& gs=groups.groups(qlev);
			FOR_EACH(gi,gs) {
				const size_t g=*gi;
				const bool psel = !qlev || svalue(groups.parent(g));
				if(psel) encode_group(qlev,g,saux);
			}
		}
    	
		decisions.clear();
		if( qlev > 0 ) {
			if( opt.get_strong_pri() && level_type( qlev ) == EXISTENTIAL ) {
				for( size_t gi : groups.groups( qlev - 1 ) ) {
    				if( svalue(gi) ) 
						decisions.push( mkLit( p( qlev, gi ) ) );
					else 
						for( size_t gc : groups.get_children( gi ) ) 
							decisions.push( ~mkLit( s( qlev, gc ) ) );
				}
			}
			else {
				for( size_t gi : groups.groups( qlev - 1 ) ) {
					// parent selection as assumption
    				decisions.push( svalue(gi) ? mkLit( p(qlev,gi)) : ~mkLit( p( qlev, gi ) ) );
				}
			}
		}
		
		if( qlev > 0 && level_type( qlev ) == EXISTENTIAL && solveBecause == solveBecausePropagate ) {
			if( opt.get_weak_pri() ) {
				for( size_t gid : groups.groups( qlev ) ) {
					const size_t pid=groups.parent(gid);
					//assert(svals[pid]==(abstractions[ groups.qlev( pid ) ].model[s(groups.qlev(pid),pid)]==l_True));
    				if( svalue(pid) ) {
						abstractions[qlev].setDecisionPriority( s(qlev,gid), 2 );
						//if( debug ) cout << getSolverName(qlev) <<".setPriority(" << s(qlev,gid) << ")=1" << endl;
					}
					else {
						abstractions[qlev].setDecisionPriority( s(qlev,gid), 1 );
						//if( debug ) cout << getSolverName(qlev) <<".setPriority(" << s(qlev,gid) << ")=0" << endl;
					}
				}
				abstractions[qlev].waitForRebuildingOrderHeap();
			}
			else if( opt.get_strong_pri() ) {
				// pin's priority always = 0
				// don't care: s( diselected ) and p( selected )
				// care : p( diselected ) and s( selected )
				const int BIGGEST_PRI = INT_MAX - 32;
				const int SECOND_PRI = BIGGEST_PRI / 2;
				for( size_t gid : groups.groups( qlev ) ) {
					const size_t pid=groups.parent(gid);
    				if( svalue(pid) ) {
						const Var v = s(qlev,gid);
						const int pri = BIGGEST_PRI;
						abstractions[qlev].setDecisionPriority( v, pri );
						//if( debug ) cout << getSolverName(qlev) <<".setPriority(" << v << ")=" << pri << endl;
					}
					else { // gid is diselected.
						assert( svalue(pid) == false );
						assert( qlev-1 == groups.qlev(pid) );
						assert( abstractions[ qlev-1 ].model[ s( qlev-1, pid ) ] == l_False );
						
						const Var v = p( qlev, pid );
						size_t sat_ql;
						if( find_last_sat_elit( pid, sat_ql) ) {
							const int pri = 1;
							abstractions[qlev].setDecisionPriority( v, pri );
							//if( debug ) cout << getSolverName(qlev) <<".setPriority(" << v << ")=" << pri << endl;
						} else {
							if( !find_first_udesel( pid, sat_ql ) ) assert(0);
							const int pri =SECOND_PRI + (int)sat_ql + 1;
							//const int pri = 2;
							abstractions[qlev].setDecisionPriority( v, pri );
							//if( debug ) cout << getSolverName(qlev) <<".setPriority(" << v << ")=" << pri << endl;
						}
						
					}
				}			
				abstractions[qlev].waitForRebuildingOrderHeap();
			}
		}
    	const bool sat = abstractions[qlev].solve( decisions ); // parent selection as assumption
		//TODO Last level
		if(debug) cout << getSolverName( qlev ) << ".solve" << decisions;
		if(debug) cout << ( sat ? " = SAT":" = UNSAT" )<< endl;
    	if( sat ) {
      		
			//for( size_t gid : groups.groups( qlev ) ) cout << ( svalue( gid ) ? 'O' : 'X' );
			//cout << endl;

			if( debug ) {
				//print_model( cout << getSolverName(qlev) <<".model = ",abstractions[qlev].model) << endl;
				cout << getSolverName(qlev) << ".model = ";
				if( opt.get_pin() && level_type(qlev) == EXISTENTIAL ) {
	        		for( size_t gi : groups.groups( qlev ) ) {
						for( Pin* pP : groups.getPins( gi ) ) {
							const Var vP = pinVar( qlev, pP->id );
							if( eval( mkLit( vP ) ,abstractions[ qlev ].model ) == l_True) 
								cout << 'p' << pP->id << " * ";
						}
					}
				} else {
					for( const Var& v : levs.level_vars( qlev ) ) {
						assert( abstractions[ qlev ].model[v] != l_Undef );
						cout << mkLit( v, abstractions[ qlev ].model[v] == l_False ) << " * ";
					}
				}
				cout << endl;
			}
			assert(qlev<levs.lev_count());
			decisions.clear();
			++qlev;
			solveBecause = solveBecausePropagate;
    	} else {//attempt conflict resolution
      		
			++tot_bt_count;
			conflict_groups.clear();
			size_t bt_qlev=-1;
			const bool resolved = analyze( qlev, bt_qlev, conflict_groups, skolemFile, herbrandFile );
			if( !resolved ) { //formula true iff universal lost
  				return level_type(qlev)==UNIVERSAL ? l_True : l_False;
			} else {
  				assert(qlev>bt_qlev);
  				conflict_clause.clear();
  				FOR_EACH( gi, conflict_groups ) {
    				const auto g=*gi;
    				const QuantifierType gt = group_type(g);
    				//encode_group( bt_qlev, g, saux, 3 ); //TODO?

    				conflict_clause.push( mkLit( s( bt_qlev, g ), gt == EXISTENTIAL ) );
  				}
  				if(verb>3)
					std::cerr<<"cc:"<<conflict_groups<<std::endl;
  				if(verb>2)
					std::cerr<<"cc sz:"<<conflict_groups.size()<<std::endl;
				if( debug ) cout << getSolverName(bt_qlev) << ".addClause" << conflict_clause << endl;
  				abstractions[bt_qlev].addClause_(conflict_clause);
				qlev=bt_qlev;
			}
			solveBecause = solveBecauseConflict;
    	}
  	}
	#undef solveBecausePropagate
	#undef solveBecauseConflict
	
	if(verb>1)std::cerr<<"restart "<<tot_bt_count<<std::endl;
  	return l_Undef;
}

bool QestoGroups::solve( const string& skolemName, const string& herbrandName, bool alreadyUnsat ) {
	//caller
	if( alreadyUnsat ) cout << "Contains an empty clause in cnf." << endl;
	ofstream skolemFile, herbrandFile;
	// fuck you 
	if( 0 && opt.get_cert() && opt.get_pin() ) {
		for( size_t qlev = 0; qlev < levs.lev_count(); ++qlev ) {
			if( level_type( qlev ) == UNIVERSAL ) continue;
			vector<size_t> gs = groups.groups(qlev);
			for( size_t gi : gs ) {
				cout << 'g' << gi << "(";
				for( const Lit li : groups.lits( gi ) ) 
					cout << li << "+";	
				cout << ")@E" << qlev << "{";
				for( const Pin* pP : groups.getPins( gi ) ) 
					cout << pP->getName() << "(" << pP->lit << "),";
				cout << endl;
			}
		}
	}
	if( opt.get_cert() ) {
		//cout << "GetCert!!" << endl;
		skolemFile.open( skolemName.c_str(), ofstream::out | std::ofstream::trunc );
		herbrandFile.open( herbrandName.c_str(), ofstream::out | std::ofstream::trunc );
		certification_open( skolemFile, herbrandFile );
	}
	int curr_restarts = 0;
	lbool status=l_Undef;
	const double restart_inc=1.5;
	const int restart_first=100;
	while(status==l_Undef){
		if( alreadyUnsat ) {
			status == l_False;
			break;
		}
		const double rest_base = luby(restart_inc, curr_restarts);
		status = solve(rest_base * restart_first, skolemFile, herbrandFile );
		curr_restarts++;
	}
	assert( status != l_Undef );

	if( opt.get_cert() ) {
		bool skol = status==l_True;
		if( skol && herbrandFile.is_open() ) 
			herbrandFile.close();
		else if( !skol && skolemFile.is_open() ) 
			skolemFile.close();

		if( skol ) if( remove( herbrandName.c_str() ) ) 
			cout << "Warning deletion!" << endl;
		if( !skol ) if( remove( skolemName.c_str() ) ) 
			cout << "Warning deletion!" << endl;
		
		if( skol && skolemFile.tellp() > long(5*1024)*long(1024*1024) ) {
			if( remove( skolemName.c_str() ) ) 
				cout << "Warning deletion!" << endl;
		} else if ( !skol && herbrandFile.tellp() > long(5*1024)*long(1024*1024) ) {
			if( remove( skolemName.c_str() ) ) 
				cout << "Warning deletion!" << endl;
		} else certification_close( skol ? skolemFile : herbrandFile, skol );
	}

	return status == l_True;
}

void QestoGroups::certification_open( ofstream& skolemFile, ofstream& herbrandFile ) {
	skolemFile << ".model skolem" << endl << ".inputs";
	herbrandFile << ".model herbrand" << endl << ".inputs";
	
	if( opt.get_cert2Mfs() ) {
		for( size_t lv = 0; lv < levs.lev_count(); ++lv ) {
			const VarVector& lvs = levs.level_vars( lv );
			for( const Var& v : lvs ) {
				if( level_type( lv ) == EXISTENTIAL ) 
					skolemFile << ' ' << v;
				if( level_type( lv ) == UNIVERSAL ) 
					herbrandFile << ' ' << v;
			}
		}
	}
	for( size_t lv = 0; lv < levs.lev_count(); ++lv ) {
		const VarVector& lvs = levs.level_vars( lv );
		for( const Var& v : lvs ) {
			if( level_type( lv ) == UNIVERSAL ) 
				skolemFile << ' ' << v;
			if( level_type( lv ) == EXISTENTIAL ) 
				herbrandFile << ' ' << v;
		}
	}

	skolemFile << endl << ".outputs";
	herbrandFile << endl << ".outputs";

	for( size_t lv = 0; lv < levs.lev_count(); ++lv ) {
		const VarVector& lvs = levs.level_vars( lv );
		ofstream* file = NULL;
		if( level_type( lv ) == EXISTENTIAL ) 
			file = &skolemFile;
		else if( level_type( lv ) == UNIVERSAL ) 
			file = &herbrandFile;
		else assert(0);
		for( const Var& v : lvs ) {
			if( opt.get_cert2Mfs() ) 
				*file << " n" << v;
			else 
				*file << ' ' << v;
		}
	}

	if( opt.get_cert2Mfs() ) {
		skolemFile << endl << ".outputs";
		herbrandFile << endl << ".outputs";
		for( size_t lv = 0; lv < levs.lev_count(); ++lv ) {
			const VarVector& lvs = levs.level_vars( lv );
			for( const Var& v : lvs ) {
				if( level_type( lv ) == EXISTENTIAL ) 
					skolemFile << " c" << v;
				if( level_type( lv ) == UNIVERSAL ) 
					herbrandFile << " c" << v;
			}
		}
	}

	skolemFile << " result";
	herbrandFile << " result";

	skolemFile << endl << "#----INIT-START----" << endl;
	herbrandFile << endl << "#----INIT-START----" << endl;

	for( Var v = 1; v <= levs.maxv(); ++v ) {
		ofstream* file;
		if( levs.type( v ) == EXISTENTIAL ) 
			file = &skolemFile;
		else if( levs.type( v ) == UNIVERSAL ) 
			file = &herbrandFile;
		else continue;
		if( opt.get_cert2Mfs() ) {
			*file << ".names " << v << "n0" << endl << 0 << endl;
			onsetId[v] = 0;
			*file << ".names " << v << "f0" << endl << 0 << endl;
			offsetId[v] = 0;
		} else {
			*file << ".names " << v << "n0" << endl << 0 << endl; // connect to onsetId
			onsetId[v] = 0;
		}
	}
	for( size_t lv = 0; lv < levs.lev_count(); ++lv ) {
		ofstream* file;
		if( level_type( lv ) == EXISTENTIAL ) 
			file = &skolemFile;
		else if( level_type( lv ) == UNIVERSAL ) 
			file = &herbrandFile;
		else continue;
		*file << ".names " << lv << "d0" << endl << 0 << endl; // already explored boolean space
		definedId[lv] = 0;
	}

	herbrandFile << "#-----EXIST-RULE-START-----" << endl;
	for( const pair<size_t, vector<Lit> >& p : waitForCert_rules_exists ) {
		size_t gid = p.first;
		const vector<Lit>& uniLits = p.second;
		assert( level_type( groups.qlev( gid ) ) == EXISTENTIAL );
		assert( level_type( levs.lev_count() - 1 ) == EXISTENTIAL );

		vector<vector<Lit> > moveLit( levs.lev_count() );
		for( Lit lit : uniLits ) {
			size_t ulv = levs.qlev( lit );
			assert( level_type( ulv ) == UNIVERSAL );
			assert( groups.qlev( gid ) < ulv && ulv < levs.lev_count() - 1 );
			moveLit[ ulv ].push_back( lit );
		}

		vector<size_t> conflict_groups;
		conflict_groups.push_back( gid );
		
		analyze_cert( herbrandFile, false, moveLit, conflict_groups );
	}
	herbrandFile << "#-----EXIST-RULE-END-----" << endl;

	skolemFile << "#-----INIT-END-----" << endl;
	herbrandFile << "#-----INIT-END-----" << endl;
}

template<class T> string toStr( const T& num ) { ostringstream o; o << num; return o.str(); }

void QestoGroups::certification_close( ofstream& file, bool skol ) {
	if( opt.get_ex_inst() && !skol && opt.get_cert2Mfs() ) {
		file << "#----INST_EX-START----" << endl;
		
		set<size_t> uniGroups;
		
		for( size_t endGroup : clauseInfluencedByInstE ) {
			assert( groups.is_end( endGroup ) );
	
			size_t gid = endGroup;
			// rule_exi covers the region inner than lastExiGroup. So we only consider the outer.
			int lastExiGroup = -1;
			while( true ) {
				if( level_type( groups.qlev( gid ) ) == EXISTENTIAL && !groups.lits( gid ).empty() ) {
					lastExiGroup = gid;
					break;
				}
				if( groups.parent( gid ) != gid ) 
					gid = groups.parent( gid );
				else break;
			}
			if( lastExiGroup == -1 ) continue;
			assert( lastExiGroup >= 0 );
			
			gid = lastExiGroup;
			while( true ) {
				if( level_type( groups.qlev( gid ) ) == UNIVERSAL && !groups.lits( gid ).empty() ) 
					uniGroups.insert( gid );
				if( groups.parent( gid ) != gid ) 
					gid = groups.parent( gid );
				else break;
			}
		}
		
		vector<set<size_t> > situationsOfEachOffset( levs.maxv()+1 );
		for( size_t gid : uniGroups ) {
			size_t pid;
			if( gid == groups.parent( gid ) ) 
				pid = SIZE_MAX;
			else {
				pid = groups.parent( gid );
				while( groups.lits( pid).empty() && groups.parent( pid ) != pid ) 
					pid = groups.parent( pid );
				if( groups.lits( pid ).empty() ) {
					assert( pid == groups.parent( pid ) );
					pid = SIZE_MAX;
				}
			}

			for( Lit aLit : groups.lits( gid ) ) {
				assert( !sign( aLit ) );
				situationsOfEachOffset[ var(aLit) ].insert( pid );
			}
		}

		int kId = 0;
		for( Var v = 1; v <= levs.maxv(); ++v ) {
			const set<size_t>& situations = situationsOfEachOffset[ v ];
			if( situations.empty() ) continue;
			const size_t lv = levs.level( v );
			const string sDef = toStr( lv ) + 'd' + toStr( definedId[ lv ] ) + ' ';
			const string sOriOffset = toStr( v ) + 'f' + toStr( offsetId[v] ) + ' ';
			const string sNewOffset = toStr( v ) + 'f' + toStr( offsetId[v] + 1 ) + ' ';

			set<size_t>::iterator it = situations.find( SIZE_MAX );
			if( it != situations.end() ) {
				file << ".names " << sOriOffset << sDef << sNewOffset << endl;
				file << "01 0" << endl;
			} else {
				ostringstream s1, s2, s3, s4, s5;
				const string sK = "k" + toStr( kId ) + ' ';
				s1 << ".names ";
				for( size_t pid : situations ) { 
					s1 << 'g' << pid << ' ';
					s2 << '1';
					groups.setWaitingForBlifWritting( pid, false );
				}
				s1 << sK;
				s2 << " 0";
				file << s1.str() << endl << s2.str() << endl;
				
				s3 << ".names " << sOriOffset << sDef << sK << sNewOffset;
				s4 << "1-- 1";
				s5 << "-01 1";
				file << s3.str() << endl << s4.str() << endl << s5.str() << endl;
				++kId;
			}
			++offsetId[v];
		}
		file << "#----INST_EX-CLOSE----" << endl;
	}

	file << "#----CONNECT-START----" << endl;
	for( Var v = 1; v <= levs.maxv(); ++v ) {
		if( ( skol && levs.type( v ) == EXISTENTIAL ) || ( !skol && levs.type( v ) == UNIVERSAL ) ) {
			if( opt.get_cert2Mfs() ) {
				file << ".names " << v << "n" << onsetId[v] << " " << "n" << v << endl << "1 1" << endl;
				file << ".names " << 'n' << v << " " << v << 'f' << offsetId[v] << " c" << v << endl << "00 0" << endl;
			} else 
				file << ".names " << v << "n" << onsetId[v] << " " << v << endl << "1 1" << endl;
		}
	}
	file << "#-----CONNECT-END-----" << endl;
		
	file << endl << "#----BAD-START----" << endl;
	file << ".names result\n";
	file << (skol?'1':'0') << endl;
	file << "#-----BAD-END-----" << endl; 
	
	
	file << "#----GROUPS-START----" << endl;
	// net gi at qlev means C_k^(<=qlev)
	for( size_t qlev = 0; qlev < levs.lev_count(); ++qlev ) {
		vector<size_t> gs = groups.groups(qlev);
		for( size_t gi : gs ) {
			if( !groups.isWaitingForBlifWritting( gi, skol ) ) continue;
			assert( !groups.lits( gi ).empty() );
			file << ".names ";
			size_t giter = gi;
			vector<bool> inputsInv;
			while( true ) {
				if( giter != gi && groups.isWaitingForBlifWritting( giter, skol ) ) {
					file << groups.getName( giter ) << " ";
					inputsInv.push_back( false );
					break;
				}
				for( const Lit li : groups.lits( giter ) ) {
					file <<  var( li ) << " ";
					inputsInv.push_back( sign(li) );
				}
				if( giter == groups.parent( giter ) ) break;
				giter = groups.parent( giter );
			}
			file << groups.getName( gi ) << endl;
	       	for( bool inv : inputsInv ) 
				file << ( inv?"1":"0" );
			file << " 0" << endl;
		}
	}
	file << "#-----GROUPS-END-----" << endl;
	file << ".end" << endl;

	file.close();
}

bool QestoGroups::analyze(size_t qlev, size_t& bt_qlev, vector<size_t>& conflict_groups, 
						  ofstream& skolemFile, ofstream& herbrandFile ) 
{
	QuantifierType loser=level_type(qlev);
	if(verb>2)
		std::cerr << "(" << tot_bt_count << ") analyse loser:" << loser << "@" << qlev << std::endl;
	bool ret;
	const bool skol = ( loser == UNIVERSAL );
	vector<size_t> low_conflict_groups;

	if( skol ) 
		ret = analyze_univ(qlev,bt_qlev,low_conflict_groups, skolemFile);
	else 
		ret = analyze_exists(qlev,bt_qlev,low_conflict_groups, herbrandFile );

	if( ret ) 
		for( size_t& g : low_conflict_groups ) 	
			conflict_groups.push_back( find_parent( bt_qlev, g ) );  
	
	// if( 0 || debug) {
	// 	cout << "#- " << ( skol ? "Sk " : "He " );
	// 	for( size_t lv = ( ret ? bt_qlev + 1 : 0 ); lv < qlev; ++lv ) { 
	// 		if( skol && level_type(lv) != EXISTENTIAL ) continue;
	// 		if( !skol && level_type(lv) != UNIVERSAL ) continue;
	// 		if( opt.get_pin() && skol ) {
    //     		for( size_t gi : groups.groups( lv ) ) 
	// 				for( Pin* pP : groups.getPins( gi ) ) 
	// 					if( eval( mkLit( pinVar(lv,pP->id) ) ,abstractions[ lv ].model ) == l_True ) 
	// 						cout <<'p'<< pP->id << " * ";
	// 		} else {
	// 			for( const Var& v : levs.level_vars( lv ) ) {
	// 				assert( abstractions[ lv ].model[v] != l_Undef );
	// 				cout << mkLit( v, abstractions[ lv ].model[v] == l_False ) << " * ";
	// 			}
	// 		}
	// 	}
	// 	cout << " @ ";
	// 	for( size_t gid : conflict_groups ) 
	// 		cout << ( skol ? "" : "!" ) << 'g' << gid << " * ";
	// 	cout << endl;
	// }

	if( opt.get_cert() ) {
		if( opt.get_pin() && skol ) 
			analyze_cert_pin( qlev, bt_qlev, conflict_groups, skolemFile, ret ); // with analyze_univ
		else //with analyze_exists
			analyze_cert( qlev, bt_qlev, conflict_groups, 
						  ( skol ? skolemFile : herbrandFile ), skol, ret, low_conflict_groups );
	}
	return ret;
}

	
#define BIG_HERBRAND_SIZE 0
void QestoGroups::analyze_cert( size_t qlev,size_t bt_qlev,const vector<size_t>& conflict_groups,
								ofstream& file, bool skol, bool ret, 
								const vector<size_t>& low_conflict_groups )
{ 
	// used by existential_analysis
	assert( opt.get_cert() );
	assert( !opt.get_pin() || !skol );
	if( file.is_open() && file.tellp() > long(5*1024)*long(1024*1024) ) {
		file.close();
		return;
	}
	vector<vector<Lit> > moveLit( levs.lev_count() );
	analyze_cert_extract_move( qlev, bt_qlev, conflict_groups, file, skol, ret,
							   moveLit, low_conflict_groups );
	analyze_cert( file, skol, moveLit, conflict_groups );
}


void 
QestoGroups::analyze_cert_extract_move( size_t qlev, size_t bt_qlev,
										const vector<size_t>& conflict_groups, 
										ofstream& file, bool skol, bool ret,
										vector<vector<Lit> >& moveLit, 
										const vector<size_t>& low_conflict_groups ) 
{
	// used by existential_analysis
	assert( opt.get_cert() );
	moveLit.clear();
	moveLit.resize( levs.lev_count() );
	for( size_t lv = ( ret ? bt_qlev + 1 : 0 ); lv < qlev; ++lv ) { 
		if( skol && level_type(lv) != EXISTENTIAL ) continue;
		if( !skol && level_type(lv) != UNIVERSAL ) continue;
		for( const Var& v : levs.level_vars( lv ) ) {
			bool sign = ( abstractions[ lv ].model[v] == l_False );
			moveLit[lv].push_back( mkLit( v, sign ) );
		}
	}
	
	if( skol ) return;
	assert( level_type( qlev ) == EXISTENTIAL );
	if( !ret ) return;
	if( BIG_HERBRAND_SIZE ) return;
	set<size_t>* pCc = new set<size_t>(); // pointer of conflict children
	assert( !low_conflict_groups.empty() );
	for( const size_t & gid : low_conflict_groups ) 
		pCc->insert( gid );
	assert( qlev > 0 );
	size_t levelOfCc = ( ret ? qlev - 1 : 0 );
    #ifndef NDEBUG
	for( size_t gid : *pCc ) 
		assert( groups.qlev( gid ) == levelOfCc );
    #endif
	for( int lv = int(qlev) - 1; lv >= ( ret ? int(bt_qlev) + 1 : 0 ); --lv ) {
		if( moveLit[lv].empty() ) continue;
		assert( level_type(lv) == UNIVERSAL );
		assert( int( levelOfCc ) >= lv );
		while( int( levelOfCc ) != lv ) {
			assert( int( levelOfCc ) > lv );
			assert( levelOfCc > 0 );

			set<size_t>* pTemp = new set<size_t>();
			for( size_t gid : *pCc ) 
				pTemp->insert( groups.parent( gid ) );
			delete pCc;
			pCc = pTemp;
			--levelOfCc;

            #ifndef NDEBUG
			for( size_t gid : *pCc ) 
				assert( groups.qlev( gid ) == levelOfCc );
            #endif
		}
		vector<bool> appear( 2*levs.maxv()+1, false );
		for( size_t gC : *pCc ) 
			for( Lit u : groups.lits( gC ) ) 
				appear[ u.x ] = true;
		vector<bool> canBeRemoved( moveLit[lv].size(), false );
		bool someMoveCanBeRemoved = false;
		for( int i = 0; i < int( moveLit[lv].size() ); ++i ) {
			Lit move = moveLit[lv][i];
			if( !appear[ (~move).x ] ) {
				canBeRemoved[i] = true;
				someMoveCanBeRemoved = true;
			}
		}
		if( someMoveCanBeRemoved ) {
			vector<Lit> vTemp;
			for( int i = 0; i < int( moveLit[lv].size() ); ++i ) 
				if( !canBeRemoved[i] ) 
					vTemp.push_back( moveLit[lv][i] );
			moveLit[lv] = vTemp;
		}
	}
	delete pCc;	
}

void QestoGroups::analyze_cert( ofstream& file, bool skol, 
								const vector<vector<Lit> >& moveLit, 
								const vector<size_t>& conflict_groups )
{
	// used by both rules_exist and existential_analysis
	if( file.is_open() && file.tellp() > long(5*1024)*long(1024*1024) ) {
		file.close();
		return;
	}
	assert( opt.get_cert() );
	if( debug ) {
		file << "#- " << ( skol ? "Sk " : "He " );
		for( const vector<Lit>& vl : moveLit ) 
			for( Lit lit : vl ) 
				file << lit << " * ";
		file << " @ ";
		for( size_t gid : conflict_groups ) 
			file << ( skol ? "" : "!" ) << 'g' << gid << " * ";
		file << endl;
	}

	set<size_t> conflict_groups2;
	for( size_t gid : conflict_groups ) {
		size_t p = gid;
		while( groups.lits( p ).empty() && groups.parent( p ) != p ) 
			p = groups.parent(p);
		conflict_groups2.insert( p );
	}

	unsigned& situationId = ( skol ? sk_situationId : he_situationId );
	++situationId;
	
	{
		ostringstream line1, line2;
		line1 << ".names ";
		for( const size_t gid : conflict_groups2 ) 
			line1 << groups.getName( gid ) << ' ';
		line1 << "s" << situationId; // corresponds to lambda(winning condition) in CUED
 		line2 << string( conflict_groups2.size(), (skol?'1':'0') ) << " 1"; 
		// winning condition for skol : disselect some grps
		//                       herb : select some grps
		for( const size_t gid : conflict_groups2 ) 
			groups.setWaitingForBlifWritting( gid, skol );
		file << line1.str() << endl << line2.str() << endl;
	}
	const string s_oriSitu = 's' + toStr( situationId ) + ' ';
	int lastL = -1;
	for( size_t lv1 = 0; lv1 < levs.lev_count(); ++lv1 ) {
		if( moveLit[lv1].empty() ) continue;
		
		if( BIG_HERBRAND_SIZE ) {
			if( lastL != -1 ) {
				ostringstream line1, line2;
				line1 << ".names " << 's' << situationId << ' ';
				line2 << '1';
					
				for( Lit ell : moveLit[ lastL ] ) {
					line1 << var(ell) << ' ';
					line2 << (sign(ell)?0:1);
				}
				line1 << 's' << situationId + 1 << ' ';
				line2 << " 1";			
				file << line1.str() << endl << line2.str() << endl;
				++situationId;
			}
		}
		
		lastL = lv1;
		const string s_def = toStr(lv1) + 'd' + toStr( definedId[lv1] ) + ' '; // explored space
		const string s_situ = 's' + toStr( situationId ) + ' '; // lambda in CUED
		static unsigned notDAndSId = 1;
		const string s_r = 'r' + toStr( notDAndSId ) + ' '; // define'&situation
		file << ".names " << s_def << s_situ << s_r << endl;
		file << "01 1" << endl;
		
		for( Lit el : moveLit[lv1] ) {
			if( !opt.get_cert2Mfs() && sign( el ) ) continue;
			Var ev = var(el);
			string s_ev_n;
			string s_ev_nn;
			if( !sign(el) ) {
				s_ev_n = toStr( ev ) + 'n' + toStr( onsetId[ev] ) + ' ';
				s_ev_nn = toStr( ev ) + 'n' + toStr( onsetId[ev]+1 ) + ' '; 
			} else {
				s_ev_n = toStr( ev ) + 'f' + toStr( offsetId[ev] ) + ' ';
				s_ev_nn = toStr( ev ) + 'f' + toStr( offsetId[ev]+1 ) + ' '; 
			}

			ostringstream line1, line2;
			line1 << ".names ";
			line1 << s_r << s_ev_n << s_ev_nn;
			line2 << "00 0";
			file << line1.str() << endl << line2.str() << endl;
			if( !sign(el) ) 
				++onsetId[ev];
			else 
				++offsetId[ev];
		}
		++notDAndSId;
		
		//if( opt.get_ex_inst() && !skol ) {
		if ( 1 ) {
			ostringstream line1, line2;
			line1 << ".names " << s_situ << s_def << lv1 << 'd' << definedId[lv1]+1;
			line2 << "00 0";
			file << line1.str() << endl << line2.str() << endl;
			++definedId[ lv1 ];
		}
	}	
	/*
	if(  !opt.get_ex_inst() || skol ) {
		size_t innermostLevelOfConflict = 0;
		for( size_t gid : conflict_groups2 ) innermostLevelOfConflict = max( innermostLevelOfConflict, groups.qlev( gid ) ); 

		for( size_t lv = innermostLevelOfConflict; lv < levs.lev_count(); ++lv ) {
			if( skol && level_type( lv ) != EXISTENTIAL ) continue;
			if( !skol && level_type( lv ) != UNIVERSAL ) continue;
			const string s_def = toStr( lv ) + 'd' + toStr( definedId[lv] ) + ' ';
			ostringstream line1, line2;		
			line1 << ".names " << s_oriSitu << s_def << lv << 'd' << definedId[lv]+1;
			line2 << "00 0";
			file << line1.str() << endl << line2.str() << endl;
			++definedId[lv];
		}
	}*/	
}



int QestoGroups::fillChildren( size_t gid, vector<bool>& mark, size_t endlev ) {
	assert( mark[ groups.parent( gid ) ] || groups.parent( gid ) == gid || !groups.lits(gid).empty() );
	assert( groups.qlev( gid ) < endlev );
	if( mark[ gid ] ) return 0;
	mark[ gid ] = true;
	if( groups.qlev( gid ) == endlev - 1 ) return 1;
	int nMark = 0; //only count mark on level endlev - 1
	for( size_t child : groups.get_children( gid ) ) nMark += fillChildren( child, mark, endlev );
	assert( !groups.is_end( gid ) || nMark );
	return nMark;
}

void QestoGroups::analyze_cert_pin( size_t qlev, size_t bt_qlev, const vector<size_t>& conflict_groups,
									ofstream& file, bool ret)
{ 
	if( file.is_open() && file.tellp() > long(5*1024)*long(1024*1024) ) {
		file.close();
		return;
	}

	assert( opt.get_pin() );

	unsigned& situationId = sk_situationId;
	++situationId;
	bool isSmallCube = true; //Warning Cued=false, Qesto=true

	set<size_t> conflict_groups2;
	for( size_t gid : conflict_groups ) {
		size_t p = gid;
		while( groups.lits( p ).empty() && groups.parent( p ) != p ) 
			p = groups.parent(p);
		conflict_groups2.insert( p );
	}
	
	vector< set<pair<Pin*, size_t> > > movePin( levs.lev_count() );

	for( size_t lv = ( ret ? bt_qlev + 1 : 0 ); lv < qlev; ++lv ) { 
		if( level_type(lv) != EXISTENTIAL ) continue;
       	for( size_t gi : groups.groups( lv ) ) { 
			for( Pin* pP : groups.getPins( gi ) ) {
				if( eval( mkLit( pinVar(lv,pP->id) ) ,abstractions[ lv ].model ) == l_True ) 
					movePin[lv].insert( pair<Pin*, size_t>( pP, gi ) );
			}
		}
	}

	// remove elements from movePin 
	// until every clause deselected by movePin is deselected by only one movePin.
	// TODO:not only fill( gid ) but also fill( gid2 ) if gid2 is the subset of gid.
	vector<bool> deselected( groups.get_group_count(), false );
	for( const size_t gid : conflict_groups2 ) 
		fillChildren( gid, deselected, qlev );
	
	for( size_t lv = ( ret ? bt_qlev + 1 : 0 ); lv < qlev; ++lv ) {
		vector< set<pair<Pin*, size_t> >::iterator > uselessMovePin;
		for( set<pair<Pin*, size_t> >::iterator it = movePin[lv].begin(); 
			 it != movePin[lv].end(); ++it ) {
			size_t gid = it->second;
			while( groups.parent( gid ) != gid && groups.lits( gid ).empty() ) 
				gid = groups.parent( gid );
			assert( groups.parent( gid ) != gid || !groups.lits( gid ).empty() );
			if( fillChildren( gid, deselected, qlev ) == 0 ) 
				uselessMovePin.push_back( it );
		}
		for( set<pair<Pin*, size_t> >::iterator it : uselessMovePin ) 
			movePin[lv].erase( it );
	}


	if( debug ) {
		file << "#- " << "Sk ";
		for( size_t lv = ( ret ? bt_qlev + 1 : 0 ); lv < qlev; ++lv ) { 
			for( const pair<Pin*, size_t>& pr : movePin[lv] ) 
				file << pr.first->getName() << " * ";
		}
		file << " @ ";
		for( size_t gid : conflict_groups2 ) 
			file << 'g' << gid << " * ";
		file << endl;
	}

	{
		ostringstream line1, line2;
		line1 << ".names ";
		for( const size_t gid : conflict_groups2 ) 
			line1 << groups.getName( gid ) << ' ';
		line1 << "s" << situationId;
		line2 << string( conflict_groups2.size(), '1' ) << " 1";
		for( const size_t gid : conflict_groups2 ) 
			groups.setWaitingForBlifWritting( gid, true );
		file << line1.str() << endl << line2.str() << endl;
	}

	vector< set<pair<Lit, size_t> > > moveLitAndParent( levs.lev_count() );
	for( size_t lv = ( ret ? bt_qlev + 1 : 0 ); lv < qlev; ++lv ) { 
		if( level_type(lv) != EXISTENTIAL ) continue;
		if( movePin[lv].empty() ) continue;

		//check if a var only appears in one phase. If true, then p != lit <- not parent. Instead,  p = lit.
		vector<bool> appear( 2*levs.maxv() + 1, false );
		vector<bool> hasSizeMax( 2*levs.maxv() + 1, false );
		for( const pair<Pin*, size_t>& pr : movePin[lv] ) 
			appear[ pr.first->lit.x ] = true;

		for( const pair<Pin*, size_t>& pr : movePin[lv] ) {
			Pin* pP =  pr.first;
			size_t gi = pr.second;
			size_t gParent;
			if( !isSmallCube && !appear[ (~(pP->lit)).x ] ) {
				gParent = SIZE_MAX;
				hasSizeMax[ pP->lit.x ] = true;
			}
			else if( lv == 0 ) {
				gParent = SIZE_MAX; 
				hasSizeMax[ pP->lit.x ] = true;
			}
			else {
				gParent = groups.parent( gi );
				while( groups.lits( gParent ).empty() && groups.parent( gParent ) != gParent ) 
					gParent = groups.parent(gParent);
				if( groups.lits( gParent ).empty() ) {
					assert( groups.parent( gParent ) == gParent );
					gParent = SIZE_MAX;
					hasSizeMax[ pP->lit.x ] = true;
				}
			}
			// if ther is already ( lit, SIZE_MAX) in moveLitAndParent[lv], then there is no need to insert ( lit, parent )
			if( hasSizeMax[ pP->lit.x ] && gParent != SIZE_MAX ) continue;
			assert( !hasSizeMax[ (~(pP->lit)).x ] );
			if( moveLitAndParent[lv].find( pair<Lit, size_t>( pP->lit, gParent ) ) 
				== moveLitAndParent[lv].end() ) {
				moveLitAndParent[lv].insert( pair<Lit, size_t>( pP->lit, gParent ) );
			}
		}
	}
				
	// int lastL = -1;
	const string s_oriSitu = 's' + toStr( situationId ) + ' ';
	for( size_t lv1 = ( ret ? bt_qlev + 1 : 0 ); lv1 < qlev; ++lv1 ) {
		if( movePin[lv1].empty() ) continue;
		assert( !moveLitAndParent[lv1].empty() );
		if( isSmallCube ) {
			/*
			if( lastL != -1 ) {
				ostringstream line1, line2;
				line1 << ".names " << 's' << situationId << ' ';
				line2 << '1';
				// 只要該pin/exist_lit所屬之groups are selected即可，不必非要是由該pin/lit達成。
				for( const pair<Pin*, size_t>& pr : movePin[ lastL ] ) {
					line1 << 'g' << pr.second << ' ';
					line2 << '1';
					groups.setWaitingForBlifWritting( pr.second, true );
				}
				line1 << 's' << situationId + 1 << ' ';
				line2 << " 1";			
				file << line1.str() << endl << line2.str() << endl;
				++situationId;
			}
			lastL = lv1;
			*/
		}
		const string s_situ = 's' + toStr( situationId ) + ' ';
		const string s_def = toStr( lv1 ) + 'd' + toStr( definedId[lv1] ) + ' ';
		static unsigned notDAndSId = 1;
		const string s_r = 'r' + toStr( notDAndSId ) + ' ';
		file << ".names " << s_def << s_situ << s_r << endl;
		file << "01 1" << endl;

		for( const pair<Lit, size_t>& pr : moveLitAndParent[lv1] ) {
			if( !opt.get_cert2Mfs() && sign( pr.first ) ) continue;
			Var ev = var( pr.first );
			string s_ev_n;
			string s_ev_nn;
			if( sign( pr.first ) ) {
				s_ev_n += toStr( ev ) + 'f' + toStr( offsetId[ev] ) + ' ';
				s_ev_nn += toStr( ev ) + 'f' + toStr( offsetId[ev]+1 ) + ' ';
			} else {
				s_ev_n += toStr( ev ) + 'n' + toStr( onsetId[ev] ) + ' ';
				s_ev_nn += toStr( ev ) + 'n' + toStr( onsetId[ev]+1 ) + ' '; 
			}

			ostringstream line1, line2, line3;
			line1 << ".names ";
			if( pr.second != SIZE_MAX ) {
				assert( lv1 != 0 );
				groups.setWaitingForBlifWritting( pr.second, true );
				const string q = 'g' + toStr( pr.second ) + ' ';
				line1 << s_r << q << s_ev_n << s_ev_nn;
				line2 << "--1 1";
				line3 << "10- 1";
				file << line1.str() << endl << line2.str() << endl << line3.str() << endl;
			} else {
				line1 << s_r << s_ev_n << s_ev_nn;
				line2 << "00 0";
				file << line1.str() << endl << line2.str() << endl;
			}
			if( sign( pr.first ) ) 
				++offsetId[ev];
			else 
				++onsetId[ev];
		}
		++notDAndSId;
		if( !isSmallCube ) {
			const string s_def = toStr( lv1 ) + 'd' + toStr( definedId[lv1] ) + ' ';
			ostringstream line1, line2;		
			line1 << ".names " << s_oriSitu << s_def << lv1 << 'd' << definedId[lv1]+1;
			line2 << "00 0";
			file << line1.str() << endl << line2.str() << endl;
			++definedId[lv1];
		}
	}

	if( isSmallCube ) {
		size_t innermostLevelOfConflict = 0;
		for( size_t gid : conflict_groups2 ) 
			innermostLevelOfConflict = max( innermostLevelOfConflict, groups.qlev( gid ) ); 
		for( size_t lv = innermostLevelOfConflict; lv < levs.lev_count(); ++lv ) {
			if( level_type( lv ) != EXISTENTIAL ) continue;
			const string s_def = toStr( lv ) + 'd' + toStr( definedId[lv] ) + ' ';
			ostringstream line1, line2;		
			line1 << ".names " << s_oriSitu << s_def << lv << 'd' << definedId[lv]+1;
			line2 << "00 0";
			file << line1.str() << endl << line2.str() << endl;
			++definedId[lv];
		}	
	}
}




bool QestoGroups::analyze_exists( size_t qlev, size_t& bt_qlev, vector<size_t>& conflict_groups, ofstream& herbrandFile ) {
	assert( level_type(qlev) == EXISTENTIAL );
	const auto& abstraction_conflict = abstractions[qlev].conflict;
	bool all_opponent = true; //No ancestor can help
	if( qlev < 2 ) return false;
	bt_qlev = -1;

	for( int i = 0; i < abstraction_conflict.size(); ++i ) {
		const Lit l = abstraction_conflict[i];
		if( ( bt_qlev + 2 ) >= qlev ) break;
		assert( sign(l) ); 
		if( !sign(l) ) continue;
		auto pg = get_pinfo( qlev, var(l) ).group;
		assert( group_type( pg ) == UNIVERSAL );
		while( true ) {
			const auto ppg = groups.parent(pg);
			if( ppg == pg ) break;
			pg = ppg;
			const auto pql = groups.qlev(pg);
			const auto pqt = level_type(pql);
			if( pqt == UNIVERSAL ) continue;
			if( !groups.lits( pg ).empty() ) {
				if( all_opponent || pql > bt_qlev ) bt_qlev = pql;
				all_opponent = false;
				break;
			}
		}
	}

	if(all_opponent) return false;
	assert( bt_qlev <= ( qlev - 2 ) );
	if( verb > 2 && ( qlev - 2 ) > bt_qlev ) 
		std::cerr << "long jump" << endl;
	if( verb > 2 ) 
		std::cerr << "bt_qlev:" << bt_qlev << endl;
	for( int i = 0; i < abstraction_conflict.size(); ++i ) {
		const Lit l = abstraction_conflict[i];
		if( !sign(l) ) continue;
		const auto vi = get_pinfo( qlev,var(l) );
		//conflict_groups.push_back( find_parent( bt_qlev, vi.group ) );
		conflict_groups.push_back( vi.group );
	}
	return true;
}

bool QestoGroups::analyze_univ(size_t qlev, size_t& bt_qlev, vector<size_t>& conflict_groups, ofstream& skolemFile ) {
	assert(level_type(qlev)==UNIVERSAL );
	vector<Lit> skLits;
	vector< vector<Lit> > skConditions;
  	const vec<Lit>& abstraction_conflict=abstractions[qlev].conflict;
	const int sz=abstraction_conflict.size();
	bool all_opponent = true;

	if(qlev<2) return false;
	if(verb>3)
		std::cerr << "abstraction_conflict:" << abstraction_conflict << std::endl;
  	bt_qlev = ( level_type(0)==UNIVERSAL ? 0 : 1 );
	vector<int> ex_maxlev (sz, -1 );
	for(int i=0;i<sz;++i) {//analyze each group in the core
		const Lit conflict_lit = abstraction_conflict[i];
		//assert( !sign(conflict_lit) ); //Hank //FIXME
		if(sign(conflict_lit)) continue;
    	
		size_t esat_ql,usat_ql;
		const auto group = get_pinfo(qlev,var(conflict_lit)).group;
		if(find_last_sat_elit(group,esat_ql)) {
			const auto q=(int)esat_ql;
			if(q>ex_maxlev[i]) 
				ex_maxlev[i]=q;
		} else {
			all_opponent=false;
			if(find_first_udesel(group,usat_ql)) 
				if(usat_ql > bt_qlev) 
					bt_qlev=usat_ql;
		}

	}
  	if(all_opponent) return false;
	
  	if( verb > 2 ) 
	  	cout << "bt_qlev:" << bt_qlev << std::endl;
  	for(int i=0;i<sz;++i) {
    	const Lit l=abstraction_conflict[i];
    	if(sign(l)) continue;
    	const auto vi=get_pinfo(qlev,var(l));
    	if(ex_maxlev[i]<=(int)bt_qlev) 
			conflict_groups.push_back( vi.group );
	}

	return true;
}
void QestoGroups::inst_e(){
  if( debug ) 
  	cout << "inst_e start" << endl;
  FOR_EACH(g,groups.groups(0)) 
  	inst_e(*g);
  if( debug ) 
  	cout << "inst_e end" << endl;
}

void QestoGroups::inst_e(size_t group) {

	// assert( there is no negative universal literal in C^{<l}_i, where group = C^l_i
	if( groups.is_end(group) ) {
		clauseInfluencedByInstE.push_back( group ); // TODO
    	vec<Lit> cl;
    	bool last = true;
    	for( int qlev=groups.qlev(group)+1; qlev--; group=groups.parent(group) ) {
      		if(level_type(qlev) != EXISTENTIAL) {
				assert( level_type(qlev) == UNIVERSAL );
				continue;
			}
      		if(!last){
        		cl.push(~mkLit(s(qlev,group)));
				if( debug ) 
					cout << getSolverName( qlev ) << ".addClause" << cl << endl;
        		abstractions[qlev].addClause(cl);
        		cl.pop();
      		} else {
        		last=false; 
			}
			const auto& ls = groups.lits(group);
			FOR_EACH(li,ls) cl.push(*li);
		}
	} else {
    	bool cut = false;
    	if(group_type(group) == UNIVERSAL) {
    		const auto& literals = groups.lits(group);
      		FOR_EACH(li,literals) {
        		if(!sign(*li)) continue;
        		cut = true; // has negative universal literal
        		break;
      		}
    	} // cut = ( group is universal and there is at least one negative literal. )
    	if(!cut) {
      		const auto& children = groups.get_children(group);
      		FOR_EACH(ci,children) inst_e(*ci);
    	}
  	}
}

size_t QestoGroups::find_parent(size_t qlev,size_t group) {
   assert(groups.qlev(group) >= qlev);
   while(1){
     const auto gql = groups.qlev(group);
     if(gql == qlev) return group;
     group=groups.parent(group);
   }
}

bool QestoGroups::find_first_udesel(size_t group, size_t& ql) {
	bool rv=false;
	assert( svalue(group) == false );
	while( true ) {
		const auto _ql = groups.qlev(group);
		if( level_type( _ql ) == UNIVERSAL && !svalue( group ) ) {
			ql = _ql;
			rv = true;
		}
		const auto parent = groups.parent(group);
		if(group == parent) {
			assert( groups.qlev(group) == 0 );
			goto Finish;//return rv;
		}
		group = parent;
	}
	assert(0);
Finish:
	return rv;
}

bool QestoGroups::find_last_sat_elit(size_t group,size_t& ql) {
	while( true ) {
		ql = groups.qlev(group);
		if(level_type(ql) == EXISTENTIAL) {
			if( opt.get_pin() ) {
				for( Pin* pP : groups.getPins(group) ) {
					if(eval( mkLit(pinVar(ql,pP->id)) ,abstractions[ql].model) == l_True) 
						return true;
				}
			} else {
				FOR_EACH(li,groups.lits(group)) {
					if(eval(*li,abstractions[ql].model)==l_True) return true;
				}	
			}
		}
		const auto parent = groups.parent(group);
		if( group == parent ) return false;
		group = parent;
	}
	assert(0);
	return false;
}

bool QestoGroups::is_disselected_by( size_t group, size_t ql ) {
	assert( groups.qlev(group) >= ql );
	while( groups.qlev(group) != ql && groups.qlev(group) > 0 ) 
		group = groups.parent(group);
	assert( groups.qlev(group) == ql );

	if( level_type(ql)==EXISTENTIAL && opt.get_pin() ) { // Hank
		for( Pin* pP : groups.getPins(group) ) 
			if(eval( mkLit(pinVar(ql,pP->id)) ,abstractions[ql].model)==l_True) 
				return true;
		return false;
	} else {
		FOR_EACH(li,groups.lits(group)) if(eval(*li,abstractions[ql].model)==l_True) return true;
		return false;
	}
}

void QestoGroups::allocate_selectors() {
	// abstractions.var = { ori......p......t......s }
	const Var orig_maxv=levs.maxv();
	assert(levs.lev_count());
  	for( size_t qlev = 0; true; ++qlev ) {
    	assert(qlev<=levs.lev_count());
   		abstractions[qlev].new_variables(orig_maxv);
        if (opt.get_ssat() && qlev >= levs.lev_count()) break; // Perry
    	if( qlev ) {//parent selectors
      		const vector<size_t>& pgs=groups.groups(qlev-1);
      		FOR_EACH( gi,pgs ) {
	        	const auto group=*gi;
   	     		Var pv;
				if( opt.get_strong_pri() && level_type(qlev)==EXISTENTIAL ) 
					pv = abstractions[qlev].newVar( false );
				else{ 
					pv =abstractions[qlev].newVar(/*assumption*/);
					//cout << "pv: " << ", " << pv <<endl;
				}

        		if (pvars.size()<=group) 
					pvars.resize(group+1,-1);
		        pvars[group] = pv;
        		if(verb>5)	
					std::cerr<<"m: "<<group<<"@"<<qlev<<":"<<pv<<std::endl;
                // Perry
                if ((int)pv2gr.size() <= pv) 
					pv2gr.resize(pv+1,-1);
                pv2gr[pv] = group;

        		const size_t inx= pv-orig_maxv-1;
        		auto& ql_infos=infos[qlev];
        		if (ql_infos.size()<=inx) 
					ql_infos.resize(inx+1);
        		ql_infos[inx].qlev=qlev-1;
        		ql_infos[inx].group=*gi;
      		}
    	}
	    if( qlev >= levs.lev_count() ) { assert( level_type(qlev)==UNIVERSAL ); break; }
    	const auto& gs=groups.groups(qlev);
    	FOR_EACH(gi,gs) {
      		const auto group=*gi;

            // [Perry] Level selectors
      		const Var tv=abstractions[qlev].newVar();
			//cout << "t: " << tv << ", ";
      		if (tvars.size()<=group) 
				tvars.resize(group+1,-1);
      		tvars[group]=tv;
    	}
    	FOR_EACH(gi,gs) {
      		const auto group=*gi;
      		const Var sv=abstractions[qlev].newVar(level_type(qlev)==EXISTENTIAL);
			//cout << "s: " << sv << ", ";
      		if (svars.size()<=group) 
			  	svars.resize(group+1,-1);
      		svars[group]=sv;
      		if(verb>5)
				std::cerr << "m: " << group << "@" << qlev << ":" << sv << std::endl;
    	}
		cout << endl;	
  	}
	if( opt.get_pin() ) { // Hank
		const vector<Pin*>& pins = groups.getPins();
		for( Pin* pP : pins ) {
			Var pv;
			if( opt.get_pin_pol() ) 
				pv = abstractions[pP->qlev].newVar(false);
			else 
				pv = abstractions[pP->qlev].newVar();
			if( pinVars.size() <= pP->id ) 
				pinVars.resize( pP->id + 1, -1 );
			pinVars[pP->id] = pv;
		}
	}
}



