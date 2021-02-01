/*
 * File:  main.cc
 * Author:  mikolas
 * Created on: Thu, Sep 04, 2014
 * Copyright (C) 2014, Mikolas Janota
 */
#include <signal.h>
#include "ReadQ.hh"
#include "Options.hh"
#include "QestoGroups.hh"
#include "Profiler.hh"
using namespace std;
static void SIG_handler(int signum);
ostream& print_usage(const Options& options,ostream& o);
QestoGroups* gps=NULL;
string skolemName, herbrandName;
Options options;
Profiler profiler(options);



int main(int argc, char** argv) {
	signal(SIGHUP, SIG_handler);
	signal(SIGTERM, SIG_handler);
	signal(SIGINT, SIG_handler);
	signal(SIGABRT, SIG_handler);
	signal(SIGUSR1, SIG_handler);

	if( argc < 2 ) {
		cout << "Error: No inputfile" << endl;
		return 3;
	}

	char* nargv[3];
	char o1[16];
	if( argc == 2 ) {
		strcpy(o1, 	"-geunw"	); //CUED
		nargv[0]=argv[0];
		nargv[1]=o1;
		nargv[2]=argv[1];
		argv=nargv;
		argc=3;
	}

	if(!options.parse(argc, argv)) {
		cerr << "ERROR: processing options." << endl;
		print_usage(options,cerr);
		return 100;
	}
	const vector<string>& rest = options.get_rest();

	if( options.get_cert() ) {
		string s = "s.blif";
		string h = "h.blif";
		if( options.get_cert2Mfs() ) {
			s = "m" + s;
			h = "m" + h;
		}
		skolemName = rest[0] + "_" + s; // _mfs.blif or _ms.blif or _fs.blif
		herbrandName = rest[0] + "_" + h;
	} 

	if( rest.size() != 1 ) cerr<<"WARNING: garbage at the end of command line."<<endl;
	if( options.get_help() ) {
		print_usage(options,cout);
		return 0;
	}
	/* assert( options.get_groups() ); */ 
    /* original version: [-ge] */
    /* cued version: [-geuw] */
    /* cued+UAS vesion: [-geuwn] */
    /* certificate: +[-k] */
    /* ->qesto certificate: [-genk] */
    /* ->our certificate: [-geuwnk] */
    /* onset/careset: +[-km] //must with certificate option */
    cout << options << endl;
	assert( !options.get_cert2Mfs() || options.get_cert() );
	if( options.get_weak_pri() && options.get_strong_pri() ) exit(3);
	if( !options.get_pin() && options.get_pin_pol() ) exit(3);
	const string flafile = rest[0];
	cout << flafile << endl;
	Reader* fr=NULL;
	gzFile ff=Z_NULL;
	if( flafile.size() == 1 && flafile[0] == '-' ) {
		fr=new Reader(cin);
	} else {
		ff = gzopen(flafile.c_str(), "rb");
		if( ff == Z_NULL ) {
			cerr << "Unable to open file: " << flafile << endl;
			exit(100);
		}
		fr=new Reader(ff);
	}
	ReadQ rq(*fr,false);
	try {
		rq.read();
	} catch( ReadException& rex ) {
		cerr << rex.what() << endl;
		exit(100);
	}
	if( fr != NULL ) delete fr;
	QFla qf;
	qf.pref=rq.get_prefix();
	qf.cnf=rq.get_clauses();
    qf.prob=rq.get_prob(); // Perry
	#ifndef NDEBUG
	cout << "QFla qf = " << endl << qf << endl;
	#endif
	if( qf.pref.size() == 0 ) {
		assert( 0 );
		qf.pref.push_back(make_pair(EXISTENTIAL,VarVector()));
	}
	bool r = 0;
	LevelInfo levs(qf.pref, qf.prob);
	Groups* grs=NULL;
	grs=new Groups(options,levs,qf);
	#ifndef NDEBUG
	grs->print();
	#endif
	gps = new QestoGroups( options, levs, *grs );
	if (!options.get_ssat()) {
        r = gps->solve( skolemName, herbrandName, rq.unsatisfy );
        cout << "c bt_count: " << gps->get_btcount() << endl;
        cout << (options.get_pin()? "CUED\t" : "QESTO\t") << (r?"SAT  ":"UNSAT") << "\t" << read_cpu_time() << endl;
    }
    else {
        gps->solve_ssat(rq.unsatisfy);
        gps->output_ssat_sol();
        cout << profiler << endl;
    }
	delete grs;
	delete gps;
    return r ? 10 : 20;
}

static void SIG_handler(int signum) {
	//cerr<<"# received external signal " << signum << endl;
	if( gps && !options.get_ssat() ) cout << "c bt_count: " << gps->get_btcount()<<std::endl;
	if(options.get_cert() ) {
		if( remove( herbrandName.c_str() ) ) cout << "Warning deletion!" << endl;
		if( remove( skolemName.c_str() ) ) cout << "Warning deletion!" << endl;
	}
    if( options.get_ssat() ) {
        gps->output_ssat_sol(true);
        cout << profiler << endl;
    }
	exit(0);
}

ostream& print_usage(const Options& options,ostream& o) {
	o << "USAGE: [OPTIONS] [FILENAME]" << endl;
	return options.print(o);
}
