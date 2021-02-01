#ifndef Profiler_HH
#define Profiler_HH

#include <chrono>
#include <iostream>
#include <vector>
#include "Options.hh"

#define TIME_LIMIT 1000

using namespace std::chrono;

struct Profiler
{
    Profiler(const Options& options) :
    opt(options),
    MCS1SuccCnt(0),
    MCS1FailCnt(0),
    MCS2SuccCnt(0),
    MCS2FailCnt(0),
    pruneClaCnt(0),
    pruneCnt(0),
    WMCCnt(0),
    cacheLookup(0),
    cacheHits(0),
    partialWMC(0),
    learntClaLen(0),
    learntClaNum(0),
    pushUNSATCoreAttempt(0),
    pushUNSATCoreSuccess(0),
    accSATTime(0),
    accWMCTime(0)
    {
        prgm_start = high_resolution_clock::now();
    }

    inline void set_SAT_time() { sat_start = high_resolution_clock::now(); }
    inline void accum_SAT_time() { accSATTime += time_elapsed(sat_start); }
    inline void set_WMC_time() { wmc_start = high_resolution_clock::now(); }
    inline void accum_WMC_time() { accWMCTime += time_elapsed(wmc_start); }
    inline double get_tot_time() const { return time_elapsed(prgm_start); }
    inline bool is_timeout() const { return get_tot_time() > TIME_LIMIT; }
    inline double time_elapsed(high_resolution_clock::time_point t) const 
    { return (high_resolution_clock::now() - t).count() * 1e-9; }

    void init(size_t lev_count) {
        levCnt = lev_count;
        selSATCnts.resize(levCnt, 0);
        selUNSATCnts.resize(levCnt, 0);
        dropCnts.resize(levCnt, 0);
        dropAttempts.resize(levCnt, 0);
        dynamicAvgDones.resize(levCnt, 0);
    }

    friend std::ostream& operator << (ostream& os, const Profiler& p) {
        size_t selTotSATCnt = 0, selTotUNSATCnt = 0;

        os << "==== Solving Profiling ====\n\n";

        for (size_t i = 0; i < p.levCnt; ++i) {
            os << "  > # of sel solving on Lev " << i << "  = " << p.selSATCnts[i] + p.selUNSATCnts[i] 
               << " (" << p.selSATCnts[i] << "/" << p.selUNSATCnts[i] << ")" << '\n';
            selTotSATCnt   += p.selSATCnts[i];
            selTotUNSATCnt += p.selUNSATCnts[i];
        }
        os << '\n';

        os << "  > # of sel solving           = " << selTotSATCnt + selTotUNSATCnt << '\n'
           << "  > # of sel solving (SAT)     = " << selTotSATCnt << '\n'
           << "  > # of sel solving (UNSAT)   = " << selTotUNSATCnt << '\n'
           << "  > # of MCS1 solving (SAT)    = " << p.MCS1SuccCnt << '\n'
           << "  > # of MCS1 solving (UNSAT)  = " << p.MCS1FailCnt << '\n'
           << "  > # of MCS2 solving (SAT)    = " << p.MCS2SuccCnt << '\n'
           << "  > # of MCS2 solving (UNSAT)  = " << p.MCS2FailCnt << '\n'
           << "  > # of calls to WMC          = " << p.WMCCnt << '\n'
           << "  > # of partial WMC           = " << p.partialWMC << '\n'
           << "  > Avg. # of pruned clause    = " << (p.pruneCnt? (float)p.pruneClaCnt / p.pruneCnt : 0) << " (" << p.pruneClaCnt << "/" << p.pruneCnt << ")" << '\n'
           << "  > Avg. length of learnt      = " << (float)p.learntClaLen / p.learntClaNum << " (" << p.learntClaLen << "/" << p.learntClaNum << ")" << '\n'
           << "  > Push UNSAT Core Succ rate  = " << (float)p.pushUNSATCoreSuccess / p.pushUNSATCoreAttempt << " (" << p.pushUNSATCoreSuccess << "/" << p.pushUNSATCoreAttempt << ")" << '\n';
        if (p.opt.get_cache())
        os << "  > Cache hit rate             = " << (float)p.cacheHits / p.cacheLookup << " (" << p.cacheHits << "/" << p.cacheLookup << ")" << '\n';
        os << '\n';

        if (p.opt.get_partial()) {
            size_t totDropCnt = 0, totDropAttempt = 0;
            for (size_t i = 0; i < p.levCnt; ++i) {
                os << "  > Avg. drop lits on Lev " << i << "    = " << (p.dropAttempts[i]? (float)p.dropCnts[i] / p.dropAttempts[i] : 0) 
                                                                << " (" << p.dropCnts[i] << "/" << p.dropAttempts[i] << ")" << '\n';
                totDropCnt     += p.dropCnts[i];
                totDropAttempt += p.dropAttempts[i];
            }
            os << "  > Avg. # of drop lits        = " << (totDropAttempt? (float)totDropCnt / totDropAttempt : 0) 
                                                  << " (" << totDropCnt << "/" << totDropAttempt << ")" << '\n';
        }
        os << '\n';

        os << "==== Runtime Profiling ====\n\n"
           << "  > Time consumed on SAT       = " << p.accSATTime << '\n'
           << "  > Time consumed on WMC       = " << p.accWMCTime << '\n'
           << "  > Total time consumed        = " << p.get_tot_time() << '\n';
        return os;
    }

    const Options& opt;
    size_t levCnt;

    high_resolution_clock::time_point prgm_start;
    high_resolution_clock::time_point sat_start;
    high_resolution_clock::time_point wmc_start;
    std::vector<size_t> selSATCnts;
    std::vector<size_t> selUNSATCnts;
    std::vector<size_t> dropCnts;
    std::vector<size_t> dropAttempts;
    std::vector<bool>   dynamicAvgDones;
    size_t      MCS1SuccCnt;
    size_t      MCS1FailCnt;
    size_t      MCS2SuccCnt;
    size_t      MCS2FailCnt;
    size_t      pruneClaCnt;
    size_t      pruneCnt;
    size_t      WMCCnt;
    size_t      cacheLookup;
    size_t      cacheHits;
    size_t      partialWMC;
    size_t      learntClaLen;
    size_t      learntClaNum;
    size_t      pushUNSATCoreAttempt;
    size_t      pushUNSATCoreSuccess;
    double      accSATTime;
    double      accWMCTime;
};

#endif
