#ifndef CacheEntry_HH
#define CacheEntry_HH

#include "MiniSatExt.hh"
#include <vector>
#include <unordered_set>

struct CacheEntry
{
    CacheEntry(const vec<Lit>& selection, double p = -1): prob(p) {
        pSel.resize( (selection.size()-1) / 64 + 1, 0 );
        for (int i = 0; i < selection.size(); ++i)
            if (!sign(selection[i])) pSel[ i/64 ] |= 1UL << ( i&63UL );
    }
    void set_selection(std::vector<bool>& selection) { sel.swap(selection); }
    
    size_t operator () () const { 
        size_t ret = 0;
        for (size_t v : pSel) ret ^= v;
        return ret;
    }

    bool operator == (const CacheEntry& entry) const {
        assert(pSel.size() == entry.pSel.size());
        for (size_t i = 0; i < pSel.size(); ++i)
            if (pSel[i] != entry.pSel[i]) return false;
        return true;
    }

    std::vector<size_t> pSel;
    double prob;
    std::vector<bool> sel;
};

struct CacheEntryHash {
    size_t operator () (const CacheEntry& entry) const { return entry(); }
};

typedef std::unordered_set<CacheEntry, CacheEntryHash> Cache;

#endif
