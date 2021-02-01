
#include "LevelInfo.hh"

LevelInfo::LevelInfo(const Prefix& pref, const vector<double>& prob)
: pref(pref), prob(prob)
{
  mxv=-1;
  for (size_t level=0; level<pref.size(); ++level) {
    const QuantifierType qt=pref[level].first;
    FOR_EACH(vi,pref[level].second) {
      const Var v=*vi;
      assert(v>=0);
      if (mxv<v) {
        mxv=v;
        vis.resize(mxv+1);
      }
      vis[(size_t)v].first=qt;
      vis[(size_t)v].second=level;
    }
  }
}
