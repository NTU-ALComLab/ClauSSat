
#ifndef GROUPINVERSION_HH
#define GROUPINVERSION_HH
#include "Groups.hh"
class GroupInversion {
   public:
     GroupInversion(const Groups& groups): groups(groups) {init();}
     inline const vector<size_t>& operator []  (Lit l) const {
       const auto rv=_get(l);
       return rv==NULL ? empty : *rv;
     }
   private:
     const std::vector<size_t> empty;
     const Groups& groups;
     std::vector<std::vector< size_t >*> inversion;
     void init();
     inline size_t lit_index(const Lit& l) const { return sign(l)? var(l)<<1 : (var(l)<<1) + 1; }
     inline vector<size_t>* _get(Lit l) const {
       const size_t i = lit_index(l);
       return i<inversion.size() ? inversion[lit_index(l)] : NULL;
     }

     inline bool put(Lit l, vector<size_t>* c) {
       const size_t i = lit_index(l);
       if (inversion.size() <= i) inversion.resize(i+1, NULL);
       const vector<size_t>* const o=inversion[i];
       inversion[i]=c;
       return o==NULL;
     }

};
#endif

