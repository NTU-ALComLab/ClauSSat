
#include "GroupInversion.hh"

void GroupInversion::init() {
  const LevelInfo& levs=groups.get_levs();
  auto ql=levs.lev_count();
  while (ql) {
    --ql;
    const auto& gs=groups.groups(ql);
    FOR_EACH(index,gs) {
      const auto& gid=*index;
      const auto& ls=groups.lits(*index);
      FOR_EACH(literal_index,ls) {
        const Lit& literal = *literal_index;
        vector<size_t>* group_list = _get(literal);
        if (group_list == NULL) {
          group_list = new vector<size_t>();
          put(literal,group_list);
        }
        group_list->push_back(gid);
      }
    }
  }
}

