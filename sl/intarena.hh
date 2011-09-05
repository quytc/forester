/*
 * Copyright (C) 2011 Kamil Dudka <kdudka@redhat.com>
 *
 * This file is part of predator.
 *
 * predator is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * any later version.
 *
 * predator is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with predator.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef H_GUARD_INTARENA_H
#define H_GUARD_INTARENA_H

#include "config.h"

#include <map>
#include <set>
#include <vector>

#include <boost/foreach.hpp>

/// ad-hoc implementaiton;  wastes memory, performance, and human resources
template <typename TInt, typename TObj>
class IntervalArena {
    public:
        typedef std::set<TObj>                      TSet;

        // for compatibility with STL
        typedef std::pair<TInt, TInt>               key_type;
        typedef std::pair<key_type, TObj>           value_type;

    private:
        typedef std::set<TObj>                      TLeaf;
        typedef std::map</* beg */ TInt, TLeaf>     TLine;
        typedef std::map</* end */ TInt, TLine>     TCont;
        TCont                                       cont_;

    public:
        void add(const key_type &, const TObj);
        void sub(const key_type &, const TObj);
        void intersects(TSet &dst, const key_type &key) const;

        void clear() {
            cont_.clear();
        }

        IntervalArena& operator+=(const value_type &item) {
            this->add(item.first, item.second);
            return *this;
        }

        IntervalArena& operator-=(const value_type &item) {
            this->sub(item.first, item.second);
            return *this;
        }
};

template <typename TInt, typename TObj>
void IntervalArena<TInt, TObj>::add(const key_type &key, const TObj obj)
{
    const TInt beg = key.first;
    const TInt end = key.second;

    cont_[end][beg].insert(obj);
}

template <typename TInt, typename TObj>
void IntervalArena<TInt, TObj>::sub(const key_type &key, const TObj obj)
{
    const TInt winBeg = key.first;
    const TInt winEnd = key.second;

    std::vector<value_type> recoverList;

    typename TCont::iterator it =
        cont_.lower_bound(winBeg + /* right-open interval given as key */ 1);

    for (; cont_.end() != it; ++it) {
        TLine &line = it->second;
        const TInt begFirst = line.begin()->first;
        if (winEnd <= begFirst)
            // we are beyond the window already
            break;

        const TInt end = it->first;

        BOOST_FOREACH(typename TLine::reference ref, line) {
            const TInt beg = ref.first;
            if (winEnd <= beg)
                // we are done with this line
                break;

            // make sure the basic window axioms hold
            CL_BREAK_IF(winEnd <= beg);
            CL_BREAK_IF(end <= winBeg);

            // remove the object from the current leaf (if found)
            TLeaf &os = ref.second;
            if (!os.erase(obj))
                continue;

            if (beg < winBeg) {
                // schedule "the part above" for re-insertion
                const key_type key(beg, winBeg);
                const value_type item(key, obj);
                recoverList.push_back(item);
            }

            if (winEnd < end) {
                // schedule "the part beyond" for re-insertion
                const key_type key(winEnd, end);
                const value_type item(key, obj);
                recoverList.push_back(item);
            }
        }

        // FIXME: Removal of empty sub-containers would be nice.  I am just not
        // sure if the STL containers can safely remove elements during such a
        // traversal.
    }

    // go through the recoverList and re-insert the missing parts
    BOOST_FOREACH(const value_type &rItem, recoverList) {
        const key_type &key = rItem.first;
        const TObj obj = rItem.second;
        const TInt beg = key.first;
        const TInt end = key.second;

        cont_[end][beg].insert(obj);
    }
}

template <typename TInt, typename TObj>
void IntervalArena<TInt, TObj>::intersects(TSet &dst, const key_type &key) const
{
    const TInt winBeg = key.first;
    const TInt winEnd = key.second;

    typename TCont::const_iterator it =
        cont_.lower_bound(winBeg + /* right-open interval given as key */ 1);

    for (; cont_.end() != it; ++it) {
        const TLine &line = it->second;
        const TInt begFirst = line.begin()->first;
        if (winEnd <= begFirst)
            // we are beyond the window already
            break;

        BOOST_FOREACH(typename TLine::const_reference ref, line) {
            const TInt beg = ref.first;
            if (winEnd <= beg)
                // we are done with this line
                break;

            // make sure the basic window axioms hold
            CL_BREAK_IF(winEnd <= beg);
            CL_BREAK_IF(/* end */ it->first <= winBeg);

            const TLeaf &os = ref.second;
            std::copy(os.begin(), os.end(), std::inserter(dst, dst.begin()));
        }
    }
}

#endif /* H_GUARD_INTARENA_H */
