/*
 * Copyright (C) 2010 Kamil Dudka <kdudka@redhat.com>
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

#include "config.h"
#include "clutil.hh"

const struct cl_type* targetTypeOfPtr(const struct cl_type *clt) {
    SE_BREAK_IF(!clt || clt->code != CL_TYPE_PTR || clt->item_cnt != 1);

    clt = clt->items[/* target */ 0].type;
    SE_BREAK_IF(!clt);
    return clt;
}

bool seekRefAccessor(const struct cl_accessor *ac) {
    for(; ac; ac = ac->next) {
        if (CL_ACCESSOR_REF != ac->code)
            continue;

        // there should be no more accessors after the first CL_ACCESSOR_REF
        SE_BREAK_IF(ac->next);
        return true;
    }

    // not found
    return false;
}
