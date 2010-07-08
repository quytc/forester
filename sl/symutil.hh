/*
 * Copyright (C) 2009-2010 Kamil Dudka <kdudka@redhat.com>
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

#ifndef H_GUARD_SYMUTIL_H
#define H_GUARD_SYMUTIL_H

/**
 * @file symutil.hh
 * some generic utilities working on top of a symbolic heap
 * @todo API documentation
 */

#include "config.h"

#include "symheap.hh"


TObjId subObjByChain(const SymHeap &sh, TObjId obj, TFieldIdxChain ic);

bool isHeapObject(const SymHeap &heap, TObjId obj);

void digRootObject(const SymHeap &heap, TValueId *pValue);

void getPtrValues(SymHeapCore::TContValue &dst, const SymHeap &heap,
                  TObjId obj);

#endif /* H_GUARD_SYMUTIL_H */