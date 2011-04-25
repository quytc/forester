/*
 * Copyright (C) 2009-2011 Kamil Dudka <kdudka@redhat.com>
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
#include "symutil.hh"

#include <cl/cl_msg.hh>
#include <cl/storage.hh>

#include "symbt.hh"
#include "symheap.hh"
#include "symproc.hh"
#include "util.hh"

#include <stack>

#include <boost/foreach.hpp>

void moveKnownValueToLeft(
        const SymHeapCore           &sh,
        TValId                      &valA,
        TValId                      &valB)
{
    sortValues(valA, valB);

    if ((0 < valA) && UV_KNOWN != sh.valGetUnknown(valA)) {
        const TValId tmp = valA;
        valA = valB;
        valB = tmp;
    }
}

// a wrapper for legacy code; this will go away once we switch to symheap-ng
TObjId objDup(SymHeap &sh, const TObjId obj) {
    const TValId addr = sh.placedAt(obj);
    const TValId dupAt = sh.valClone(addr);
    return sh.objAt(dupAt);
}

// TODO: remove this
TObjId subObjByChain(const SymHeap &sh, TObjId obj, TFieldIdxChain ic) {
    BOOST_FOREACH(const int nth, ic) {
        obj = sh.subObj(obj, nth);
        if (OBJ_INVALID == obj)
            break;
    }

    return obj;
}

// TODO: remove this
TObjId subObjByInvChain(const SymHeap &sh, TObjId obj, TFieldIdxChain ic) {
    std::stack<int> chkStack;

    // just slowly go to the root
    for (unsigned i = 0; i < ic.size(); ++i) {
        int nth;
        const TObjId parent = sh.objParent(obj, &nth);
        if (OBJ_INVALID == parent)
            // count mismatch
            return OBJ_INVALID;

        chkStack.push(nth);
        obj = parent;
    }

    // now check if the captured selector sequence matches the given one
    for (unsigned i = 0; i < ic.size(); ++i) {
        CL_BREAK_IF(chkStack.empty());
        if (chkStack.top() != ic[i])
            // field mismatch
            return OBJ_INVALID;

        chkStack.pop();
    }
    CL_BREAK_IF(!chkStack.empty());

    return obj;
}

bool isHeapObject(const SymHeap &sh, TObjId obj) {
    if (obj <= 0)
        return false;

    const TValId at = sh.placedAt(obj);
    return SymHeap::isOnHeap(sh.valTarget(at));
}

TObjId /* root */ objRoot(const SymHeap &sh, TObjId obj) {
    if (obj <= 0)
        return obj;

    const TValId addr = sh.placedAt(obj);
    const TValId rootAt = sh.valRoot(addr);
    const TObjId root = const_cast<SymHeap &>(sh).objAt(rootAt);
    if (OBJ_UNKNOWN == root)
        // FIXME: a dangling object??? (try test-0093 with a debugger)
        return obj;

    return root;
}

void getPtrValues(TValList &dst, const SymHeap &sh, TValId at) {
    TObjList ptrs;
    sh.gatherLivePointers(ptrs, at);
    BOOST_FOREACH(const TObjId obj, ptrs) {
        const TValId val = sh.valueOf(obj);
        if (0 < val)
            dst.push_back(sh.valueOf(obj));
    }
}

void skipObj(const SymHeap &sh, TObjId *pObj, TOffset offNext)
{
    const TValId cursorAt = sh.placedAt(*pObj);
    const TValId rootAt = sh.valRoot(cursorAt);

    // move to the next object
    SymHeap &writable = const_cast<SymHeap &>(sh);
    const TObjId ptr = writable.ptrAt(writable.valByOffset(rootAt, offNext));
    const TValId nextAt = sh.valRoot(sh.valueOf(ptr));

    *pObj = writable.objAt(nextAt);
}

typedef std::pair<TObjId, const cl_initializer *> TInitialItem;

// specialization of TraverseSubObjsHelper suitable for gl initializers
template <> struct TraverseSubObjsHelper<TInitialItem> {
    static const struct cl_type* getItemClt(const SymHeap           &sh,
                                            const TInitialItem      &item)
    {
        const struct cl_type *clt = sh.objType(item.first);
        CL_BREAK_IF(item.second && (!clt || *clt != *item.second->type));
        return clt;
    }

    static TInitialItem getNextItem(const SymHeap                   &sh,
                                    TInitialItem                    item,
                                    int                             nth)
    {
        item.first = sh.subObj(item.first, nth);

        const struct cl_initializer *&initial = item.second;
        if (initial)
            initial = initial->data.nested_initials[nth];

        return item;
    }
};

bool initSingleVariable(SymHeap &sh, const TInitialItem &item) {
    const TObjId obj = item.first;
    const struct cl_type *clt = sh.objType(obj);
    CL_BREAK_IF(!clt);

    const enum cl_type_e code = clt->code;
    switch (code) {
        case CL_TYPE_ARRAY:
            CL_DEBUG("CL_TYPE_ARRAY is not supported by VarInitializer");
            return /* continue */ true;

        case CL_TYPE_UNION:
        case CL_TYPE_STRUCT:
            CL_TRAP;

        default:
            break;
    }

    const struct cl_initializer *initial = item.second;
    if (!initial) {
        // no initializer given, nullify the variable
        sh.objSetValue(obj, /* also equal to VAL_FALSE */ VAL_NULL);
        return /* continue */ true;
    }

    // FIXME: we're asking for troubles this way
    SymBackTrace dummyBt(sh.stor());
    SymProc proc(sh, &dummyBt);

    // resolve initial value
    const struct cl_operand *op = initial->data.value;
    const TValId val = proc.valFromOperand(*op);
    CL_DEBUG("using explicit initializer: obj #"
            << static_cast<int>(obj) << " <-- val #"
            << static_cast<int>(val));

    // set the initial value
    CL_BREAK_IF(VAL_INVALID == val);
    sh.objSetValue(obj, val);

    return /* continue */ true;
}

void initVariable(SymHeap                       &sh,
                  TObjId                        obj,
                  const CodeStorage::Var        &var)
{
    const TInitialItem item(obj, var.initial);

    if (isComposite(var.clt))
        traverseSubObjs(sh, item, initSingleVariable, /* leavesOnly */ true);
    else
        initSingleVariable(sh, item);
}

class PointingObjectsFinder {
    public:
        // we have to use std::set, a vector is not sufficient in all cases
        typedef std::set<TObjId> TResults;

    private:
        TResults results_;

    public:
        const TResults& results() const { return results_; }

        bool operator()(const SymHeap &sh, TObjId obj) {
            const TValId addr = sh.placedAt(obj);
            CL_BREAK_IF(addr <= 0);

            TObjList refs;
            sh.usedBy(refs, addr);
            std::copy(refs.begin(), refs.end(),
                      std::inserter(results_, results_.begin()));

            return /* continue */ true;
        }
};

TObjId subSeekByOffset(
        const SymHeap               &sh,
        const TObjId                obj,
        const TOffset               offToSeek,
        const struct cl_type        *clt,
        const enum cl_type_e        code)
{
    if (obj < 0)
        return obj;

    SymHeap &shNonConst = const_cast<SymHeap &>(sh);
    const TValId addr = sh.placedAt(obj);
    const TValId subAddr = shNonConst.valByOffset(addr, offToSeek);
    CL_BREAK_IF(subAddr <= 0);

    if (clt)
        return shNonConst.objAt(subAddr, clt);
    else
        return shNonConst.objAt(subAddr, code);
}

TObjId ptrObjByOffset(const SymHeap &sh, TObjId obj, TOffset off) {
    return subSeekByOffset(sh, obj, off, /* clt */ 0, CL_TYPE_PTR);
}

TObjId compObjByOffset(const SymHeap &sh, TObjId obj, TOffset off) {
    return subSeekByOffset(sh, obj, off, /* clt */ 0, CL_TYPE_STRUCT);
}

void redirectInboundEdges(
        SymHeap                 &sh,
        const TObjId            pointingFrom,
        const TObjId            pointingTo,
        const TObjId            redirectTo)
{
#ifndef NDEBUG
    const struct cl_type *clt1 = sh.objType(pointingTo);
    const struct cl_type *clt2 = sh.objType(redirectTo);
    CL_BREAK_IF(!clt1 || !clt2 || *clt1 != *clt2);
#endif

    // go through all objects pointing at/inside pointingTo
    TObjList refs;
    sh.pointedBy(refs, sh.placedAt(pointingTo));
    BOOST_FOREACH(const TObjId obj, refs) {
        if (OBJ_INVALID != pointingFrom && pointingFrom != objRoot(sh, obj))
            // pointed from elsewhere, keep going
            continue;

        // check the current link
        const TValId nowAt = sh.valueOf(obj);
        const TOffset offToRoot = sh.valOffset(nowAt);
        const TValId targetAt = sh.placedAt(redirectTo);
        CL_BREAK_IF(sh.valOffset(targetAt));

        // redirect accordingly
        const TValId result = sh.valByOffset(targetAt, offToRoot);
        sh.objSetValue(obj, result);
    }
}
