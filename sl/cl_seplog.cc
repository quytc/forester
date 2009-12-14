/*
 * Copyright (C) 2009 Kamil Dudka <kdudka@redhat.com>
 *
 * This file is part of sl.
 *
 * sl is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * any later version.
 *
 * sl is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sl.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "cl_seplog.hh"

#include "cl_storage.hh"
#include "storage.hh"
#include "symexec.hh"

class ClSepLog: public ClStorageBuilder {
    public:
        ClSepLog(const char *configString);
        virtual ~ClSepLog();

    protected:
        virtual void run(CodeStorage::Storage &);
};

// /////////////////////////////////////////////////////////////////////////////
// ClSepLog implementation
ClSepLog::ClSepLog(const char *) {
    // TODO
}

ClSepLog::~ClSepLog() {
    // TODO
}

void ClSepLog::run(CodeStorage::Storage &stor) {
    CL_DEBUG("looking for 'main()' at gl scope...");
    CodeStorage::Fnc *main = stor.glFncByName["main"];
    if (!main) {
        CL_MSG_STREAM_INTERNAL(cl_error,
                "error: main() not declared at global scope");
        return;
    }

    // run the symbolic execution
    SymExec se(stor);
    se.exec(*main);
}


// /////////////////////////////////////////////////////////////////////////////
// public interface, see cl_seplog.hh for more details
ICodeListener* createClSepLog(const char *configString) {
    return new ClSepLog(configString);
}