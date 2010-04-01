/*
 * Copyright (C) 2009 Kamil Dudka <kdudka@redhat.com>
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

#include "cld_uniregs.hh"
#include "cld_optrans.hh"
#include "relocator.hh"

class CldUniRegs: public CldOpTransBase {
    public:
        CldUniRegs(ICodeListener *slave);

        virtual void fnc_open(
            const struct cl_operand *fnc)
        {
            reloc_.reset();
            CldOpTransBase::fnc_open(fnc);
        }

    private:
        Relocator<int, int> reloc_;

    protected:
        virtual void modifyOperand(struct cl_operand *);
};

CldUniRegs::CldUniRegs(ICodeListener *slave):
    CldOpTransBase(slave),
    reloc_(1)
{
}

void CldUniRegs::modifyOperand(struct cl_operand *op) {
    if (CL_OPERAND_REG != op->code)
        return;

    op->data.reg.id = reloc_.lookup(op->data.reg.id);
}


// /////////////////////////////////////////////////////////////////////////////
// public interface, see cld_uniregs.hh for more details
ICodeListener* createCldUniRegs(ICodeListener *slave) {
    return new CldUniRegs(slave);
}