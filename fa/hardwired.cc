/*
 * Copyright (C) 2012 Jiri Simacek
 *
 * This file is part of forester.
 *
 * forester is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * any later version.
 *
 * forester is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with forester.  If not, see <http://www.gnu.org/licenses/>.
 */

// Standard library headers
#include <vector>
#include <unordered_map>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <ctime>
#include <cstdlib>
#include <signal.h>

// Boost headers
#include <boost/algorithm/string.hpp>

// Forester headers
#include "symexec.hh"
#include "programerror.hh"
#include "notimpl_except.hh"
#include "compiler.hh"

#include "microcode.hh"
#include "jump.hh"
#include "call.hh"
#include "fixpoint.hh"
#include "comparison.hh"

SymExec se;

void clEasyRun(const CodeStorage::Storage&, const char*) {}

int main(int, char*[]) {

	TA<label_type>::Backend backend;

	BoxMan boxMan;

	cl_global_init_defaults("hardwired", 3);

    try {

		Compiler::Assembly assembly;

		// labels
		std::unordered_map<const CodeStorage::Block*, AbstractInstruction*> codeIndex;

		// set the number of temporary registers
		assembly.regFileSize_ = 4;

		const TypeBox* typeStack = boxMan.createTypeInfo("Stack", {});
		const TypeBox* typeT = boxMan.createTypeInfo("T", { 0 });

		assembly.code_ = {
			// create ABP (we don't need it but verifier expects that it exists)
			new FI_load_cst(nullptr, 0, Data::createVoidPtr(0)),// 00:	mov		r0, (void_ptr)0
			new FI_node_create(
				nullptr, 0, 0, 0, typeStack, {}
			),													// 01:	node	r0, r0
			new FI_push_greg(nullptr, 0),						// 02:	push	r0
			// real work starts here
			// x = (int)0;
			new FI_load_cst(nullptr, 1, Data::createInt(0)),	// 03:	mov		r3, (unknw)
			new FI_push_greg(nullptr, 1),						// 04:	push	r1
			// r3 = (unknw);
			new FI_load_cst(nullptr, 3, Data::createUnknw()),	// 05:	mov		r3, (unknw)
			// while (*) {
			new FI_abs(nullptr, backend, backend, boxMan),		// 06:	abs
			new FI_eq(0, 3, 3),									// 07:	eq		r0, r3, r3
			nullptr, // placeholder								// 08:	cjmp	r0, @16, @09
			//   y = malloc(4);
			new FI_load_cst(nullptr, 1, Data::createInt(4)),	// 09:	mov		r1, (int)4
			new FI_alloc(nullptr, 1, 1),						// 10:	alloc	r1, r1
			new FI_node_create(
				nullptr, 1, 1, 4, typeT, { SelData(0, 4, 0) }
			),													// 11:	node	r1, r1
			//   y->next = x;
			new FI_get_greg(nullptr, 2, 1),						// 12:	mov		r2, gr1
			new FI_store(nullptr, 1, 2, 0),						// 13:	mov		[r1 + 0], r2
			//   x = y;
			new FI_set_greg(nullptr, 1, 1),						// 14:  mov		gr1, r1
			// }
			new FI_jmp(nullptr, (const CodeStorage::Block*)5),	// 15:	jmp		@06
			// r3 = (int)0;
			new FI_load_cst(nullptr, 3, Data::createInt(0)),	// 16:	mov		r3, (int)0
			// while (x) {
			new FI_abs(nullptr, backend, backend, boxMan),		// 17:	abs
			new FI_get_greg(nullptr, 0, 1),						// 18:	mov		r0, gr1
			new FI_eq(0, 0, 3),									// 19:	eq		r0, r0, r3
			nullptr, // placeholder								// 20:	cjmp	r0, @28, @21
			//   y = x
			new FI_get_greg(nullptr, 1, 1),						// 21:	mov		r1, gr1
			//   x = x->next
			new FI_acc_sel(nullptr, 1, 0),						// 22:	acc		[r1 + 0]
			new FI_load(nullptr, 0, 1, 0),						// 23:	mov		r0, [r1 + 0]
			new FI_set_greg(nullptr, 1, 0),						// 24:	mov		gr1, r0
			//   free(y)
			new FI_acc_all(nullptr, 1),							// 25:	acca	[r1]
			new FI_node_free(nullptr, 1),						// 26:	free	r1
			// }
			new FI_jmp(nullptr, (const CodeStorage::Block*)16),	// 27:	jmp		@17
			// check garbage
			new FI_check(nullptr),								// 28:	check
			// terminate
			new FI_abort(nullptr)								// 29:	abort
		};

		// fill placeholders
		assembly.code_[8] = new FI_cond(nullptr, 0, { assembly.code_[16], assembly.code_[9] });
		assembly.code_[20] = new FI_cond(nullptr, 0, { assembly.code_[28], assembly.code_[21] });

		// setup jumps
		for (size_t i = 0; i < assembly.code_.size(); ++i)
			codeIndex.insert(std::make_pair((const CodeStorage::Block*)i, assembly.code_[i]));

		// finalize
		for (auto i = assembly.code_.begin(); i != assembly.code_.end(); ++i)
			(*i)->finalize(codeIndex, i);

		CL_DEBUG("assembly: " << std::endl << assembly);

		se.run(assembly);

		CL_NOTE("the program is safe ...");

	} catch (const ProgramError& e) {

		if (e.location())
			CL_ERROR_MSG(e.location(), e.what());
		else
			CL_ERROR(e.what());

	} catch (const NotImplementedException& e) {

		if (e.location())
			CL_ERROR_MSG(e.location(), "not implemented: " + std::string(e.what()));
		else
			CL_ERROR("not implemented: " + std::string(e.what()));

	} catch (const std::exception& e) {

		CL_ERROR(e.what());

	}

	cl_global_cleanup();

	return 0;

}
