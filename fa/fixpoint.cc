/*
 * Copyright (C) 2011 Jiri Simacek
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

#include <ostream>

#include <cl/storage.hh>
#include <cl/cl_msg.hh>
#include "../cl/ssd.h"

#include "treeaut.hh"
#include "forestautext.hh"
#include "ufae.hh"
#include "executionmanager.hh"
#include "virtualmachine.hh"
#include "folding.hh"
#include "abstraction.hh"
#include "normalization.hh"
#include "splitting.hh"
#include "utils.hh"
#include "regdef.hh"

#include "fixpoint.hh"

using namespace ssd;

struct ExactTMatchF {
	bool operator()(const TT<label_type>& t1, const TT<label_type>& t2) {
		return t1.label() == t2.label();
	}
};

struct SmartTMatchF {
	bool operator()(const TT<label_type>& t1, const TT<label_type>& t2) {
		if (t1.label()->isNode() && t2.label()->isNode())
			return t1.label()->getTag() == t2.label()->getTag();
		return t1.label() == t2.label();
	}
};

struct SmarterTMatchF {
	bool operator()(const TT<label_type>& t1, const TT<label_type>& t2) {
		if (t1.label()->isNode() && t2.label()->isNode()) {
			if (t1.label()->getTag() != t2.label()->getTag())
				return false;
			std::vector<size_t> tmp;
			for (std::vector<size_t>::const_iterator i = t1.lhs().begin(); i != t1.lhs().end(); ++i) {
				if (FA::isData(*i))
					tmp.push_back(*i);
			}
			size_t i = 0;
			for (std::vector<size_t>::const_iterator j = t2.lhs().begin(); j != t2.lhs().end(); ++j) {
				if (FA::isData(*j)) {
					if ((i >= tmp.size()) || (*j != tmp[i++]))
						return false;
				}
			}
			return (i == tmp.size());
		}
		return t1.label() == t2.label();
	}
};

struct CompareVariablesF {
	bool operator()(size_t i, const TA<label_type>& ta1, const TA<label_type>& ta2) {
		if (i)
			return true;
		const TT<label_type>& t1 = ta1.getAcceptingTransition();
		const TT<label_type>& t2 = ta2.getAcceptingTransition();
		return (t1.label() == t2.label()) && (t1.lhs() == t2.lhs());
	}
};

struct FuseNonZeroF {
	bool operator()(size_t root, const FAE*) {
		return root != 0;
	}
};

inline bool normalizeAndFold(FAE& fae, BoxMan& boxMan,ExecutionManager& execMan, std::vector<FAE>& faeList) {
//        CL_DEBUG_AT(1, "before normalization: " << std::endl << fae);
          FAE inputFae = fae; 
  //      std::cerr << ".......................before normalization and fold.............................. " << fae << std::endl;
	std::set<size_t> tmp;

	VirtualMachine vm(fae);

	Normalization norm(fae);

	Folding folding(fae, boxMan);

	const Data& abp = vm.varGet(ABP_INDEX);

	std::vector<size_t> order;
	std::vector<bool> marked;

//	fae.unreachableFree();

	fae.updateConnectionGraph();

//	vm.getNearbyReferences(abp.d_ref.root, tmp);

//        std::cerr << ".......................before normalization.............................. " << fae << std::endl;
	norm.scan(marked, order);
//	norm.normalize(marked, order);
//        std::cerr << "......................after normalization.............................. " << fae << std::endl;
//	CL_CDEBUG(3, "after normalization: " << std::endl << fae);

	tmp.clear();

//	vm.getNearbyReferences(abp.d_ref.root, tmp);

//	norm.scan(marked, order);

	// folding
        
	bool matched = false;

	// do not touch root 0
	tmp.insert(abp.d_ref.root);

	std::unordered_map<Box, std::set<size_t>, boost::hash<Box>> cache;

	std::vector<std::shared_ptr<const Box>> boxes;
//        CL_DEBUG_AT(1, "each comp: " << std::endl << *fae.roots[0]);
	// never fold at root 0
	for (size_t i = 1; i < order.size(); ++i) {

		assert(fae.roots[order[i]]);
          //      CL_DEBUG_AT(1, "folding at each comp: " << std::endl << *fae.roots[i]);
		if (folding.discover(order[i], tmp, &boxes)) {

			matched = true;

			continue;

		}
//                std::cerr << "before going to boxes" << std::endl;
		for (auto& aBox : boxes) {
  //                     std::cerr << "inside the for loop of boxes: ";// << *boxMan.getBox(*aBox) << std::endl;
			auto iter = cache.insert(std::make_pair(*aBox, std::set<size_t>())).first;

			iter->second.insert(order[i]);

			if (iter->second.count(order[i - 1])) {

				auto newBox = boxMan.getBox(*aBox);

				CL_DEBUG_AT(1, "learned " << *(AbstractBox*)newBox << ":" << std::endl << *newBox);
//std::cerr << "learned " << *(AbstractBox*)newBox << ":" << std::endl << *newBox;
				for (auto& j : iter->second)
					folding.discover(j, tmp);

				matched = true;

				cache.erase(iter);

			}

		}

		boxes.clear();

	}

	CL_DEBUG_AT(1, "after folding: " << std::endl << fae);
        
	vm.getNearbyReferences(abp.d_ref.root, tmp);

	norm.scan(marked, order, tmp);
	norm.normalize(marked, order);

        FAE outputFae = fae;
	CL_DEBUG_AT(1, "after normalization: " << std::endl << fae);
        //std::cerr << ".......................After normalization.............................. " << fae << std::endl;
	if(matched){
      //  std::cerr << "-----------------------------------Normanization and Fold....................................." << std::endl << outputFae << std::endl;
         //CL_DEBUG_AT(1, "Available Boxes: "<< *(AbstractBox*)&box << ':' << std::endl << box);
        //     std::cerr << "Available Boxes: "<< *(AbstractBox*)&box << ':' << std::endl << box;
       
            execMan.absFAEs.push_back(outputFae);
       }
        return matched;

}

inline bool testInclusion(FAE& fae, TA<label_type>& fwdConf, UFAE& fwdConfWrapper) {

	TA<label_type> ta(*fwdConf.backend);
	Index<size_t> index;

	fwdConfWrapper.fae2ta(ta, index, fae);

//	CL_DEBUG_AT(1,"challenge" << std::endl << ta);
//	CL_DEBUG_AT(1,"response" << std::endl << fwdConf);

	if (TA<label_type>::subseteq(ta, fwdConf))
		return true;

	CL_CDEBUG(1, "extending fixpoint with:" << std::endl << fae);

	fwdConfWrapper.join(ta, index);

	ta.clear();

	fwdConf.minimized(ta);
	fwdConf = ta;

	return false;

}

inline void abstract(FAE& fae, TA<label_type>& fwdConf, TA<label_type>::Backend& backend, BoxMan& boxMan) {
   //     std::cerr << "before abstraction: " << fae << std::endl;
	fae.unreachableFree();

//	CL_CDEBUG(1, SSD_INLINE_COLOR(C_LIGHT_GREEN, "after normalization:" ) << std::endl << *fae);

	// merge fixpoint
	std::vector<FAE*> tmp;

	ContainerGuard<std::vector<FAE*> > g(tmp);

	FAE::loadCompatibleFAs(
		tmp, fwdConf, backend, boxMan, &fae, 0, CompareVariablesF()
	);

	for (size_t i = 0; i < tmp.size(); ++i)
		CL_CDEBUG(3, "accelerator " << std::endl << *tmp[i]);

	fae.fuse(tmp, FuseNonZeroF());

//	fae.fuse(target->fwdConf, FuseNonZeroF());

	CL_CDEBUG(3, "fused " << std::endl << fae);

	// abstract
//	CL_CDEBUG("abstracting ... " << 1);

	Abstraction abstraction(fae);

	for (size_t i = 1; i < fae.getRootCount(); ++i)
               {// CL_DEBUG_AT(1, "abstraction root count: " <<i << std::endl);
		abstraction.heightAbstraction(i, 1, SmartTMatchF());
               }  
	fae.unreachableFree();

//	std::cerr << "after abstraction: " << fae << std::endl;
}

// FI_fix
void FI_abs::execute(ExecutionManager& execMan, const AbstractInstruction::StateType& state) {
         SymState* s = state.second;
         std::vector<FAE> faeList;
         faeList.clear();
       // std::cerr << "Micro" << *state.second->instr << std::endl;
	std::shared_ptr<FAE> fae = std::shared_ptr<FAE>(new FAE(*state.second->fae));
        execMan.avaiBoxes.clear(); 
	normalizeAndFold(*fae, this->boxMan, execMan, faeList);
         
	do {
                abstract(*fae, this->fwdConf, this->taBackend, this->boxMan);
                 execMan.absFAEs.push_back(*fae);
               /* execMan.avaiBoxes.clear();
                for (auto& box : this->boxMan.getBoxes()){
                  std::ostringstream ss;
                  ss << *(AbstractBox*)&box << ':' << std::endl << box;
                  execMan.avaiBoxes.push_back(ss.str());
                 }*/
	} while (normalizeAndFold(*fae, this->boxMan,execMan, faeList));       
   	// test inclusion
	fae->unreachableFree();

	if (testInclusion(*fae, this->fwdConf, this->fwdConfWrapper)) {

		CL_CDEBUG(3, "hit");

		execMan.traceFinished(state.second);

	} else {
 		execMan.enqueue(state.second, state.first, fae, this->next_);

	}
            execMan.avaiBoxes = {};
            for (auto& box : boxMan.getBoxes()){
            std::ostringstream ss;
            ss << *(AbstractBox*)&box << ':' << std::endl << box;
            execMan.avaiBoxes.push_back(ss.str());
            }

 }

// FI_fix
void FI_fix::execute(ExecutionManager& execMan, const AbstractInstruction::StateType& state) {
      // std::cerr << "fix statement------------------------------------------" << *state.second->instr << std::endl; 
       // CL_DEBUG_AT(1, "fix statement ");
	std::shared_ptr<FAE> fae = std::shared_ptr<FAE>(new FAE(*state.second->fae));
        std::vector<FAE> faeList1;
	normalizeAndFold(*fae, this->boxMan,execMan,faeList1);

	if (testInclusion(*fae, this->fwdConf, this->fwdConfWrapper)) {

		CL_CDEBUG(3, "hit");

		execMan.traceFinished(state.second);

	} else {

		execMan.enqueue(state.second, state.first, fae, this->next_);

	}

}
