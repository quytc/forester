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

#include "jump.hh"

void FI_jmp::execute(ExecutionManager& execMan, const AbstractInstruction::StateType& state) {

	




assert(false);

}

void FI_jmp::finalize(
	const std::unordered_map<const CodeStorage::Block*, AbstractInstruction*>& codeIndex,
	std::vector<AbstractInstruction*>::const_iterator
) {

	this->next_ = this;

	while (this->next_->getType() == fi_type_e::fiJump)
		this->next_ = ((FI_jmp*)this->next_)->getTarget(codeIndex);

	this->next_->setTarget();

}
