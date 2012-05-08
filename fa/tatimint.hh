/*
 * Copyright (C) 2010 Jiri Simacek
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

#ifndef TA_TIM_INT_H
#define TA_TIM_INT_H

#include <string>
#include <sstream>
#include <map>

#include "timbuk.hh"
#include "treeaut.hh"
#include "utils.hh"

using std::string;

class TAReader : public TimbukReader {

	TA<string>* dst;
	string name;

protected:

	virtual void newLabel(const string&, size_t, size_t) {}
	
	virtual void beginModel(const string& name) {
		this->dst->clear();
		this->name = name;
	}
	
	virtual void newState(const string&, size_t) {}
	
	virtual void newFinalState(size_t id) {
		this->dst->addFinalState(id);
	}
	
	virtual void endDeclaration() {}

	virtual void newTransition(const vector<size_t>& lhs, size_t label, size_t rhs) {
		this->dst->addTransition(lhs, this->getLabelName(label), rhs);
	}
	
	virtual void endModel() {}
	
public:

	TAReader(std::istream& input = std::cin, const string& name = "")
		: TimbukReader(input, name), dst(NULL) {}
	
	TA<string>& read(TA<string>& dst) {
		this->dst = &dst;
		this->readOne();
		return dst;
	}

	void readFirst(TA<string>& dst, string& name) {
		this->dst = &dst;
		TimbukReader::readFirst();
		name = this->name;
	}

	bool readNext(TA<string>& dst, string& name) {
		this->dst = &dst;
		if (!TimbukReader::readNext())
			return false;
		name = this->name;
		return true;
	}

};

class TAMultiReader : public TimbukReader {

	TA<string>::Backend& backend;

public:

	std::vector<TA<std::string> > automata;
	std::vector<std::string> names;

protected:

	virtual void newLabel(const string&, size_t, size_t) {}
	
	virtual void beginModel(const string& name) {
		this->automata.push_back(TA<string>(this->backend));
		this->names.push_back(name);
	}
	
	virtual void newState(const string&, size_t) {}
	
	virtual void newFinalState(size_t id) {
		this->automata.back().addFinalState(id);
	}
	
	virtual void endDeclaration() {}

	virtual void newTransition(const vector<size_t>& lhs, size_t label, size_t rhs) {
		this->automata.back().addTransition(lhs, this->getLabelName(label), rhs);
	}
	
	virtual void endModel() {}
	
public:

	TAMultiReader(TA<string>::Backend& backend, std::istream& input = std::cin, const string& name = "")
		: TimbukReader(input, name), backend(backend) {}

	void clear() {
		this->automata.clear();
		this->names.clear();
	}

	void read() {
		this->readAll();
	}

};

template <class T>
class TAWriter : public TimbukWriter {

	struct StdF {

		std::string operator()(size_t s) {
			std::ostringstream ss;
			ss << 'q' << s;
			return ss.str();
		}

	};

public:

	TAWriter(std::ostream& output = std::cout) : TimbukWriter(output) {}

	template <class F>
	void writeTransitions(const TA<T>& aut, F f) {
		for (typename TA<T>::iterator i = aut.begin(); i != aut.end(); ++i) {
			std::ostringstream ss;
			ss << i->label();
//                      std::cerr << i->label();
			this->writeTransition(i->lhs(), ss.str(), i->rhs(), f);
			this->endl();
//        std::cerr << "-------------tree automata-------------------" << i->lhs() << std::endl;                
		}
       //  std::cerr << "-------------tree automata-------------------" << *aut;

	}

	void writeTransitions(const TA<T>& aut) {
  //              std::cerr << "-------------tree automata-------------------" << aut;
		for (typename TA<T>::iterator i = aut.begin(); i != aut.end(); ++i) {
			std::ostringstream ss;
			ss << i->label();
			this->writeTransition(i->lhs(), ss.str(), i->rhs());
			this->endl();
		}
	}

	template <class F>
	void writeOne(const TA<T>& aut, F f, const string& name = "TreeAutomaton") {
    //            std::cerr << "-------------tree automata-------------------" << aut;
		std::map<string, size_t> labels;
		std::set<size_t> states;
		for (typename TA<T>::iterator i = aut.begin(); i != aut.end(); ++i) {
			std::ostringstream ss;
			ss << i->label();
			labels.insert(std::make_pair(ss.str(), i->lhs().size()));
			states.insert(i->rhs());
			for (size_t j = 0; j < i->lhs().size(); ++j)
				states.insert(i->lhs()[j]);
		}
		this->startAlphabet();
		for (std::map<std::string, size_t>::iterator i = labels.begin(); i != labels.end(); ++i)
			this->writeLabel(i->first, i->second);
		this->endl();
		this->newModel(name);
		this->endl();
		this->startStates();
		for (set<size_t>::iterator i = states.begin(); i != states.end(); ++i)
			this->writeState(*i, f);
		this->endl();
		this->startFinalStates();
		for (set<size_t>::iterator i = aut.getFinalStates().begin(); i != aut.getFinalStates().end(); ++i)
			this->writeState(*i, f);
		this->endl();
		this->startTransitions();
		this->endl();
		this->writeTransitions(aut, f);
	}
	
	void writeOne(const TA<T>& aut, const string& name = "TreeAutomaton") {
		std::map<string, size_t> labels;
		std::set<size_t> states;
		for (typename TA<T>::iterator i = aut.begin(); i != aut.end(); ++i) {
			std::ostringstream ss;
			ss << i->label();
			labels.insert(std::make_pair(ss.str(), i->lhs().size()));
			states.insert(i->rhs());
			for (size_t j = 0; j < i->lhs().size(); ++j)
				states.insert(i->lhs()[j]);
		}
		this->startAlphabet();
		for (std::map<string, size_t>::iterator i = labels.begin(); i != labels.end(); ++i)
			this->writeLabel(i->first, i->second);
		this->endl();
		this->newModel(name);
		this->endl();
		this->startStates();
		for (std::set<size_t>::iterator i = states.begin(); i != states.end(); ++i)
			this->writeState(*i);
		this->endl();
		this->startFinalStates();
		for (std::set<size_t>::iterator i = aut.getFinalStates().begin(); i != aut.getFinalStates().end(); ++i)
			this->writeState(*i);
		this->endl();
		this->startTransitions();
		this->endl();
		this->writeTransitions(aut);
	}

};

#endif
