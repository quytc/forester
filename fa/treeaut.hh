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

#ifndef TREE_AUT_H
#define TREE_AUT_H

#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <cassert>
#include <stdexcept>

#include <boost/unordered_map.hpp>

#include "cache.hh"
#include "utils.hh"
#include "lts.hh"

using std::vector;
using std::set;
using std::map;
using std::pair;
using std::make_pair;

using boost::hash_value;
using boost::unordered_map;

template <class T> class TA;

template <class T>
class TT {

	friend class TA<T>;

public:

	typedef Cache<vector<size_t> > lhs_cache_type;

private:

	mutable lhs_cache_type& lhsCache;

public:

	lhs_cache_type::value_type* _lhs;
	T _label;
	size_t _rhs;

	TT(const TT& transition)
		: lhsCache(transition.lhsCache), _label(transition._label) {
		this->_lhs = this->lhsCache.lookup(transition._lhs->first);
//		this->_label = transition._label;
		this->_rhs = transition._rhs;
	}

	TT(const vector<size_t>& lhs, const T& label, size_t rhs, lhs_cache_type& lhsCache)
		: lhsCache(lhsCache), _label(label) {
		this->_lhs = this->lhsCache.lookup(lhs);
//		this->_label = label;
		this->_rhs = rhs;
	}
	
	TT(const vector<size_t>& lhs, const T& label, size_t rhs, const vector<size_t>& index, lhs_cache_type& lhsCache)
		: lhsCache(lhsCache), _label(label) {
		vector<size_t> tmp(lhs.size());
		for (size_t i = 0; i < lhs.size(); ++i)
			tmp[i] = index[lhs[i]];
		this->_lhs = this->lhsCache.lookup(tmp);
//		this->_label = label;
		this->_rhs = index[rhs];
	}

	TT(const TT& transition, lhs_cache_type& lhsCache)
		: lhsCache(lhsCache), _label(transition._label) {
		this->_lhs = this->lhsCache.lookup(transition._lhs->first);
//		this->_label = transition._label;
		this->_rhs = transition._rhs;
	}
  
	TT(const TT& transition, const vector<size_t>& index, lhs_cache_type& lhsCache)
		: lhsCache(lhsCache), _label(transition._label) {
		vector<size_t> tmp(transition._lhs->first.size());
		for (size_t i = 0; i < transition._lhs->first.size(); ++i)
			tmp[i] = index[transition._lhs->first[i]];
		this->_lhs = this->lhsCache.lookup(tmp);
//		this->_label = transition._label;
		this->_rhs = index[transition._rhs];
	}

	~TT() { this->lhsCache.release(this->_lhs);	}

	const vector<size_t>& lhs() const { return this->_lhs->first; }
	const T& label() const { return this->_label; }
	size_t rhs() const { return this->_rhs; }
	
	bool operator==(const TT& rhs) const {
		return (this->_label == rhs._label) && (this->_lhs == rhs._lhs) && (this->_rhs == rhs._rhs);
	}

	bool operator<(const TT& rhs) const {
		return (this->_rhs < rhs._rhs) || (
			(this->_rhs == rhs._rhs) && (
				(this->_label < rhs._label) || (
					(this->_label == rhs._label) && (
						this->_lhs->first < rhs._lhs->first
					)
				)
			)
		);
	}
/*
	bool operator<(const TT& rhs) const {
		return (this->_label < rhs._label) || (
			(this->_label == rhs._label) && (
				(this->_lhs->first < rhs._lhs->first) || (
					(this->_lhs == rhs._lhs) && (
						this->_rhs < rhs._rhs
					)
				)
			)
		);
		return (this->_lhs->first < rhs._lhs->first) || (
			(this->_lhs->first == rhs._lhs->first) && (
				(this->_label < rhs._label) || (
					(this->_label == rhs._label) && (
						this->_rhs < rhs._rhs
					)
				)
			)
		);
	}
*/	
	friend size_t hash_value(const TT& t) {
		return hash_value(hash_value(hash_value(t._lhs) + hash_value(t._label)) + hash_value(t._rhs));
	}
	
	friend std::ostream& operator<<(std::ostream& os, const TT& t) {
		os << t._label << '(';
		if (t._lhs->first.size() > 0) {
			os << t._lhs->first[0];
			for (size_t i = 1; i < t._lhs->first.size(); ++i)
				os << ',' << t._lhs->first[i];
		}
		return os << ")->" << t._rhs;
	}

};

template <class T>
class TA {

//	friend template <class U> class TAManager<T>;

public:

    typedef Cache<TT<T> > trans_cache_type;

	// this is the place where transitions are stored
	struct Backend {

		typename TT<T>::lhs_cache_type lhsCache;
		trans_cache_type transCache;

	};

	mutable Backend* backend;
	
	typename TT<T>::lhs_cache_type& lhsCache() const { return this->backend->lhsCache; }

	trans_cache_type& transCache() const { return this->backend->transCache; }

	class Iterator {
		typename set<typename trans_cache_type::value_type*>::const_iterator _i;
	public:
		Iterator(typename set<typename trans_cache_type::value_type*>::const_iterator i) : _i(i) {}

		Iterator& operator++() { return ++this->_i, *this; }

		Iterator operator++(int) { return Iterator(this->_i++); }

		const TT<T>& operator*() const { return (*this->_i)->first; }

		const TT<T>* operator->() const { return &(*this->_i)->first; }

		bool operator==(const Iterator& rhs) const { return this->_i == rhs._i; }

		bool operator!=(const Iterator& rhs) const { return this->_i != rhs._i; }

	};

public:

	typedef typename boost::unordered_map<size_t, std::vector<const TT<T>*> > td_cache_type;

	class TDIterator {
		
		const td_cache_type& _cache;
		set<size_t> _visited;
		vector<pair<typename vector<const TT<T>*>::const_iterator, typename vector<const TT<T>*>::const_iterator> > _stack;
	
		void insertLhs(const vector<size_t>& lhs) {
			for (vector<size_t>::const_iterator i = lhs.begin(); i != lhs.end(); ++i) {
				if (this->_visited.insert(*i).second) {
					typename td_cache_type::const_iterator j = this->_cache.find(*i);
					if (j != this->_cache.end())
						this->_stack.push_back(make_pair(j->second.begin(), j->second.end()));
				}
			}
		}
		
	public:
		TDIterator(const td_cache_type& cache, const vector<size_t>& stack)
			: _cache(cache), _visited() {
			this->insertLhs(stack);
		}
		
		bool isValid() const { return !this->_stack.empty(); }
		
		bool next() {
			size_t oldSize = this->_stack.size();
			this->insertLhs((*this->_stack.back().first)->_lhs->first);
			// if something changed then we have a new "working" item on the top of the stack
			if (this->_stack.size() != oldSize)
				return true;
			do {
				++this->_stack.back().first;
				// is there something to process ?
				if (this->_stack.back().first != this->_stack.back().second)
					return true;
				// discard processed queue
				this->_stack.pop_back();
			} while (!this->_stack.empty());
			// nothing else remains
			return false;
		}
		
		const TT<T>& operator*() const { return **this->_stack.back().first; }

		const TT<T>* operator->() const { return *this->_stack.back().first; }

	};

	typedef typename boost::unordered_map<size_t, std::vector<const TT<T>*> > bu_cache_type;

	typedef boost::unordered_map<T, std::vector<const TT<T>*> > lt_cache_type;
//	typedef boost::unordered_map<size_t, lt_cache_type> slt_cache_type;

public:

	typedef Iterator iterator;
	typedef TDIterator td_iterator;

public:

//	int labels;
	size_t next_state;
	size_t maxRank;

	struct CmpF {
		bool operator()(typename trans_cache_type::value_type* lhs, typename trans_cache_type::value_type* rhs) {
			return lhs->first < rhs->first;
		}
	};

	typedef std::set<typename trans_cache_type::value_type*, CmpF> trans_set_type;

	trans_set_type transitions;
	std::set<size_t> finalStates;
	
//	std::map<const std::vector<int>*, int> lhsMap;

public:

	TA(Backend& backend) : backend(&backend), next_state(0), maxRank(0) {}
	
	TA(const TA<T>& ta, bool copyFinalStates = true) : backend(ta.backend), next_state(ta.next_state), maxRank(ta.maxRank), transitions(ta.transitions) {
		for (typename std::set<typename trans_cache_type::value_type*>::iterator i = this->transitions.begin(); i != this->transitions.end(); ++i)
			this->transCache().addRef(*i);
		if (copyFinalStates)
			this->finalStates = ta.finalStates;
	}
	
	~TA() { this->clear(); }

	typename TA<T>::Iterator begin() const { return typename TA<T>::Iterator(this->transitions.begin()); }
	typename TA<T>::Iterator end() const { return typename TA<T>::Iterator(this->transitions.end()); }

	typename TA<T>::TDIterator tdStart(const td_cache_type& cache) const {
		return typename TA<T>::TDIterator(cache, vector<size_t>(this->finalStates.begin(), this->finalStates.end()));
	}

	typename TA<T>::TDIterator tdStart(const td_cache_type& cache, const vector<size_t>& stack) const {
		return typename TA<T>::TDIterator(cache, stack);
	}

	TA<T>& operator=(const TA<T>& rhs) {
		this->clear();
		this->next_state = rhs.next_state;
		this->maxRank = rhs.maxRank;
		this->backend = rhs.backend;
		this->transitions = rhs.transitions;
		this->finalStates = rhs.finalStates;
		for (typename set<typename trans_cache_type::value_type*>::iterator i = this->transitions.begin(); i != this->transitions.end(); ++i)
			this->transCache().addRef(*i);
		return *this;
	}

	void clear() {
		this->maxRank = 0;
		this->next_state = 0;
		for (typename set<typename trans_cache_type::value_type*>::iterator i = this->transitions.begin(); i != this->transitions.end(); ++i)
			this->transCache().release(*i);
		this->transitions.clear();
		this->finalStates.clear();
	}
/*
	void loadFromDFS(const TA<T>::dfs_cache_type& dfsCache, const TA<T>& ta, const vector<size_t>& stack, bool registerFinalStates = true) {
		for (TA<T>::dfs_iterator i = ta.dfsStart(dfsCache, stack); i.isValid(); i.next())
			this->addTransition(*i);
		if (registerFinalStates)
			this->addFinalStates(stack);
	}
*/	
	size_t newState() { return this->next_state++; }
	
	void updateStateCounter() {
		this->next_state = 0;
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = this->transitions.begin(); i != this->transitions.end(); ++i)
			this->next_state = std::max(this->next_state, 1 + std::max((*i)->first._rhs, *std::max_element((*i)->first._lhs->first.begin(), (*i)->first._lhs->first.end())));
	}
	
	void buildStateIndex(Index<size_t>& index) const {
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = this->transitions.begin(); i != this->transitions.end(); ++i) {
			for (vector<size_t>::const_iterator j = (*i)->first._lhs->first.begin(); j != (*i)->first._lhs->first.end(); ++j)
				index.add(*j);
			index.add((*i)->first._rhs);
		}
		for (set<size_t>::const_iterator i = this->finalStates.begin(); i != this->finalStates.end(); ++i)
			index.add(*i);
	}

	void buildSortedStateIndex(Index<size_t>& index) const {
		std::set<size_t> s;
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = this->transitions.begin(); i != this->transitions.end(); ++i) {
			for (std::vector<size_t>::const_iterator j = (*i)->first._lhs->first.begin(); j != (*i)->first._lhs->first.end(); ++j)
				s.insert(*j);
			s.insert((*i)->first._rhs);
		}
		s.insert(this->finalStates.begin(), this->finalStates.end());
		for (std::set<size_t>::iterator i = s.begin(); i != s.end(); ++i)
			index.add(*i);
	}

	void buildLabelIndex(Index<T>& index) const {
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = this->transitions.begin(); i != this->transitions.end(); ++i)
			index.add((*i)->first._label);
	}
/*
	void buildIndex(Index<T>& stateIndex, Index<T>& labelIndex) const {
		stateIndex.clear();
		labelIndex.clear();
		for (set<trans_cache_type::value_type*>::const_iterator i = this->transitions.begin(); i != this->transitions.end(); ++i) {
			for (vector<size_t>::const_iterator j = (*i)->first._lhs->first.begin(); j != (*i)->first._lhs->first.end(); ++j)
				stateIndex.add(*j);
			labelIndex.add((*i)->first._label);
			stateIndex.add((*i)->first._rhs);
		}
	}
*/
	void buildLhsIndex(Index<const std::vector<size_t>*>& index) const {
		for (typename std::set<typename trans_cache_type::value_type*>::iterator i = this->transitions.begin(); i != this->transitions.end(); ++i)
			index.add(&(*i)->first._lhs->first);
	}
	
	void buildTDCache(td_cache_type& cache) const {
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = this->transitions.begin(); i != this->transitions.end(); ++i)
			cache.insert(make_pair((*i)->first._rhs, vector<const TT<T>*>())).first->second.push_back(&(*i)->first);
	}

	void buildBUCache(bu_cache_type& cache) const {
		boost::unordered_set<size_t> s;
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = this->transitions.begin(); i != this->transitions.end(); ++i) {
			s.clear();
			for (std::vector<size_t>::const_iterator j = (*i)->first._lhs->first.begin(); j != (*i)->first._lhs->first.end(); ++j) {
				if (s.insert(*j).second)
					cache.insert(make_pair(*j, vector<const TT<T>*>())).first->second.push_back(&(*i)->first);
			}
		}
	}
/*	
	void buildSLTBUCache(slt_cache_type& cache, leaf_cache_type& leafCache) const {
		boost::unordered_map<std::pair<size_t, const T*>, std::set<const TT<T>*> > tmp;
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = this->transitions.begin(); i != this->transitions.end(); ++i) {
			if ((*i)->first._lhs->first.empty()) {
				leafCache.insert(make_pair(&(*i)->first._label, std::set<const TT<T>*>())).first->second.insert(&(*i)->first);
				continue;
			}
			for (std::vector<size_t>::const_iterator j = (*i)->first._lhs->first.begin(); j != (*i)->first._lhs->first.end(); ++j)
				tmp.insert(make_pair(make_pair(*j, &(*i)->first._label), vector<const TT<T>*>())).first->second.insert(&(*i)->first);
		}
		for (boost::unordered_map<std::pair<size_t, const T*>, std::set<const TT<T>*> >::const_iterator i = tmp.begin(); i != tmp.end(); ++i) {
			cache.insert(
				make_pair(i->first.first, boost::unordered_map<const T*, std::vector<const TT<T>*> >())
			).first->second.insert(
				make_pair(i->first.second, std::vector<const TT<T>*>(i->second.begin(), i->second.end()))
			);
		}
	}
*/	
	void buildLTCache(lt_cache_type& cache) const {
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = this->transitions.begin(); i != this->transitions.end(); ++i)
			cache.insert(make_pair((*i)->first._label, std::vector<const TT<T>*>())).first->second.push_back(&(*i)->first);
	}

	typename trans_cache_type::value_type* addTransition(const vector<size_t>& lhs, const T& label, size_t rhs) {
		if (lhs.size() > this->maxRank)
			this->maxRank = lhs.size();
		typename trans_cache_type::value_type* x = this->transCache().lookup(TT<T>(lhs, label, rhs, this->lhsCache()));
		if (!this->transitions.insert(x).second)
			this->transCache().release(x);
		return x;
	}

	typename trans_cache_type::value_type* addTransition(const vector<size_t>& lhs, const T& label, size_t rhs, const vector<size_t>& index) {
		if (lhs.size() > this->maxRank)
			this->maxRank = lhs.size();
		typename trans_cache_type::value_type* x = this->transCache().lookup(TT<T>(lhs, label, rhs, index, this->lhsCache()));
		if (!this->transitions.insert(x).second)
			this->transCache().release(x);
		return x;
	}

	typename trans_cache_type::value_type* addTransition(const typename trans_cache_type::value_type* transition) {
		if (transition->first.lhs().size() > this->maxRank)
			this->maxRank = transition->first.lhs().size();
		typename trans_cache_type::value_type* x = this->transCache().lookup(TT<T>(transition->first, this->lhsCache()));
		if (!this->transitions.insert(x).second)
			this->transCache().release(x);
		return x;
	}

	typename trans_cache_type::value_type* addTransition(const typename trans_cache_type::value_type* transition, const vector<size_t>& index) {
		if (transition->first.lhs().size() > this->maxRank)
			this->maxRank = transition->first.lhs().size();
		typename trans_cache_type::value_type* x = this->transCache().lookup(TT<T>(transition->first, index, this->lhsCache()));
		if (!this->transitions.insert(x).second)
			this->transCache().release(x);
		return x;
	}

	typename trans_cache_type::value_type* addTransition(const TT<T>& transition) {
		if (transition.lhs().size() > this->maxRank)
			this->maxRank = transition.lhs().size();
		typename trans_cache_type::value_type* x = this->transCache().lookup(TT<T>(transition, this->lhsCache()));
		if (!this->transitions.insert(x).second)
			this->transCache().release(x);
		return x;
	}

	typename trans_cache_type::value_type* addTransition(const TT<T>& transition, const vector<size_t>& index) {
		if (transition.lhs().size() > this->maxRank)
			this->maxRank = transition.lhs().size();
		typename trans_cache_type::value_type* x = this->transCache().lookup(TT<T>(transition, index, this->lhsCache()));
		if (!this->transitions.insert(x).second)
			this->transCache().release(x);
		return x;
	}

	void addFinalState(size_t state) { this->finalStates.insert(state); }
	
	void addFinalStates(const vector<size_t>& states) { this->finalStates.insert(states.begin(), states.end()); }
	
	void removeFinalState(size_t state) { this->finalStates.erase(state); }
	
	void clearFinalStates() { this->finalStates.clear(); }

	bool isFinalState(size_t state) const { return (this->finalStates.find(state) != this->finalStates.end()); }
	
	const std::set<size_t>& getFinalStates() const { return this->finalStates; }
	
	size_t getFinalState() const {
		assert(this->finalStates.size() == 1);
		return *this->finalStates.begin();
	}
	
	const trans_set_type& getTransitions() const { return this->transitions; }

	void downwardTranslation(LTS& lts, const Index<size_t>& stateIndex, const Index<T>& labelIndex) const;
	
	void downwardSimulation(vector<vector<bool> >& rel, const Index<size_t>& stateIndex) const;
	
	void upwardTranslation(LTS& lts, vector<vector<size_t> >& part, vector<vector<bool> >& rel, const Index<size_t>& stateIndex, const Index<T>& labelIndex, const vector<vector<bool> >& sim) const;

	void upwardSimulation(vector<vector<bool> >& rel, const Index<size_t>& stateIndex, const vector<vector<bool> >& param) const;
	
	static void combinedSimulation(vector<vector<bool> >& dst, const vector<vector<bool> >& dwn, const vector<vector<bool> >& up) {
		size_t size = dwn.size();
		vector<vector<bool> > dut(size, vector<bool>(size, false));
		for (size_t i = 0; i < size; ++i) {
			for (size_t j = 0; j < size; ++j) {
				for (size_t k = 0; k < size; ++k) {
					if (dwn[i][k] && up[j][k]) {
						dut[i][j] = true;
						break;
					}
				}
			}
		}
		dst = dut;
		for (size_t i = 0; i < size; ++i) {
			for (size_t j = 0; j < size; ++j) {
				if (!dst[i][j])
					continue;
				for (size_t k = 0; k < size; ++k) {
					if (dwn[j][k] && !dut[i][k]) {
						dst[i][j] = false;
						break;
					}
				}
			}
		}
	}

	template <class F>
	static size_t computeProduct(const lt_cache_type& cache1, const lt_cache_type& cache2, F f, size_t stateOffset = 0) {
//		std::vector<std::pair<size_t, size_t> > stack;
		boost::unordered_map<std::pair<size_t, size_t>, size_t> product;
		for (typename lt_cache_type::const_iterator i = cache1.begin(); i != cache1.end(); ++i) {
			if (!i->second.front()->_lhs->first.empty())
				continue;
			typename lt_cache_type::const_iterator j = cache2.find(i->first);
			if (j == cache2.end())
				continue;
			for (typename std::vector<const TT<T>*>::const_iterator k = i->second.begin(); k != i->second.end(); ++k) {
				for (typename std::vector<const TT<T>*>::const_iterator l = j->second.begin(); l != j->second.end(); ++l) {
					std::pair<boost::unordered_map<std::pair<size_t, size_t>, size_t>::iterator, bool> p =
						product.insert(make_pair(make_pair((*k)->_rhs, (*l)->_rhs), product.size() + stateOffset));
					f(*k, *l, std::vector<size_t>(), p.first->second);
//					if (p.second)
//						stack.push_back(p.first->first);
				}
			}
		}
		bool changed = true;
		while (changed) {
//			std::pair<size_t, size_t> s = stack.back();
//			stack.pop_back();
			changed = false;
			for (typename lt_cache_type::const_iterator i = cache1.begin(); i != cache1.end(); ++i) {
				if (i->second.front()->_lhs->first.empty())
					continue;
				typename lt_cache_type::const_iterator j = cache2.find(i->first);
				if (j == cache2.end())
					continue;
				for (typename std::vector<const TT<T>*>::const_iterator k = i->second.begin(); k != i->second.end(); ++k) {
					for (typename std::vector<const TT<T>*>::const_iterator l = j->second.begin(); l != j->second.end(); ++l) {
						assert((*k)->_lhs->first.size() == (*l)->_lhs->first.size());
						std::vector<size_t> lhs; 
						for (size_t m = 0; m < (*k)->_lhs->first.size(); ++m) {
							boost::unordered_map<std::pair<size_t, size_t>, size_t>::iterator n = product.find(
								make_pair((*k)->_lhs->first[m], (*l)->_lhs->first[m])
							);
							if (n == product.end())
								break;
							lhs.push_back(n->second);
						}
						if (lhs.size() < (*k)->_lhs->first.size())
							continue;
						std::pair<boost::unordered_map<std::pair<size_t, size_t>, size_t>::iterator, bool> p =
							product.insert(make_pair(make_pair((*k)->_rhs, (*l)->_rhs), product.size() + stateOffset));
						f(*k, *l, lhs, p.first->second);
						if (p.second)
							changed = true; //stack.push_back(p.first->first);
					}
				}
			}
		}
		return product.size();
	}

	struct IntersectF {

		TA<T>& dst;
		const TA<T>& src1;
		const TA<T>& src2;

		IntersectF(TA<T>& dst, const TA<T>& src1, const TA<T>& src2) : dst(dst), src1(src1), src2(src2) {}

		void operator()(const TT<T>* t1, const TT<T>* t2, const std::vector<size_t>& lhs, size_t rhs) {
			this->dst.addTransition(lhs, t1->_label, rhs);
			if (this->src1.isFinalState(t1->_rhs) && this->src2.isFinalState(t2->_rhs))
				this->dst.addFinalState(rhs);
		}

	};

	static size_t intersection(TA<T>& dst, const TA<T>& src1, const TA<T>& src2, size_t stateOffset = 0) {
		lt_cache_type cache1, cache2;
		src1.buildLTCache(cache1);
		src2.buildLTCache(cache2);
		return TA<T>::computeProduct(cache1, cache2, TA<T>::IntersectF(dst, src1, src2), stateOffset);
	}

	struct PredicateF {

		std::vector<size_t>& dst;
		const TA<T>& predicate;

		PredicateF(std::vector<size_t>& dst, const TA<T>& predicate) : dst(dst), predicate(predicate) {}

		void operator()(const TT<T>* t1, const TT<T>* t2, const std::vector<size_t>& lhs, size_t rhs) {
			if (predicate.isFinalState(t2->_rhs))
				this->dst.push_back(t2->_rhs);
		}

	};

	void intersectingStates(std::vector<size_t>& dst, const TA<T>& predicate) const {
		lt_cache_type cache1, cache2;
		this->buildLTCache(cache1);
		predicate.buildLTCache(cache2);
		TA<T>::computeProduct(cache1, cache2, TA<T>::PredicateF(dst, predicate));
	}

	static bool transMatch(const TT<T>* t1, const TT<T>* t2, std::vector<std::vector<bool> >& mat, const Index<size_t>& stateIndex) {

		if (t1->_label != t2->_label)
			return false;

		bool match = true;
		for (size_t m = 0; m < t1->_lhs->first.size(); ++m) {
			if (!mat[stateIndex[t1->_lhs->first[m]]][stateIndex[t2->_lhs->first[m]]]) {
				match = false;
				break;
			}
		}
		return match;

	}

	// currently erases '1' from the relation
	void heightAbstraction(std::vector<std::vector<bool> >& result, size_t height, const Index<size_t>& stateIndex) const {

		td_cache_type cache;
		this->buildTDCache(cache);

		std::vector<std::vector<bool> > tmp;
/*
		for (Index<size_t>::iterator i = stateIndex.begin(); i != stateIndex.end(); ++i)
			std::cerr << i->first << ':' << i->second << ' ';
		std::cerr << std::endl;
*/
		while (height--) {

			tmp = result;
/*
			for (size_t i = 0; i < tmp.size(); ++i) {
				for (size_t j = 0; j < tmp[i].size(); ++j) {
					std::cerr << tmp[i][j];
				}
				std::cerr << std::endl;
			}
*/
			for (Index<size_t>::iterator i = stateIndex.begin(); i != stateIndex.end(); ++i) {

				size_t state1 = i->second;

				typename td_cache_type::iterator j = cache.insert(
					std::make_pair(i->first, std::vector<const TT<T>*>())
				).first;

				for (Index<size_t>::iterator k = stateIndex.begin(); k != stateIndex.end(); ++k) {

					size_t state2 = k->second;

					if ((state1 == state2) || !tmp[state1][state2])
						continue;

					typename td_cache_type::iterator l = cache.insert(
						std::make_pair(k->first, std::vector<const TT<T>*>())
					).first;

					bool match = false;

					for (typename std::vector<const TT<T>*>::const_iterator m = j->second.begin(); m != j->second.end(); ++m) {

						for (typename std::vector<const TT<T>*>::const_iterator n = l->second.begin(); n != l->second.end(); ++n) {

							if (TA<T>::transMatch(*m, *n, tmp, stateIndex)) {
								match = true;
								break;
							}

						}

						if (match)
							break;

					}

					if (!match)
						result[state1][state2] = false;

				}

			}

		}

		for (size_t i = 0; i < result.size(); ++i) {
			for (size_t j = 0; j < i; ++j) {
				if (!result[i][j])
					result[j][i] = false;
				if (!result[j][i])
					result[i][j] = false;
			}
		}

	}

	void predicateAbstraction(std::vector<std::vector<bool> >& result, const TA<T>& predicate, const Index<size_t>& stateIndex) const {
		std::vector<size_t> states;
		this->intersectingStates(states, predicate);
		std::set<size_t> s;
		for (std::vector<size_t>::iterator i = states.begin(); i != states.end(); ++i)
			s.insert(stateIndex[*i]);
		for (size_t i = 0; i < result.size(); ++i) {
			if (s.count(i) == 1)
				continue;
			for (size_t j = 0; j < i; ++j) {
				result[i][j] = 0;
				result[j][i] = 0;
			}
			for (size_t j = i + 1; j < result.size(); ++j) {
				result[i][j] = 0;
				result[j][i] = 0;
			}
		}
	}
	
	// collapses states according to a given relation
	TA<T>& collapsed(TA<T>& dst, const vector<vector<bool> >& rel, const Index<size_t>& stateIndex) const {
		vector<size_t> headIndex;
		utils::relBuildClasses(rel, headIndex);
		// TODO: perhaps improve indexing
		std::vector<size_t> invStateIndex(stateIndex.size());
		for (Index<size_t>::iterator i = stateIndex.begin(); i != stateIndex.end(); ++i)
			invStateIndex[i->second] = i->first;
		for (std::vector<size_t>::iterator i = headIndex.begin(); i != headIndex.end(); ++i)
			*i = invStateIndex[*i];
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = this->transitions.begin(); i != this->transitions.end(); ++i) {
			vector<size_t> lhs;
			stateIndex.translate(lhs, (*i)->first._lhs->first);
			for (size_t j = 0; j < lhs.size(); ++j)
				lhs[j] = headIndex[lhs[j]];
			dst.addTransition(lhs, (*i)->first._label, headIndex[stateIndex[(*i)->first._rhs]]);
		}
		for (set<size_t>::const_iterator i = this->finalStates.begin(); i != this->finalStates.end(); ++i)
			dst.addFinalState(headIndex[stateIndex[*i]]);
		return dst; 
	}
	
	TA<T>& uselessFree(TA<T>& dst) const {
		vector<typename trans_cache_type::value_type*> v1(this->transitions.begin(), this->transitions.end()), v2;
		set<size_t> states;
		bool changed = true;
		while (changed) {
			changed = false;
			for (typename vector<typename trans_cache_type::value_type*>::const_iterator i = v1.begin(); i != v1.end(); ++i) {
				bool matches = true;
				for (vector<size_t>::const_iterator j = (*i)->first._lhs->first.begin(); j != (*i)->first._lhs->first.end(); ++j) {
					if (!states.count(*j)) {
						matches = false;
						break;
					}
				}
				if (matches) {
					if (states.insert((*i)->first._rhs).second)
						changed = true;
					dst.addTransition(*i);
				} else {
					v2.push_back(*i);
				}
			}
			v1.clear();
			std::swap(v1, v2);
		}
		for (set<size_t>::const_iterator i = this->finalStates.begin(); i != this->finalStates.end(); ++i) {
			if (states.count(*i))
				dst.addFinalState(*i);
		}
		return dst;
	}
	
	TA<T>& unreachableFree(TA<T>& dst) const {
		vector<typename trans_cache_type::value_type*> v1(transitions.begin(), this->transitions.end()), v2;
		set<size_t> states(this->finalStates.begin(), this->finalStates.end());
		bool changed = true;
		while (changed) {
			changed = false;
			for (typename vector<typename trans_cache_type::value_type*>::const_iterator i = v1.begin(); i != v1.end(); ++i) {
				if (states.count((*i)->first._rhs)) {
					dst.addTransition(*i);
					for (vector<size_t>::const_iterator j = (*i)->first._lhs->first.begin(); j != (*i)->first._lhs->first.end(); ++j) {
						if (states.insert(*j).second)
							changed = true;
					}
				} else {
					v2.push_back(*i);
				}
			}
			v1.clear();
			std::swap(v1, v2);
		}
		for (set<size_t>::const_iterator i = this->finalStates.begin(); i != this->finalStates.end(); ++i)
			dst.addFinalState(*i);
		return dst;
	}
	
	TA<T>& minimized(TA<T>& dst, const vector<vector<bool> >& cons, const Index<size_t>& stateIndex) const {
		typename TA<T>::Backend backend;
		vector<vector<bool> > dwn;
		this->downwardSimulation(dwn, stateIndex);
		utils::relAnd(dwn, cons, dwn);
		TA<T> tmp1(backend), tmp2(backend);
		return this->collapsed(tmp1, dwn, stateIndex).uselessFree(tmp2).unreachableFree(dst);
	}
	
	TA<T>& minimized(TA<T>& dst) const {
		Index<size_t> stateIndex;
		this->buildSortedStateIndex(stateIndex);
		vector<vector<bool> > cons(stateIndex.size(), vector<bool>(stateIndex.size(), true));
		return this->minimized(dst, cons, stateIndex);
	}
	
	static bool subseteq(const TA<T>& a, const TA<T>& b);

	static TA<T>& reduce(TA<T>& dst, const TA<T>& src, Index<size_t>& index, size_t offset = 0, bool addFinalStates = true) {
		vector<size_t> lhs;
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = src.transitions.begin(); i != src.transitions.end(); ++i) {
			lhs.clear();
			index.translateOTF(lhs, (*i)->first._lhs->first, offset);
			dst.addTransition(lhs, (*i)->first._label, index.translateOTF((*i)->first._rhs) + offset);
		}
		if (addFinalStates) {
			for (std::set<size_t>::const_iterator i = src.finalStates.begin(); i != src.finalStates.end(); ++i)
				dst.addFinalState(index.translateOTF(*i) + offset);
		}
		return dst;
	}

	template <class F>
	static TA<T>& rename(TA<T>& dst, const TA<T>& src, F f, bool addFinalStates = true) {
		vector<size_t> lhs;
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = src.transitions.begin(); i != src.transitions.end(); ++i) {
			lhs.resize((*i)->first._lhs->first.size());
			for (size_t j = 0; j < (*i)->first._lhs->first.size(); ++j)
				lhs[j] = f((*i)->first._lhs->first[j]);
			dst.addTransition(lhs, (*i)->first._label, f((*i)->first._rhs));
		}
		if (addFinalStates) {
			for (std::set<size_t>::const_iterator i = src.finalStates.begin(); i != src.finalStates.end(); ++i)
				dst.addFinalState(f(*i));
		}
		return dst;
	}

public:

	// makes state numbers contiguous
	TA& reduced(TA<T>& dst, Index<size_t>& index) const {
		return TA<T>::reduce(dst, *this, index);
	}
	
	static TA<T>& disjointUnion(TA<T>& dst, const TA<T>& a, const TA<T>& b) {
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = a.transitions.begin(); i != a.transitions.end(); ++i)
			dst.addTransition(*i);
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = b.transitions.begin(); i != b.transitions.end(); ++i)
			dst.addTransition(*i);
		for (set<size_t>::const_iterator i = a.finalStates.begin(); i != a.finalStates.end(); ++i)
			dst.addFinalState(*i);
		for (set<size_t>::const_iterator i = b.finalStates.begin(); i != b.finalStates.end(); ++i)
			dst.addFinalState(*i);
		return dst;
	}

	static TA<T>& disjointUnion(TA<T>& dst, const TA<T>& src, bool addFinalStates = true) {
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = src.transitions.begin(); i != src.transitions.end(); ++i)
			dst.addTransition(*i);
		if (addFinalStates) {
			for (set<size_t>::const_iterator i = src.finalStates.begin(); i != src.finalStates.end(); ++i)
				dst.addFinalState(*i);
		}
		return dst;
	}

	static TA<T>& renamedUnion(TA<T>& dst, const TA<T>& a, const TA<T>& b, size_t& aSize) {
		Index<size_t> index;
		reduce(dst, a, index);
		aSize = index.size();
		index.clear();
		reduce(dst, b, index, aSize);
		return dst;
	}

	static TA<T>& renamedUnion(TA<T>& dst, const TA<T>& src, size_t offset, size_t& srcSize) {
		Index<size_t> index;
		reduce(dst, src, index, offset);
		srcSize = index.size();
		return dst;
	}

	TA<T>& unfoldAtRoot(TA<T>& dst, size_t newState, bool registerFinalState = true) const {
		for (typename set<typename trans_cache_type::value_type*>::const_iterator i = this->transitions.begin(); i != this->transitions.end(); ++i) {
			dst.addTransition(*i);
			if (this->isFinalState((*i)->first._rhs))
				dst.addTransition((*i)->first._lhs->first, (*i)->first._label, newState);
		}
		if (registerFinalState)
			dst.addFinalState(newState);
		return dst;
	}

/*	
	TA<T>& unfoldAtLeaf(TA<T>& dst, size_t selector) const {
		// TODO:
		return dst;
	}
*/
	class Manager : Cache<TA<T>*>::Listener {
	
		mutable typename TA<T>::Backend& backend;
	
		Cache<TA<T>*> taCache;
		std::vector<TA<T>*> taPool;

	protected:

		virtual void drop(typename Cache<TA<T>*>::value_type* x) {
			x->first->clear();
			this->taPool.push_back(x->first);
		}
	
	public:

		Manager(typename TA<T>::Backend& backend) : backend(backend) {
			this->taCache.addListener(this);
		}

		~Manager() {
			utils::erase(this->taPool);
			assert(this->taCache.empty());
		}

		const Cache<TA<T>*>& getCache() const {
			return this->taCache;
		}

		TA<T>* alloc() {
			TA<T>* dst;
			if (!this->taPool.empty()) {
				dst = this->taPool.back();
				this->taPool.pop_back();
			} else {
				dst = new TA<T>(this->backend);
			}
			return this->taCache.lookup(dst)->first;
		}
	
		TA<T>* clone(TA<T>* src, bool copyFinalStates = true) {
			assert(src);
			assert(src->backend == &this->backend);
			return this->taCache.lookup(new TA<T>(*src, copyFinalStates))->first;
		}

		TA<T>* addRef(TA<T>* x) {
			typename Cache<TA<T>*>::value_type* v = this->taCache.find(x);
			assert(v);
			return this->taCache.addRef(v), x;
		}
	
		size_t release(TA<T>* x) {
			typename Cache<TA<T>*>::value_type* v = this->taCache.find(x);
			assert(v);
			return this->taCache.release(v);
		}
	
		void clear() {
			this->taCache.clear();
			for (typename vector<TA<T>*>::iterator i = this->taPool.begin(); i != this->taPool.end(); ++i)
				delete *i;
			this->taPool.clear();
		}

		bool isAlive(TA<T>* x) {
			return this->taCache.find(x) != NULL;			
		}

		typename TA<T>::Backend& getBackend() {
			return this->backend;
		}
	
	};

};
#endif