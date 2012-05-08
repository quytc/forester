
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

#include <sstream>
#include <vector>
#include <list>
#include <set>
#include <boost/unordered_set.hpp>
#include <boost/unordered_map.hpp>

#include <algorithm>

#include <cl/code_listener.h>
#include <cl/cl_msg.hh>
#include <cl/cldebug.hh>
#include <cl/clutil.hh>
#include <cl/storage.hh>
#include "../cl/ssd.h"

#include "forestautext.hh"
#include "symctx.hh"
#include "executionmanager.hh"
#include "fixpointinstruction.hh"
#include "virtualmachine.hh"
#include "regdef.hh"
#include "symexec.hh"
#include "compiler.hh"
using namespace ssd;
using std::vector;
using std::list;
using std::set;
using boost::unordered_set;
using boost::unordered_map;
class SymExec::Engine {

	TA<label_type>::Backend taBackend;
	TA<label_type>::Backend fixpointBackend;
	BoxMan boxMan;

	std::vector<const Box*> boxes;
	std::vector<const Box*> basicBoxes;
	boost::unordered_map<const Box*, std::vector<const Box*> > hierarchy;

	Compiler compiler_;
	Compiler::Assembly assembly_;

	ExecutionManager execMan;
	bool dbgFlag;
        std::vector<string> vars;
protected:
static void getStatus(SymState* state, ExecutionManager& execMan, string& status)
   {
          status = "unknown";
          std::ostringstream ss;
          ss << state->instr->insn();

          for(int i = 0; i < execMan.condQueue_.size(); i++)
            {
                if(execMan.condQueue_.at(i).first == state){
                  status =  execMan.condQueue_.at(i).second;}  
            }
          
 
   }
static void getAbsTA(SymState* state, ExecutionManager& execMan, std::vector<FAE>& absFaes, int& status)
   {
          status = 0;
          absFaes.clear();
          for(int i = 0; i < execMan.absQueue_.size(); i++)
            {
                if(execMan.absQueue_.at(i).first == state)
                 {status = 1; 
                 absFaes =  execMan.absQueue_.at(i).second;}
            }


   }
static void getAbsTrace(AbstractInstruction::StateType state, std::vector<std::vector<FAE>>& absTrace, ExecutionManager& execMan ) {
       SymState* s = state.second;
       SymState* s1 = state.second;
       string ss1 = "";
       std::ostringstream ss;
       absTrace.clear();
       int status,i;
       i = 0;
       std::vector<SymState*> trace;

      for ( ; s; s = s->parent)
        { 
          trace.push_back(s);
        }
      std::reverse(trace.begin(), trace.end());

      for (int i = 0; i < trace.size()-1; i++)
       if (trace.at(i)->instr->insn())
          std::cerr << "     " << *trace.at(i)->instr->insn() << "-------" << *trace.at(i)->instr << std::endl;
       }
static void getCondTrace(AbstractInstruction::StateType state, std::vector<string>& condTrace, ExecutionManager& execMan ) {
        SymState* s = state.second; 
          for ( ; s; s = s->parent){
              string status;
              getStatus(s,execMan,status);       
              if (s->instr->insn()) {          
                std::ostringstream ss;
                ss << *s->instr->insn();
                if(status.find("unknown") == string::npos && ss.str().find("if") != string::npos)
                    {   condTrace.push_back(status);
                    }
             }
          }
          std::reverse(condTrace.begin(), condTrace.end());
 }

static void printTrace(const AbstractInstruction::StateType state, std::vector<pair<FAE,string>>& statements ) {
              SymState* s = state.second;
              statements = {};
	      std::vector<SymState*> trace;
              int size = 0;
	      for ( ; s; s = s->parent){
			trace.push_back(s);
              }
	      std::reverse(trace.begin(), trace.end());
	      for (auto s : trace) {
		if (s->instr->insn()) {
		 std::stringstream ss,ss2,ss1;
                 ss2 << *s->instr;
                 if(ss2.str().find("abs") != string::npos)
                  ss << *s->instr->insn() << "--abs";
                 else
                  ss << *s->instr->insn();
                  ss1 << *s->fae;
                  statements.push_back(pair<FAE,string>(*s->fae,ss.str()));
                  size++;
		}
       

		}        
	}
 static int sizeTrace(const AbstractInstruction::StateType state) {

                SymState* s = state.second;
               int size = 0;
                for ( ; s; s = s->parent){
                      if(s->instr->insn())
                         size++;        
                 } 
                 return size;
        }

static void printTrace2(std::vector<pair<FAE,string>> statements) {

               CL_NOTE("trace:");
               int size = 0;
                for (int i = 0; i < statements.size(); i++) {
                              if(statements.at(i).second.find("deleted") == string::npos)
                                std::cerr << statements.at(i).second << std::endl;
                                size++;
                }

        }

static int branchsize(std::vector<pair<FAE,string>> statements) {
               int size = 0;
                for (int i = 0; i < statements.size(); i++) {
                                size++;
                }
        return size;
        }

static void refineStatements(std::vector<pair<FAE,string>>& instructions, std::vector<string> condTrace) {
    for(int i = 0; i < instructions.size(); i++){
     if(i+2 < instructions.size())
     {
      if(instructions.at(i).second.find("nondet") != string::npos && instructions.at(i+2).second.find("if")!=string::npos)
         {
          if(instructions.at(i).second.find("--abs") == string::npos)
             instructions.at(i) = pair<FAE,string>(instructions.at(i).first, "deleted");
          instructions.at(i+1) = pair<FAE,string>(instructions.at(i+1).first, "deleted");
          instructions.at(i+2) = pair<FAE,string>(instructions.at(i+2).first, "Check (ND) " + condTrace.at(i+3));
          
          continue;}
     }
      if(instructions.at(i).second.find("if")!=string::npos)
         {
         int x = int(instructions.at(i).second.find("("));
         int y = int(instructions.at(i).second.find(")"));
         string z = instructions.at(i).second.substr(x+1, y-x - 1);
         string s = instructions.at(i).second.substr(y);
         string expression;
            
         if(instructions.at(i-1).second.find(z) != string::npos)
          {
          x = int(instructions.at(i-1).second.find("("));
          string exp;
          if(instructions.at(i-1).second.find("==") != string::npos)
          {y = int(instructions.at(i-1).second.find("=="));
          exp = "==";}
          if(instructions.at(i-1).second.find("<=") != string::npos)
          {y = int(instructions.at(i-1).second.find("<="));
          exp = "<=";}
          if(instructions.at(i-1).second.find("< ") != string::npos)
          {y = int(instructions.at(i-1).second.find("< "));
          exp = "< ";}
          if(instructions.at(i-1).second.find("!=") != string::npos)
          {y = int(instructions.at(i-1).second.find("!="));
          exp = "!=";}
          int t = int(instructions.at(i-1).second.find(")"));
          string left;
          string right;
          // for case of full expression
          if(instructions.at(i-1).second.substr(x,y-x).find(":")==string::npos&&instructions.at(i-1).second.substr(y,t-y).find(":")==string::npos &&
            instructions.at(i-1).second.substr(y,t-y).find("NULL")==string::npos)
            {
            if(instructions.at(i-3).second.find(instructions.at(i-1).second.substr(x+1,y-x-1))!=string::npos)
            {
            int x1 = int(instructions.at(i-3).second.find("="));
            left = instructions.at(i-3).second.substr(x1);
            if(left.find("#") != string::npos)
            {
            left = left.substr(int(left.find(":"))+1);
            }
            instructions.at(i-3) = pair<FAE,string>(instructions.at(i-3).first, "deleted");
            }
            if(instructions.at(i-2).second.find(instructions.at(i-1).second.substr(y+3, t-y-3))!=string::npos)
            {
            int x2 = int(instructions.at(i-2).second.find("="));
            right = instructions.at(i-2).second.substr(x2);
            if(right.find("#") != string::npos)
            {
            right = right.substr(int(right.find(":"))+1);
            }
            instructions.at(i-2) = pair<FAE,string>(instructions.at(i-2).first, "deleted");
          }
            expression = left + exp + right;
            instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"Check (" + expression + ")" + condTrace.at(i+1));
            if(instructions.at(i-1).second.find("--abs") == string::npos)
               instructions.at(i-1) =  pair<FAE,string>(instructions.at(i-1).first, "deleted");
        }
       else
            {
            if(instructions.at(i-1).second.substr(x,y-x).find(":")==string::npos)
                 {
                 int x1 = int(instructions.at(i-2).second.find("="));
                 left = instructions.at(i-2).second.substr(x1);
                 if(left.find("#") != string::npos)
                 {
                  left = left.substr(int(left.find(":"))+1);
                 }

                if(instructions.at(i-1).second.substr(y,t-y).find("NULL")==string::npos)
                        { int x2 = int(instructions.at(i-1).second.find(":"));
                              right = instructions.at(i-1).second.substr(x2+1,1);
                        }
                      else
                          right = "NULL";
                      expression = left + exp + right;
                      instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"Check (" + expression + ")"
                                              + condTrace.at(i+1));
                      instructions.at(i-2) = pair<FAE,string>(instructions.at(i-2).first, "deleted");
                      if(instructions.at(i-1).second.find("--abs") == string::npos) 
                        instructions.at(i-1) = pair<FAE,string>(instructions.at(i-1).first, "deleted");
                   }
                   else {
                    if(instructions.at(i-1).second.substr(y,t-y).find(":")!=string::npos)

                    {
                         int x1 = int(instructions.at(i-1).second.substr(x,y-x).find(":"));
                         left = instructions.at(i-1).second.substr(x,y-x).substr(x1+1,1);
                         int x2 = int(instructions.at(i-1).second.substr(y,t-y).find(":"));
                         right = instructions.at(i-1).second.substr(y,t-y).substr(x2+1,1);
                         expression = left + exp + right;
                         instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"Check (" + expression + ")"
                                              + condTrace.at(i+1));
                         if(instructions.at(i-1).second.find("--abs") == string::npos)
                           instructions.at(i-1) = pair<FAE,string>(instructions.at(i-1).first, "deleted");
                    }
                    else
                     {
                         int x1 = int(instructions.at(i-1).second.substr(x,y-x).find(":"));
                         left = instructions.at(i-1).second.substr(x,y-x).substr(x1+1,1);
                         right = "NULL";
                         expression = left + exp + right;
                         instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"Check (" + expression + ")"
                                              + condTrace.at(i+1));
                         if(instructions.at(i-1).second.find("--abs") == string::npos)
                          instructions.at(i-1) = pair<FAE,string>(instructions.at(i-1).first, "deleted");
                     }
                  }
             }
            }
}
        //-----------------------------malloc statement--------------------------------------------
        if(instructions.at(i).second.find("malloc")!=string::npos)
         instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"Node* "+ instructions.at(i).second.substr
         (int(instructions.at(i).second.find(":"))+1,1) + " = New Node()" );
        //-----------------------------Assignment statement-----------------------------------------
        else
        {
        if(instructions.at(i).second.find("=")!=string::npos)
        if(instructions.at(i).second.find(":")!=string::npos && int(instructions.at(i).second.find("=")) > int(instructions.at(i).second.find(":")))
        {
        int x = int(instructions.at(i).second.find(":"));
        string first = instructions.at(i).second.substr(x+1);
        string left, right;
        if(first.find(":")!=string::npos)
        {int y = int(first.find(":"));
        int z = int(first.find("#"));
        left = first.substr(0,z);
        right = first.substr(y+1);
        instructions.at(i) = pair<FAE,string>(instructions.at(i).first,left + right);
        }
        else
        {
        instructions.at(i) = pair<FAE,string>(instructions.at(i).first,first);
        }
       }
      }
      //-------------Free statement--------------------------------------------------------
     if(instructions.at(i).second.find("free") != string::npos)
       { int x = int(instructions.at(i).second.find(":"));
       instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"Free(" + instructions.at(i).second.substr(x+1,1) + ")");
       }
     //--------------------------Return statement-----------------------------------------------------
     if(instructions.at(i).second.find("(int)0") != string::npos && instructions.at(i+1).second.find("return") != string::npos)
      { instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"deleted");
        instructions.at(i+1) = pair<FAE,string>(instructions.at(i+1).first,"Return 0");
      }
     if(instructions.at(i).second.find("(int)1") != string::npos && instructions.at(i+1).second.find("return") != string::npos)
      { instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"deleted");
        instructions.at(i+1) = pair<FAE,string>(instructions.at(i+1).first,"Return 1");
      }
   }
   for(int i = 0; i < instructions.size()-1; i++)    
     if(instructions.at(i).second.find("#") != string::npos)
     {
       int x,y;
       x = int(instructions.at(i).second.find("#"));
       y = int(instructions.at(i).second.find("="));
       string right = instructions.at(i).second.substr(x,y-x-1);
      if(instructions.at(i+1).second.find(right) != string::npos)
        {
         y = int(instructions.at(i).second.find(":"));
         right = instructions.at(i).second.substr(y+1);
         x = int(instructions.at(i+1).second.find(":"));
         y = int(instructions.at(i+1).second.find("="));
         string left = instructions.at(i+1).second.substr(0,y-1);
         instructions.at(i+1) = pair<FAE,string>(instructions.at(i+1).first,left + "=" + right);
         instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"deleted"); 
        }
       for(int i = 0; i < instructions.size(); i++){
        if(instructions.at(i).second.find(")--abs") != string::npos)
        { instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"Abstraction");
        }
       }
     }
 }


void printBoxes() const {
		for (auto& box : this->boxMan.getBoxes())
		 std::cerr << "Available Boxes: "<< *(AbstractBox*)&box << ':' << std::endl << box;
	}
     
static  void readStackFrame(const FAE& fae, std::vector<Data>& out) {
       out={};
       VirtualMachine vm(fae);
       size_t root = vm.varGet(ABP_INDEX).d_ref.root;
       auto& t = fae.roots[root]->getAcceptingTransition();
       int n = 0; 
       for (auto i = t.lhs().begin(); i != t.lhs().end(); ++i)
               out.push_back(fae.getData(*i));
               n++;
       }
static  void collectTA(std::vector<string>& ta, string& fae)
        {  ta = {};
           while(fae.find("===") != string::npos)
           {
            int x = int(fae.find("==="));
            if(fae.substr(x+3).find("===") != string::npos)
             {
              int y = fae.substr(x+3).find("===");
              ta.push_back(fae.substr(x+3).substr(0,y));
              fae.assign(fae.substr(y));
             }
            else
             {
              ta.push_back(fae.substr(x+3));
              break;
             }
           }

        }
static void printTAwithvariables(std::vector<Data> stack, std::vector<string> vars,std::vector<string>& ta)
        {         
         for(int i = 2; i < stack.size(); i++)
         {
          std::stringstream ss,ss1;
          ss << stack.at(i);
          if(ss.str().find("(ref)") != string::npos)
           {
            int index = 0;
            std::stringstream os(ss.str().substr(5,1));
            os >> index;
            ss1 << vars.at(i-2);
            for(int j = 0; j < ta.size(); j++){
            if(ta.at(j).find("root " + os.str())!=string::npos)
             ta.at(j)= "var: [" +  ss1.str() + "]: " + "\n  |\n  v\n " + ta.at(j);
            }
           }
          } 
        }

static void printAbsTAs(std::vector<FAE> absTrace, std::vector<string> vars) {
   std::vector<string> msg;
   for(int i = absTrace.size()-1; i >= 0; i--)
    { 
     int z = absTrace.size() - 1- i;
     if(z%2 == 0)
       msg.push_back("After Abstraction");
     else
       msg.push_back("After Norminaze and Fold");
  }
   std::reverse(msg.begin(), msg.end());
   std::vector<Data> out;
   std::vector<string> ta = {};
   for(int i = 0; i < absTrace.size(); i++)
   {
    string fae;
    std::stringstream ss;
    ss << absTrace.at(i);
    fae = ss.str();
    ta.clear();
    collectTA(ta,fae);
    readStackFrame(absTrace.at(i), out);
    printTAwithvariables(out,vars,ta);
    std::cerr << msg.at(i) << std::endl;
    for(int j = 0; j < ta.size(); j++)
      std::cerr << ta.at(j) << std::endl;
  }

 }
static void printBoxes(std::vector<string>& boxes)
 {
 for(int i = 0; i < boxes.size(); i++)
     std::cerr << boxes.at(i) << std::endl;
 }
static void printTATrace(std::vector<pair<FAE,string>>& statements,std::vector<string> vars, std::vector<std::vector<FAE>> absTrace, std::vector<std::vector<string>>& boxes) {
   int size = 0;
   std::vector<std::vector<Data>> stacklist = {};
   std::vector<Data> out;
   std::vector<string> ta = {};
   int count = 0;
  for (int i = 0; i < statements.size(); i++) {
    string fae;
    std::stringstream ss;
    ss << statements.at(i).first;
    fae = ss.str();
    ta.clear();
    Engine::collectTA(ta,fae);
    readStackFrame(statements.at(i).first, out);
    stacklist.push_back(out);
    printTAwithvariables(out,vars,ta);
  if(i>0 && statements.at(i-1).second.find("Abstraction") != string::npos)
  {
   if(statements.at(i).second.find("deleted") == string::npos)
    {
    std::cerr << "------------------------------------------------------------------------------------------------------------------------------" << std::endl;
    std::cerr << statements.at(i).second << std::endl;
    std::cerr << "------------------------------------------------------------------------------------------------------------------------------" << std::endl;
    }
    continue;
  }
  if(statements.at(i).second.find("Abstraction") != string::npos)
  {
    for(int j = 0; j < ta.size(); j++)
      std::cerr << ta.at(j) << std::endl;
    std::cerr << "------------------------------------------------------------------------------------------------------------------------------" << std::endl;
    std::cerr << "Abstraction" << std::endl;
    std::cerr << "------------------------------------------------------------------------------------------------------------------------------" << std::endl;
    printBoxes(boxes.at(i+1));
    printAbsTAs(absTrace.at(i+1),vars);
  }
  else
  if((statements.at(i).second.find("deleted") == string::npos && i > 0 && statements.at(i-1).second.find("deleted") == string::npos) ||
      (statements.at(i).second.find("deleted") == string::npos && i == 0))
   {
    for(int j = 0; j < ta.size(); j++)
      std::cerr << ta.at(j) << std::endl;  
    std::cerr << "------------------------------------------------------------------------------------------------------------------------------" << std::endl;
    std::cerr << statements.at(i).second << std::endl;
    std::cerr << "------------------------------------------------------------------------------------------------------------------------------" << std::endl;
    size++;
   }
   else
    {
    if( i>0 && statements.at(i-1).second.find("deleted") == string::npos)
     {
        for(int j = 0; j < ta.size(); j++)
           std::cerr << ta.at(j) << std::endl;
     }
    if(i>0 && statements.at(i).second.find("deleted") == string::npos)
    {
    std::cerr << "------------------------------------------------------------------------------------------------------------------------------" << std::endl;
    std::cerr << statements.at(i).second << std::endl;
    std::cerr << "------------------------------------------------------------------------------------------------------------------------------" << std::endl;
    }
    }
  }
}

void mainLoop() {

		AbstractInstruction::StateType state;
                
                std::vector<std::vector<pair<FAE,string>>> statelist = {};
                std::vector<std::vector<string>> condTraceList = {};
                std::vector<string> condTrace;
                std::vector<std::vector<std::vector<FAE>>> absTraceList;
                std::vector<std::vector<string>> boxTrace = {};
                std::vector<std::vector<std::vector<string>>> boxTraceList = {};
                std::vector<pair<std::vector<string>, string>> instructions = {};
                std::vector<pair<FAE,string>> statements;
                std::vector<Data> out;
                std::vector<string> ta = {};            
                std::vector<std::vector<Data>> stacklist = {};           
                std::vector<std::vector<FAE>> absTrace = {}; 
         try {
                       string fae;
                       
                       AbstractInstruction::StateType laststate,oldstate;
			while (this->execMan.dequeueDFS(state)) {
                                if (state.second->instr->insn()) {
                                        string insn;
                                        std::ostringstream ss;
                                        ss << *state.second->instr->insn();
                                        insn = ss.str();
                                        ss << *state.second->fae;
                                        fae = ss.str();
                                        collectTA(ta,fae);  

                                        VirtualMachine vm(*state.second->fae);
                                      if(sizeTrace(state) <= branchsize(statements))
                                       {
                                          // add cond, abs, box trace into their lists
                                          absTrace.push_back(execMan.absFAEs);
                                          execMan.absFAEs.clear();
                                          absTraceList.push_back(absTrace); 
                                          boxTrace.push_back(execMan.avaiBoxes);
                                          execMan.avaiBoxes.clear();
                                          boxTraceList.push_back(boxTrace); 
                                          condTraceList.push_back(condTrace);
                                          statelist.push_back(statements);
                                          // Change condition trace, abs trace, box trace
                                          absTrace.erase(absTrace.begin() + sizeTrace(state) , absTrace.end());
                                          condTrace.erase(condTrace.begin() + sizeTrace(state) - 1, condTrace.end());
                                          boxTrace.erase(boxTrace.begin() + sizeTrace(state), boxTrace.end());
                                          Engine::printTrace(state, statements);
                                          // update cond, abs,box traces
                                          // absTrace.push_back(execMan.absFAEs);
                                          condTrace.push_back(execMan.condStatus);
                                          // execMan.absFAEs.clear();
                                          execMan.condStatus = "...";
                                       }
                                       else
                                       {
                                         Engine::printTrace(state, statements);
                                         // update cond, abs, box traces
                                         absTrace.push_back(execMan.absFAEs);
                                         condTrace.push_back(execMan.condStatus);
                                         boxTrace.push_back(execMan.avaiBoxes);
                                         execMan.avaiBoxes.clear();
                                         execMan.absFAEs.clear();
                                         execMan.condStatus = "..."; 
                                          }
                                  
				} else {                  
		           }
				this->execMan.execute(state);
		     } 
                     for(int i =0; i < statelist.size(); i++){
                       refineStatements(statelist.at(i), condTraceList.at(i));
                       Engine::printTrace2(statelist.at(i));
                       Engine::printTATrace(statelist.at(i),vars,absTraceList.at(i),boxTraceList.at(i));
                     }
		} catch (ProgramError& e) {
		throw;
		}
	}

public:

	Engine() : boxMan(),
		compiler_(this->fixpointBackend, this->taBackend, this->boxMan, this->boxes),
		dbgFlag(false) {}

	void loadTypes(const CodeStorage::Storage& stor) {

	    CL_DEBUG_AT(3, "loading types ...");

	    this->boxMan.clear();

		for (auto type : stor.types) {

			std::vector<size_t> v;
			std::string name;

			switch (type->code) {

				case cl_type_e::CL_TYPE_STRUCT:

					NodeBuilder::buildNode(v, type);

					if (type->name)
						name = std::string(type->name);
					else {
						std::ostringstream ss;
						ss << type->uid;
						name = ss.str();
					}

					CL_DEBUG_AT(3, name);

					this->boxMan.createTypeInfo(name, v);
					break;

				default:
					break;

			}

		}

		for (auto fnc : stor.fncs) {

			std::vector<size_t> v;

			for (auto sel : SymCtx(*fnc).sfLayout)
				v.push_back(sel.offset);

			std::ostringstream ss;
			ss << nameOf(*fnc) << ':' << uidOf(*fnc);

			CL_DEBUG_AT(3, ss.str());

			this->boxMan.createTypeInfo(ss.str(), v);

		}

	}
void compile(const CodeStorage::Storage& stor, const CodeStorage::Fnc& entry) {

		CL_DEBUG_AT(2, "compiling ...");
            
		this->compiler_.compile(this->assembly_, stor, entry, vars);
                CL_DEBUG_AT(2, "assembly instructions:" << std::endl << this->assembly_);

	}

	void run() {

		assert(this->assembly_.code_.size());

		this->execMan.clear();

	    CL_CDEBUG(2, "creating empty heap ...");
		// create empty heap
		std::shared_ptr<FAE> fae = std::shared_ptr<FAE>(new FAE(this->taBackend, this->boxMan));

	    CL_CDEBUG(2, "sheduling initial state ...");
		// schedule initial state for processing
		this->execMan.init(
			std::vector<Data>(this->assembly_.regFileSize_, Data::createUndef()),
			fae,
			this->assembly_.code_.front()
		);

		try {

			this->mainLoop();

			this->printBoxes();

			for (auto instr : this->assembly_.code_) {
                             if (instr->getType() != fi_type_e::fiFix)
					continue;
                                std::cerr << "fixpoint at instruction" <<  *instr << instr->insn()->loc << std::endl << ((FixpointInstruction*)instr)->getFixPoint();
			
                        	CL_DEBUG_AT(1, "fixpoint at " << instr->insn()->loc << std::endl << ((FixpointInstruction*)instr)->getFixPoint());

			}

		CL_DEBUG_AT(1, "forester has evaluated " << this->execMan.statesEvaluated() << " state(s) in " << this->execMan.tracesEvaluated() << " trace(s)");

		} catch (std::exception& e) {
			CL_DEBUG(e.what());
			this->printBoxes();
			throw;
		}
	}
	void setDbgFlag() {
		this->dbgFlag = 1;
	}

};
SymExec::SymExec() : engine(new Engine()) {}
SymExec::~SymExec() {
	delete this->engine;
}

void SymExec::loadTypes(const CodeStorage::Storage& stor) {
	this->engine->loadTypes(stor);
}

void SymExec::compile(const CodeStorage::Storage& stor, const CodeStorage::Fnc& main) {
	this->engine->compile(stor, main);
}

void SymExec::run() {
	this->engine->run();
}

void SymExec::setDbgFlag() {
	this->engine->setDbgFlag();
}
