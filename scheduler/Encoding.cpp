#include "Encoding.hpp"
#include "util/threeval.h"
//#include "solver-src/sat/cardinality.h"


std::stringstream formula;

Encoding::Encoding(ITree *it, M *m): bvUtils(slv)
{
  _m = m;
  _it = it;
  last_node = it->_slist[it->_slist.size() -1] ; 
  traceSize = it->_slist.size()-1;
  _deadlock_found = false;
  // instantiating two variables in the solver memory
  one = slv.new_variable();
  zero = slv.new_variable();
  // slv.constraintStream << "one = " << one.get() <<std::endl; 
  // slv.constraintStream << "zero = " << zero.get() <<std::endl; 
  // setting one to true and zero to false
  slv.l_set_to(one, true);
  slv.l_set_to(zero, false);
 
}

std::string Encoding::getLitName (literalt a)
{
  std::stringstream res;
  if( a == one)
    res << "1";
  else if (a ==zero)
    res << "0";
  else{
  StrIntPair MnP= lit2sym.find(a)->second;
  res << "X" << MnP.first << "," << MnP.second;
  }
  return res.str();
}

void Encoding::createMatchSet()
{
  
  // for non-SR matches
  for(int i =0 ; i < _it->_slist.size()-1; i++){
    CB front = _it->_slist[i]->curr_match_set.front();
    Transition *t = _it->_slist[i]->GetTransition(front);
    Envelope *env = t->GetEnvelope();
    // check whether match is a non send-recv one
    if( env->isCollectiveType() &&  !(env->func_id == FINALIZE)){
      matchSet.push_back(&(_it->_slist[i]->curr_match_set));
    }
  }
  //for SR matches
  _MIterator mit, mitend;
  mitend = _m->_MSet.end();
  for (mit = _m->_MSet.begin(); mit != mitend; mit++){
    assert(!(*mit).second.empty());
    matchSet.push_back(&((*mit).second));
  }
}

void Encoding::printMatchSet()
{
  formula << "**********MATCHSET*************" << std::endl;
  formula << "MatchSet Size =" << matchSet.size() << std::endl;
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
      formula << (*lit);
    }
    formula << std::endl;
  }
  
}



////////////////////////////////////////////////////////////
/////                                                ///////
////        ENCODING 0                               ///////
////////////////////////////////////////////////////////////


void Encoding0::createMatchLiterals()
{
  /* 
     TRICK: Write to a stringstream: appending it with numbers
     the way you want and write the contents of a stringstream 
     back to an integer -- quick hack to just juxtapose numerals.
   */
  
  std::stringstream uniquepair;
  std::string matchNumeral;
  
  for(int i = 0; i < traceSize-1; i++){
    
    forall_matchSet(mit, matchSet){
      
      literalt lt = slv.new_variable();
      
      
      forall_match(lit, (**mit)){
	uniquepair<<(*lit)._pid;
	uniquepair<<(*lit)._index;
      }
      //      uniquepair << "_" << i; 
      //uniquepair >> matchNumeral; 
      matchNumeral = uniquepair.str();

      // clear out uniquepair
      uniquepair.str("");
      uniquepair.clear();      

      //debug print
      //std::cout << " =====DEBUG PRINT START: unique symbol=====" <<std::endl; 
      //std::cout << "uniquepair: " << matchNumeral << ":" << i <<std::endl;
      //  std::cout << " =====DEBUG PRINT END=====" <<std::endl; 
      
      //insert in to the map
      lit2sym.insert(std::pair<literalt, StrIntPair> (lt, StrIntPair(matchNumeral, i)));
      sym2lit.insert(std::pair<StrIntPair, literalt> (StrIntPair(matchNumeral, i), lt));
      match2sym.insert(std::pair<MatchPtr, StrIntPair> (*mit, StrIntPair(matchNumeral, i)));
      
      //debug print
      //std::cout << " =====DEBUG PRINT START: matchSym Entry=====" <<std::endl; 
      // std::cout << "match2sym entry: " << (*mit) << ", " << matchNumeral << ":" 
      // << i <<std::endl;
      // std::cout << " =====DEBUG PRINT END=====" <<std::endl; 
 
    }
  }
}

literalt Encoding0::getLiteralFromMatches(MatchPtr mptr, int pos)
{
  int  position;
  std::string matchNumeral;
  literalt res;

  std::pair<std::multimap<MatchPtr, StrIntPair>::iterator, 
	    std::multimap<MatchPtr, StrIntPair>::iterator > ret; 
  ret = match2sym.equal_range(mptr);
  
  for(std::multimap<MatchPtr, StrIntPair>::iterator iter = ret.first;
      iter != ret.second; iter++){
    
    matchNumeral = (*iter).second.first;
    position = (*iter).second.second;
    
    if(position == pos){

      // debug print
      //std::cout << " =====DEBUG PRINT START: literal=====" <<std::endl; 
      //std::cout << res << std::endl;
      //std::cout << " =====DEBUG PRINT END: literal=====" <<std::endl; 
      res = sym2lit.find(StrIntPair(matchNumeral, pos))->second;
      return res;
    }
  }
  // requires check at callee site whether returned value makes sense
  return res;
}

literalt Encoding0::uniqueAtPosition()
{
  literalt x_ap, x_bp;
  bvt rhs,lhs_rhs; // res;
  
   
  ///////////////////////////////////////////////////////////////////
  formula << "****UniqueAtPosition****" << std::endl;

  for(int i = 0; i < traceSize-1; i++){
    forall_matchSet(mit, matchSet){
      // get the literal, matchNumeral, pos entry for the match 
      x_ap = getLiteralFromMatches(*mit, i);
      StrIntPair x_ap_MatchPos = lit2sym.find(x_ap)->second;
      
      // debug print to ostream
      formula << getLitName(x_ap) << " => "; 
      
      forall_matchSet(mit1, matchSet){
	x_bp = getLiteralFromMatches(*mit1, i);
	StrIntPair x_bp_MatchPos = lit2sym.find(x_bp)->second;
	/* x_bp and x_ap should share the same position but should have 
	   different match numerals
	*/
	if(x_bp_MatchPos.second == x_ap_MatchPos.second && 
	   x_bp_MatchPos.first.compare(x_ap_MatchPos.first) != 0 ) {
	  rhs.push_back(slv.lnot(x_bp));
	  // debug print to ostream
	  formula << "¬" << getLitName(x_bp) << "/\\";
	}
      }
      lhs_rhs.push_back(slv.limplies(x_ap, slv.land(rhs)));
      // debug print to ostream
      formula << std::endl;
      rhs.clear();
    }
    //res.push_back(slv.land(lhs_rhs));
    //lhs_rhs.clear();
  }
  
  ///////////////////////////////////////////////////////////////////////
  
  return slv.land(lhs_rhs); 
}


literalt Encoding0::noRepetition()
{
  
  literalt x_ap, x_bpdash;
  bvt rhs, rhsFinal, lhs_rhs;
  
  bool flag = false;

  //////////////////////////////////////////////////////////////////////
  formula << "****noRepetition****" << std::endl;
  for(int i = 0; i < traceSize -1; i++){
    forall_matchSet(mit, matchSet){
      x_ap = getLiteralFromMatches(*mit, i);
      
      // debug print to ostream
      formula << getLitName(x_ap) << "=>"; 
      
      for(int j = 0; j < i; j++){
	forall_matchSet(mitN, matchSet){
	  x_bpdash = getLiteralFromMatches(*mitN, j);
	  forall_match(lit, (**mit)){
	    forall_match(litN, (**mitN)){
	      if((*lit) == (*litN)){
		flag = true; 
		goto RHS;
	      }
	    }
	  }
	RHS: if(flag) {
	    rhs.push_back(slv.lnot(x_bpdash)); 
	    // debug print to ostream
	    formula << "¬" << getLitName(x_bpdash) << "/\\"; 
	    flag = false;
	  }
	}
      }
      if(rhs.size() ==  0){
	rhs.push_back(one); 
	// debug print to ostream
	formula << getLitName(one) ; 
	
      }
      lhs_rhs.push_back(slv.limplies(x_ap, slv.land(rhs)));
      rhs.clear();
      // debug print to ostream
      formula << std::endl;
    }
  }
  ///////////////////////////////////////////////////////////////////
  return slv.land(lhs_rhs);
}
 
literalt Encoding0::partialOrder()
{

  literalt x_ap, x_bpdash;
  bvt rhs, rhsFinal, lhs_rhs ;
  
  bool flag = false;
  bool ancestor = false;

  ///////////////////////////////////
  formula << "****partialOrder****" << std::endl;
  for(int i = 0; i < traceSize -1; i++){
    forall_matchSet(mit, matchSet){
      x_ap = getLiteralFromMatches(*mit, i);
      
      // debug print to ostream
      formula << getLitName(x_ap) << "=>"; 
      
      forall_transitionLists(iter, last_node->_tlist){
	forall_transitions(titer, (*iter)->_tlist){
	  Envelope *envB = (*titer).GetEnvelope();
	  if(envB->func_id == FINALIZE) continue; // skip the loop for the finalize event
	  CB B(envB->id, envB->index);

	  forall_match(lit, (**mit)){
	    if(last_node->isAncestor((*lit), B)){
	      ancestor = true; 
	      break;
	    }
	  }
	  if(ancestor){
	    // debug print to ostream
	    formula << "(";
	    for(int j = 0; j < i; j++){
	      forall_matchSet(mitN, matchSet){
		x_bpdash = getLiteralFromMatches(*mitN, j);
		forall_match(lit, (**mitN)){
		  if((*lit)._pid == envB->id && (*lit)._index == envB->index){ 
		    flag = true; break;
		  }
		}
		if(flag) {
		  rhs.push_back(x_bpdash); 
		  // debug print to ostream
		  formula << getLitName(x_bpdash) << "\\/";
		  flag = false;
		}
	      }
	    }
	    ancestor = false;
	    // debug print to ostream
	    formula << ") /\\";
	  }
	  if(rhs.size()){
	    rhsFinal.push_back(slv.lor(rhs));
	    rhs.clear();
	  }
	}
      }
      if(rhsFinal.size() == 0){
	rhsFinal.push_back(one);
	// debug print to ostream
	formula << getLitName(one) ;
      }
      lhs_rhs.push_back(slv.limplies(x_ap, slv.land(rhsFinal)));
      rhsFinal.clear();
      // debug print to ostream
      formula << std::endl;
    }
  }
  ///////////////////////////////////////
  return slv.land(lhs_rhs);

}

literalt Encoding0::extensionNextPos ()
{
  bool flag, ancestor;
  flag = false;
  ancestor = false;
  
  literalt x_ap, x_bpdash;
  bvt rhs,rhsA, lhs_rhs;

 //////////////////////////////////
  formula << "****extensionNextPos****" << std::endl;
  int i = traceSize -2;
  forall_matchSet(mit, matchSet){
    x_ap = getLiteralFromMatches(*mit, i);
    
    // debug print to ostream
    formula << getLitName(x_ap) << " <=> "; 
    
    forall_transitionLists(iter, last_node->_tlist){
      forall_transitions(titer, (*iter)->_tlist){
	Envelope *envB = (*titer).GetEnvelope();
	if(envB->func_id == FINALIZE) continue; // skip the loop for the finalize event
	CB B(envB->id, envB->index);
	forall_match(lit, (**mit)){
	  if(last_node->isAncestor((*lit), B)){
	    ancestor = true; 
	    break;
	  }
	}
	if(ancestor){
	  // debug print to ostream
	  formula << "(";
	  for(int j = 0; j < i; j++){
	    forall_matchSet(mitN, matchSet){
	      x_bpdash = getLiteralFromMatches(*mitN, j);
	      forall_match(lit, (**mitN)){
		if((*lit)._pid == envB->id && (*lit)._index == envB->index){ 
		  flag = true; break;
		}
	      }
	      if(flag) {
		rhs.push_back(x_bpdash); 
		// debug print to ostream
		formula << getLitName(x_bpdash) << "\\/";
		flag = false;
	      }
	    }
	  }
	  ancestor = false;
	  // debug print to ostream
	  formula << ") /\\";
	}
	if(rhs.size()){
	  rhsA.push_back(slv.lor(rhs));
	  rhs.clear();
	}
      }
    }
    
    // debug print to ostream
    formula << "("; 
    
    for(int j = 0; j < i; j++){
      forall_matchSet(mitN, matchSet){
	x_bpdash = getLiteralFromMatches(*mitN, j);
	forall_match(lit, (**mit)){
	  forall_match(litN, (**mitN)){
	    if((*lit) == (*litN)){
	      flag = true; 
	      goto RHS;
	    }
	  }
	}
      RHS: if(flag) {
	  rhsA.push_back(slv.lnot(x_bpdash)); 
	  // debug print to ostream
	  formula << "¬" << getLitName(x_bpdash) << "/\\"; 
	  flag = false;
	}
      }
    }
    // svs: FIX TODO-- check the size of rhsA
    lhs_rhs.push_back(slv.land(slv.limplies(slv.land(rhsA), x_ap), 
			       slv.limplies(x_ap, slv.land(rhsA))));
    rhsA.clear();
    // debug print to ostream
    formula << ")"; 
    formula << std::endl;
    
  }
    
  //////////////////////////////////
  
  return slv.land(lhs_rhs); 
}

literalt Encoding0::noMatchAtNextPos()
{
  int i = traceSize-2;
  literalt x_ap; 
  bvt res;
  //////////////////////////////////
  formula << "****noMatchAtNextPos****" << std::endl;
 
  forall_matchSet(mit, matchSet){
    x_ap = getLiteralFromMatches(*mit, i);
    
    // debug print to ostream
    formula << "¬" << getLitName(x_ap) << "/\\";
    
    res.push_back(slv.lnot(x_ap));
    //slv.l_set_to(slv.lnot(x_ap), true);
  }
  
  // debug print to ostream
  formula <<std::endl;
  
  //////////////////////////////////
  return slv.land(res);
}

void Encoding0::publish()
{
 tvt result;
  literalt x_ap;

  for(int i = 0; i < traceSize -1; i++){
    forall_matchSet(mit, matchSet){
      x_ap = getLiteralFromMatches(*mit, i);
      switch(slv.l_get(x_ap).get_value()){ 
      case tvt::TV_TRUE:
	formula << getLitName(x_ap) << ":1" << std::endl;
	break;
      case tvt::TV_FALSE:
	formula << getLitName(x_ap) << ":0" << std::endl;
	break;
      case tvt::TV_UNKNOWN:
	formula << getLitName(x_ap) << ":UNKNOWN" << std::endl;
	break;
      default: assert(false);
      }
    }
  }
}

void Encoding0::Encoding_Matches()
{
  bvt res; 
  
  // creating match set and associated literals.
  createMatchSet();
  createMatchLiterals();

  res.push_back(uniqueAtPosition());
  res.push_back(noRepetition());
  res.push_back(partialOrder());
  res.push_back(extensionNextPos());
  res.push_back(noMatchAtNextPos());
  
  slv.l_set_to(slv.land(res), true);
  
  satcheckt::resultt answer = slv.prop_solve();
  
  switch(answer){
  case satcheckt::P_UNSATISFIABLE:
    std::cout << "Formula is UNSAT" <<std::endl;
    break;
  case satcheckt::P_SATISFIABLE:
    std::cout << "Formula is SAT -- DEADLOCK DETECTED" <<std::endl;
    publish();
    break;
    // output the valuations
  default: 
    std::cout << "ERROR in SAT SOLVING" <<std::endl;
    break;
  }
  std::cout << formula.str();
  std::cout << std::endl;
			       

}



////////////////////////////////////////////////////////////
/////                                                ///////
////        ENCODING 1                               ///////
////////////////////////////////////////////////////////////



void Encoding1::createEventLiterals()
{
  
  std::stringstream uniquepair;
  std::string eventNumeral;
  
  for(int i = 0; i < traceSize-1; i++){
    forall_transitionLists(iter, last_node->_tlist){
      forall_transitions(titer, (*iter)->_tlist){
	Envelope *env = (*titer).GetEnvelope();
	if(env->func_id == FINALIZE) continue;
	uniquepair << env->id;
	uniquepair << env->index;
	//uniquepair >> eventNumeral;
	eventNumeral = uniquepair.str();

	// clear out uniquepair
	uniquepair.str("");
	uniquepair.clear();      
	
	
	literalt lt = slv.new_variable();
	
	//insert in to the map
	lit2sym.insert(std::pair<literalt, StrIntPair> (lt, StrIntPair(eventNumeral, i)));
	sym2lit.insert(std::pair<StrIntPair, literalt> (StrIntPair(eventNumeral, i), lt));
      }
    }
  }
}


literalt Encoding1::getLiteralFromEvents(TIter tit, int pos)
{
  literalt res; 
  Envelope *env = (*tit).GetEnvelope();
  std::stringstream uniquepair;
  uniquepair << env->id << env->index;
  
  res = sym2lit.find(StrIntPair(uniquepair.str(), pos))->second;
  return res;
}

literalt Encoding1::getLiteralFromCB(CB a, int pos)
{
  std::stringstream p; 
  p << a._pid << a._index;

  std::string eventNumeral;
  //p >> eventNumeral;
  eventNumeral = p.str();

  StrIntPair pair(eventNumeral, pos);
  
  literalt res = sym2lit.find(pair)->second;
  
  return res;
}


void Encoding1::uniqueAtPosition()
{
  literalt x_ap, x_bp; 
  bvt lhs, rhs;
  bool flag =false;
  ////////////////////////////////////////////
  // debug print to ostream
  formula << "****uniqueAtPosition****" << std::endl; 
    
  for(int i = 0; i < traceSize-1; i++){
    forall_matchSet(mit, matchSet){
      formula << "(";
      forall_match(lit, (**mit)) {
	x_ap = getLiteralFromCB((*lit), i); 
	formula << getLitName(x_ap) << "/\\";
	lhs.push_back(x_ap);
      }
      formula << ") =>";
      forall_transitionLists(iter, last_node->_tlist){
	forall_transitions(titer, (*iter)->_tlist){
	  x_bp = getLiteralFromEvents(titer, i);
	  if((*titer).GetEnvelope()->func_id == FINALIZE) continue;
	  //	  if(x_ap == x_bp) continue;
	  for(bvt::iterator bit = lhs.begin(), bitend = lhs.end(); 
	      bit != bitend; bit++){
	    if((*bit) == x_bp){ flag =true; break;}
	  }
	  if(flag) { flag = false; continue;}
	  else{
	    rhs.push_back(slv.lnot(x_bp));
	    formula << "¬" << getLitName(x_bp) << "/\\";
	  }
	}
      }
      slv.l_set_to(slv.limplies(slv.land(lhs), slv.land(rhs)), true); 
      lhs.clear();
      rhs.clear();
      formula << std::endl;
    }
  }
  ///////////////////////////////////////////
  
}

void Encoding1::noRepetition()
{
  literalt x_ap, x_aprime;
  bvt rhs;
  
  /////////////////////////////////////////
  formula << "****noRepetition****" << std::endl; 
  for(int i = 0; i < traceSize-1; i++){
    forall_transitionLists(iter, last_node->_tlist){
      forall_transitions(titer, (*iter)->_tlist){
	x_ap = getLiteralFromEvents(titer, i);
	if((*titer).GetEnvelope()->func_id == FINALIZE) continue;
	formula << getLitName(x_ap) << " => ";
	for(int j=0; j<i; j++){
	  x_aprime = getLiteralFromEvents(titer, j);
	  rhs.push_back(slv.lnot(x_aprime));
	  formula << "¬" << getLitName(x_aprime) << "/\\";
	}
	if(rhs.size()){
	  slv.l_set_to(slv.limplies(x_ap, slv.land(rhs)), true);
	  rhs.clear();
	}
	else {
	  slv.l_set_to(slv.limplies(x_ap, one), true);
	  formula << getLitName(one) << "/\\";
	}
	formula << std::endl; 
      }
    }
  }
  ////////////////////////////////////////
}

void Encoding1::partialOrder()
{
  literalt x_ap, x_bprime;
  bvt rhs;
  //////////////////////////////////////
  formula << "****PartialOrder****" << std::endl; 
  for(int i = 0; i < traceSize-1; i++){
    forall_transitionLists(iter, last_node->_tlist){
      forall_transitions(titer, (*iter)->_tlist){
	if((*titer).GetEnvelope()->func_id == FINALIZE) continue;
	x_ap = getLiteralFromEvents(titer,i);
	Envelope *envA = (*titer).GetEnvelope();
	CB A(envA->id, envA->index);
	forall_transitions(titerN, (*iter)->_tlist){
	  Envelope *envB = (*titerN).GetEnvelope();
	  if(envB->func_id == FINALIZE) continue;
	  CB B(envB->id, envB->index);
	  if(last_node->isAncestor(A,B)){
	    formula << getLitName(x_ap) << " => ";
	    for(int j=0; j<i; j++){
	      x_bprime = getLiteralFromEvents(titerN, j);
	      formula << getLitName(x_bprime) << "\\/";
	      rhs.push_back(x_bprime);
	    }
	    if(rhs.size()){
	      slv.l_set_to(slv.limplies(x_ap, slv.lor(rhs)), true);
	      rhs.clear();
	    }   
	    else {
	      slv.l_set_to(slv.limplies(x_ap, zero), true);
	      formula << getLitName(zero);
	    }
	    formula << std::endl;
	  }
	}
      }
    }
  }
  ////////////////////////////////////
}


void Encoding1::stutteringAtPosition()
{
  literalt x_ap, x_bp; 
  bool flag = false;
  bvt rhs, rhsFinal;
  
  ////////////////////////////////////////////////
  formula << "****stutteringAtPosition****" << std::endl; 
  for(int i = 0; i < traceSize-1; i++){
    forall_transitionLists(iter, last_node->_tlist){
      forall_transitions(titer, (*iter)->_tlist){
	x_ap = getLiteralFromEvents(titer, i);
	if((*titer).GetEnvelope()->func_id == FINALIZE) continue;
	formula << getLitName(x_ap) << " => ";
	forall_matchSet(mit, matchSet){
	  formula << "(";
	  forall_match(lit, (**mit)){
	    x_bp = getLiteralFromCB((*lit), i);
	    rhs.push_back(x_bp);
	    if(x_ap == x_bp) flag = true;
	  }
	  if(flag){
	    rhsFinal.push_back(slv.land(rhs));
	    for(bvt::iterator bit = rhs.begin(); bit != rhs.end(); bit++){
	      formula << getLitName(*bit) << "/\\";
	    }
	    flag = false;
	  }
	  formula << ") \\/ ";
	  rhs.clear();
	}
	if(rhsFinal.size()){
	  slv.l_set_to( slv.limplies(x_ap, slv.lor(rhsFinal)), true);
	  rhsFinal.clear();
	}
	formula << std::endl;
      }
    }
  }
  ///////////////////////////////////////////////
}

void Encoding1::extensionNextPos()
{
  int i = traceSize-2;
  literalt x_ap, x_bpdash, x_apdash;
  bvt lhs, rhsA, rhsB, temp;
  //////////////////////////////////////
  formula << "****extensionNextPos****" << std::endl; 
  forall_matchSet(mit, matchSet){
    formula << "(" ; 
    forall_match(lit, (**mit)) {    
      x_ap = getLiteralFromCB((*lit), i);
      formula << getLitName(x_ap) << " /\\";
      lhs.push_back(x_ap); 
    }
    formula << ") <=> (" ;
    forall_match(lit, (**mit)) {
      for(int j=0; j < i; j++){
	x_apdash = getLiteralFromCB((*lit), j);
	rhsB.push_back(slv.lnot(x_apdash));
	formula << "¬" << getLitName(x_apdash) << "/\\";
      } 
      if(rhsB.empty()){
	rhsB.push_back(one); 
	formula << getLitName(one) << "/\\";
      }
    }
    formula << ") /\\ (" ;
    forall_match(lit, (**mit)){
      forall_transitionLists(iter, last_node->_tlist){
	forall_transitions(titer, (*iter)->_tlist){
	  Envelope *envB = (*titer).GetEnvelope();
	  if(envB->func_id == FINALIZE) continue;	  
	  CB B (envB->id, envB->index);
	  if(last_node->isAncestor((*lit),B)){
	    formula << "(" ;
	    for (int j=0; j<i; j++){
	      x_bpdash = getLiteralFromEvents(titer, j);
	      temp.push_back(x_bpdash);
	      formula << getLitName(x_bpdash) << "\\/";
	    }
	   
	    if(!temp.empty()){
	      formula << ") /\\";
	      rhsA.push_back(slv.lor(temp));
	      temp.clear();
	    }
	    else{
	      rhsA.push_back(zero);
	      formula << getLitName(zero) << ") /\\";
	    }
	  }
	}
      }
    }
    // if(rhsA.empty()){
    //   rhsA.push_back(one);
    //   formula << getLitName(one) << ") /\\";
    // }
    if(!rhsA.empty())
      rhsB.push_back(slv.land(rhsA));

    slv.l_set_to(slv.land(slv.limplies(slv.land(lhs), slv.land(rhsB)), 
			  slv.limplies(slv.land(rhsB), slv.land(lhs))), true);
    rhsB.clear();
    lhs.clear();
    rhsA.clear();
    formula << std::endl;
  }
  /////////////////////////////////////
  
}


void Encoding1::noMatchAtNextPos()
{
  int i = traceSize-2;
  literalt x_ap;
  bvt res, resF;
  /////////////////////////////////////
  formula << "****noMatchAtNextPos****" << std::endl; 
  forall_matchSet(mit, matchSet){
    formula << "(";
    forall_match(lit, (**mit)) {    
      x_ap = getLiteralFromCB((*lit), i);
      res.push_back(slv.lnot(x_ap));
      formula << "¬" << getLitName(x_ap) << "\\/";
    }
    formula << ") /\\";
    resF.push_back(slv.lor(res)); 
    res.clear();
  }
  formula <<std::endl;
  slv.l_set_to(slv.land(resF), true);
 /////////////////////////////////////

}

void Encoding1::publish()
{
 tvt result;
  literalt x_ap;
  

  for(int i = 0; i < traceSize -1; i++){
    forall_transitionLists(iter, last_node->_tlist){
      forall_transitions(titer, (*iter)->_tlist){
	if((*titer).GetEnvelope()->func_id == FINALIZE) continue;
	x_ap = getLiteralFromEvents(titer, i);
	switch(slv.l_get(x_ap).get_value()){ 
	case tvt::TV_TRUE:
	  formula << getLitName(x_ap) << ":1" << std::endl;
	  break;
	case tvt::TV_FALSE:
	  formula << getLitName(x_ap) << ":0" << std::endl;
	  break;
	case tvt::TV_UNKNOWN:
	  formula << getLitName(x_ap) << ":UNKNOWN" << std::endl;
	  break;
	default: assert(false);
	}
      }
    }
  }
}

void Encoding1::Encoding_Events()
{
  // creating match set and associated literals.
  createMatchSet();
  createEventLiterals();
  gettimeofday(&constGenStart, NULL);  
  uniqueAtPosition();
  noRepetition();
  partialOrder();
  stutteringAtPosition();
  extensionNextPos();
  noMatchAtNextPos();
  gettimeofday(&constGenEnd, NULL);  
  std::cout << formula.str();
  std::cout << std::endl;
  
  formula.str("");
  formula.clear();
  
  gettimeofday(&solverStart, NULL);
  satcheckt::resultt answer = slv.prop_solve();
  gettimeofday(&solverEnd, NULL);

  formula << "Number of Clauses: " << slv.no_clauses() << std::endl;
  formula << "Number of Variables: " << slv.no_variables() << std::endl;
  formula << "Constraint Generation Time: "
	  << (getTimeElapsed(constGenStart, constGenEnd)*1.0)/1000000 << "sec \n";
  formula << "Solving Time: " << (getTimeElapsed(solverStart, solverEnd)*1.0)/1000000 << "sec \n";
  

  switch(answer){
  case satcheckt::P_UNSATISFIABLE:
    formula << "Formula is UNSAT" <<std::endl;
    break;
  case satcheckt::P_SATISFIABLE:
    formula  << "Formula is SAT -- DEADLOCK DETECTED" <<std::endl;
    publish();
    break;
    // output the valuations
  default: 
    formula << "ERROR in SAT SOLVING" <<std::endl;
    break;
  }

  std::cout << formula.str();
  std::cout << std::endl;
  
}


////////////////////////////////////////////////////////////
/////                                                ///////
////        ENCODING 2                               ///////
////////////////////////////////////////////////////////////

void Encoding2::createMatchLiterals()
{
  std::stringstream uniquepair;
  std::string matchNumeral;
  bool flag = false;

  for(int i = 0; i < traceSize-1; i++){
    forall_matchSet(mit, matchSet){
      forall_match(lit, (**mit)){
	uniquepair<<(*lit)._pid;
	uniquepair<<(*lit)._index;
	if(last_node->GetTransition((*lit))->GetEnvelope()->isCollectiveType()) 
	  flag = true;
      }
      if(flag){ // add only collective match-literals
	matchNumeral = uniquepair.str();
	flag = false;
	literalt lt = slv.new_variable();
	//insert in to the map
	lit2sym.insert(std::pair<literalt, StrIntPair> (lt, StrIntPair(matchNumeral, i)));
	sym2lit.insert(std::pair<StrIntPair, literalt> (StrIntPair(matchNumeral, i), lt));
	match2sym.insert(std::pair<MatchPtr, StrIntPair> (*mit, StrIntPair(matchNumeral, i)));
      }
      // clear out uniquepair
      uniquepair.str("");
      uniquepair.clear();      
    }
  }
}

void Encoding2::createEventLiterals()
{
  std::stringstream uniquepair;
  std::string eventNumeral;

  for(int i = 0; i < traceSize-1; i++){
    forall_transitionLists(iter, last_node->_tlist){
      forall_transitions(titer, (*iter)->_tlist){
	Envelope *env = (*titer).GetEnvelope();
	if(env->func_id == FINALIZE) continue;

	if(!(env->isCollectiveType())){ 
	  uniquepair << env->id;
	  uniquepair << env->index;
	  //uniquepair >> eventNumeral;
	  eventNumeral = uniquepair.str();
	  literalt lt = slv.new_variable();
	  
	  //insert in to the map
	  lit2sym.insert(std::pair<literalt, StrIntPair> (lt, StrIntPair(eventNumeral, i)));
	  sym2lit.insert(std::pair<StrIntPair, literalt> (StrIntPair(eventNumeral, i), lt));
	}
	  // clear out uniquepair
	uniquepair.str("");
	uniquepair.clear();      
      }
    }
  }
}

literalt Encoding2::getLiteralFromEvents(TIter tit, int pos)
{
  literalt res; 
  Envelope *env = (*tit).GetEnvelope();
  std::stringstream uniquepair;
  uniquepair << env->id << env->index;
  
  res = sym2lit.find(StrIntPair(uniquepair.str(), pos))->second;
  return res;
}

literalt Encoding2::getLiteralFromCB(CB a, int pos)
{
  std::stringstream p; 
  p << a._pid << a._index;

  std::string eventNumeral;
  //p >> eventNumeral;
  eventNumeral = p.str();

  StrIntPair pair(eventNumeral, pos);
  
  literalt res = sym2lit.find(pair)->second;
  
  return res;
}

literalt Encoding2::getLiteralFromMatches(MatchPtr mptr, int pos)
{
  int  position;
  std::string matchNumeral;
  literalt res;

  std::pair<std::multimap<MatchPtr, StrIntPair>::iterator, 
	    std::multimap<MatchPtr, StrIntPair>::iterator > ret; 
  ret = match2sym.equal_range(mptr);
  
  for(std::multimap<MatchPtr, StrIntPair>::iterator iter = ret.first;
      iter != ret.second; iter++){
    
    matchNumeral = (*iter).second.first;
    position = (*iter).second.second;
    
    if(position == pos){
      res = sym2lit.find(StrIntPair(matchNumeral, pos))->second;
      return res;
    }
  }
  // requires check at callee site whether returned value makes sense
  return res;
}

MatchPtr Encoding2::getMatchPtrFromEvent(CB a)
{
  bool flag = false;
  MatchPtr res;
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
      if((*lit) == a){
	flag = true;
	break;
      }
    }
    if(flag) {
      res = *mit;
      break;
    }
  }
  return res;
}


void Encoding2::uniqueAtPosition()
{
  literalt x_ap, x_bp, x_np; 
  bvt lhs, rhs, rhsPrint;
  bool collective = false;
  bool flag = false;
  ////////////////////////////////////////////
  // debug print to ostream
  formula << "****uniqueAtPosition****" << std::endl; 
    
  for(int i = 0; i < traceSize-1; i++){
    forall_matchSet(mit, matchSet){

      forall_match(lit, (**mit)) {
	if(!(last_node->GetTransition(*lit)->GetEnvelope()->isCollectiveType())){
	  x_ap = getLiteralFromCB((*lit), i); 
	  lhs.push_back(x_ap);
	}
	else {
	  collective = true; 
	  break;
	}
      }
      if(!collective){ // matched events are not collective
	assert(lhs.size() != 0);
	forall_transitionLists(iter, last_node->_tlist){
	  forall_transitions(titer, (*iter)->_tlist){
	    if((*titer).GetEnvelope()->isCollectiveType() ||
	       (*titer).GetEnvelope()->func_id == FINALIZE) continue;
	    x_bp = getLiteralFromEvents(titer, i);
	    for(bvt::iterator bit = lhs.begin(), bitend = lhs.end(); 
		bit != bitend; bit++){
	      if((*bit) == x_bp){ flag =true; break;}
	    }
	    if(flag) { flag = false; continue;}
	    else{
	      rhs.push_back(slv.lnot(x_bp));
	      rhsPrint.push_back(x_bp);
	    }
	  }
	}
	forall_matchSet(mitN, matchSet){
	  forall_match(lit, (**mitN)){
	    if(last_node->GetTransition(*lit)->GetEnvelope()->isCollectiveType()){
	      flag = true;
	      break;
	    }
	  }
	  if(flag){
	    x_np = getLiteralFromMatches(*mitN, i);
	    rhs.push_back(slv.lnot(x_np));
	    rhsPrint.push_back(x_np);
	    flag=false;
	  }
	}
	if(!rhs.empty()){
	  //formula output
	  formula << "((";
	  for(bvt::iterator bit = lhs.begin(); bit != lhs.end(); bit++){
	    formula << getLitName(*bit) << " & ";
	  }
	  formula << ") -> ("; 
	  for(bvt::iterator bit = rhsPrint.begin(); bit != rhsPrint.end(); bit++){
	    formula << "!" << getLitName(*bit) << " & ";
	  }
	  formula << ")) &" << std::endl; 
	  
	  slv.l_set_to(slv.limplies(slv.land(lhs),slv.land(rhs)) , true); 
	  rhs.clear();
	  rhsPrint.clear();
	}
	lhs.clear();
      }
      else{ // for collective events
	x_np = getLiteralFromMatches(*mit, i);
	forall_matchSet(mitN, matchSet){
	  x_bp = getLiteralFromMatches(*mitN,i);
	  forall_match(lit, (**mitN)){
	    if(last_node->GetTransition(*lit)->GetEnvelope()->isCollectiveType()){
	      flag = true;
	      break;
	    }
	  }
	  if(flag){
	    if(x_bp != x_np){
	      rhs.push_back(slv.lnot(x_bp));
	      rhsPrint.push_back(x_bp);
	    }
	    flag=false;
	  }
	}
	forall_transitionLists(iter, last_node->_tlist){
	  forall_transitions(titer, (*iter)->_tlist){
	    if((*titer).GetEnvelope()->isCollectiveType() ||
	       (*titer).GetEnvelope()->func_id == FINALIZE) continue;
	    x_ap = getLiteralFromEvents(titer, i);
	    rhs.push_back(slv.lnot(x_ap));
	    rhsPrint.push_back(x_ap);
	  }
	}
	if(!rhs.empty()){
	  //formula output
	  formula << "(";
	  formula << getLitName(x_np);
	  formula << " -> ("; 
	  for(bvt::iterator bit = rhsPrint.begin(); bit != rhsPrint.end(); bit++){
	    formula << "!" << getLitName(*bit) << " & ";
	  }
	  formula << ")) &" << std::endl; 

	  slv.l_set_to(slv.limplies(x_np, slv.land(rhs)), true);
	  rhs.clear();
	  rhsPrint.clear();
	}
	collective =false;
      }
    }
  }
  ///////////////////////////////////////////
  
}

void Encoding2::noRepetition()
{
  literalt x_ap, x_apdash;
  bvt rhs;
  bvt rhsPrint;
  bool flag = false;
  bool flag1 = false;
  ////////////////////////////////////////////
  formula << "****noRepetition****" << std::endl; 

  for(int i = 0; i < traceSize-1; i++){
    forall_transitionLists(iter, last_node->_tlist){
      forall_transitions(titer, (*iter)->_tlist){
	if((*titer).GetEnvelope()->isCollectiveType() ||
	   (*titer).GetEnvelope()->func_id == FINALIZE) continue;
	x_ap = getLiteralFromEvents(titer, i);
	for (int j = 0; j < i ; j++){
	  x_apdash = getLiteralFromEvents(titer, j);
	  rhs.push_back(slv.lnot(x_apdash));
	  rhsPrint.push_back(x_apdash);
	}
	if(!rhs.empty())
	  slv.l_set_to(slv.limplies(x_ap, slv.land(rhs)), true);
	else {
	  slv.l_set_to(slv.limplies(x_ap, one), true);
	}
	// // formula output
	formula << "(" << getLitName(x_ap) << " -> ( ";
	if(!rhsPrint.empty())
	  for(bvt::iterator bit = rhsPrint.begin(); bit != rhsPrint.end(); bit++){
	    formula << "!" << getLitName(*bit) << " & ";
	  }       
	else
	  formula << getLitName(one);
	formula << ")) & " << std::endl;
	rhs.clear();
	rhsPrint.clear();
      }
    }
    
    forall_matchSet(mit, matchSet){
      forall_match(lit, (**mit)){
	if(last_node->GetTransition(*lit)->GetEnvelope()->isCollectiveType()){
	  flag = true;
	  break;
	}	
      }
      if (flag){
	x_ap = getLiteralFromMatches(*mit, i);
	for (int j = 0; j <i; j ++){
	  x_apdash = getLiteralFromMatches(*mit, j);
	  rhs.push_back(slv.lnot(x_apdash));
	  rhsPrint.push_back(x_apdash);
	}
	if(!rhs.empty())
	  slv.l_set_to(slv.limplies(x_ap, slv.land(rhs)), true);
	else 
	  slv.l_set_to(slv.limplies(x_ap, one), true);

	// // formula output
	formula <<"(" << getLitName(x_ap) << " -> ( ";
	if(!rhs.empty())
	  for(bvt::iterator bit = rhsPrint.begin(); bit != rhsPrint.end(); bit++){
	    formula << "!" << getLitName(*bit) << " & ";
	  }       
	else
	  formula << getLitName(one);
	formula << ")) & " << std::endl;
	
	rhs.clear();
	rhsPrint.clear();	
	flag = false;
      }
    }
  }
  ////////////////////////////////////////////

}

void Encoding2::partialOrder()
{
  bvt rhs;
  literalt x_ap, x_bp;

  ////////////////////////////////////////////
  formula << "****partialOrder****" << std::endl; 

  for(int i = 0; i < traceSize-1; i++){

    forall_transitionLists(iter, last_node->_tlist){
      forall_transitions(titer, (*iter)->_tlist){
	if((*titer).GetEnvelope()->func_id == FINALIZE) continue;
	else if(!((*titer).GetEnvelope()->isCollectiveType())){
	  x_ap = getLiteralFromEvents(titer, i);
	  CB A(titer->GetEnvelope()->id, titer->GetEnvelope()->index);
	  forall_transitions(titerN, (*iter)->_tlist){
	    if((*titerN).GetEnvelope()->func_id == FINALIZE) continue;
	    CB B(titerN->GetEnvelope()->id, titerN->GetEnvelope()->index);
	    if(last_node->isAncestor(A, B)){
	      if(!((*titerN).GetEnvelope()->isCollectiveType())){
		
		for(int j =0 ; j<i; j++){
		  x_bp = getLiteralFromEvents(titerN, j);
		  rhs.push_back(x_bp);
		}
		if(!rhs.empty())
		  slv.l_set_to(slv.limplies(x_ap,slv.lor(rhs)),true);
		else
		  slv.l_set_to(slv.limplies(x_ap, zero),true);
		  
		// //formula output
		formula << "(" << getLitName(x_ap) << " -> ( " ;
		if(!rhs.empty())
		  for(bvt::iterator bit = rhs.begin(); bit != rhs.end(); bit++){
		    formula << getLitName(*bit) << " | ";
		  }
		else
		  formula << getLitName(zero); 
		formula << " )) &" << std::endl;
		
		rhs.clear();
	      }
	      else { //titerN is collective type
		MatchPtr Bptr = getMatchPtrFromEvent(B);
		for(int j=0; j<i; j++){
		  x_bp = getLiteralFromMatches(Bptr, j);
		  rhs.push_back(x_bp);
		}
		if(!rhs.empty())
		  slv.l_set_to(slv.limplies(x_ap, slv.lor(rhs)),true);
		else 
		  slv.l_set_to(slv.limplies(x_ap, zero),true);
		
		// //formula output
		formula << "(" << getLitName(x_ap) << " -> ( " ;
		if(!rhs.empty())
		  for(bvt::iterator bit = rhs.begin(); bit != rhs.end(); bit++){
		    formula << getLitName(*bit) << " | ";
		  }
		else
		  formula << getLitName(zero); 
		formula << " )) &" << std::endl;
		
		rhs.clear();
	      }
	    }
	  }
	}
	else{  // titer is collective type
	  CB A(titer->GetEnvelope()->id, titer->GetEnvelope()->index);
	  MatchPtr Aptr = getMatchPtrFromEvent(A);
	  x_ap = getLiteralFromMatches(Aptr, i);
	  forall_transitions(titerN, (*iter)->_tlist){
	    if((*titerN).GetEnvelope()->func_id == FINALIZE) continue;
	    CB B(titerN->GetEnvelope()->id, titerN->GetEnvelope()->index);
	    if(last_node->isAncestor(A, B)){
	     if(!((*titerN).GetEnvelope()->isCollectiveType())){
	       for(int j =0 ; j<i; j++){
		  x_bp = getLiteralFromEvents(titerN, j);
		  rhs.push_back(x_bp);
	       }
	       if(!rhs.empty())
		 slv.l_set_to(slv.limplies(x_ap,slv.lor(rhs))  ,true);
	       else 
		 slv.l_set_to(slv.limplies(x_ap,zero)  ,true);
	       
	       // //formula output
	       	formula << "(" << getLitName(x_ap) << " -> ( " ;
	       	if(!rhs.empty())
	       	  for(bvt::iterator bit = rhs.begin(); bit != rhs.end(); bit++){
	       	    formula << getLitName(*bit) << " | ";
	       	  }
	       	else
	       	  formula << getLitName(zero); 
	       	formula << " )) &" << std::endl;
		
		rhs.clear();
	      }
	      else { //titerN is collective type
		MatchPtr Bptr = getMatchPtrFromEvent(B);
		for(int j=0; j<i; j++){
		  x_bp = getLiteralFromMatches(Bptr, j);
		  rhs.push_back(x_bp);
		}
		if(!rhs.empty())
		  slv.l_set_to(slv.limplies(x_ap, slv.lor(rhs)),true);
		else 
		  slv.l_set_to(slv.limplies(x_ap, zero),true);
		
		// //formula output
		formula << "(" << getLitName(x_ap) << " -> ( " ;
		if(!rhs.empty())
		  for(bvt::iterator bit = rhs.begin(); bit != rhs.end(); bit++){
		    formula << getLitName(*bit) << " | ";
		  }
		else
		  formula << getLitName(zero); 
		formula << " )) &" << std::endl;

		rhs.clear();
	      }
	    }
	  }
	}
      }
    }
  }
  ////////////////////////////////////////////// 
}


void Encoding2::stutteringAtPosition()
{
 literalt x_ap, x_bp; 
  bool flag = false;
  bvt rhs, rhsFinal;
  std::list<bvt> rhsPrint;
  
  ////////////////////////////////////////////////
  formula << "****stutteringAtPosition****" << std::endl; 
  for(int i = 0; i < traceSize-1; i++){
    forall_transitionLists(iter, last_node->_tlist){
      forall_transitions(titer, (*iter)->_tlist){
	if((*titer).GetEnvelope()->isCollectiveType() ||
	   (*titer).GetEnvelope()->func_id == FINALIZE) continue;
	x_ap = getLiteralFromEvents(titer, i);
	forall_matchSet(mit, matchSet){
	  forall_match(lit, (**mit)){
	    x_bp = getLiteralFromCB((*lit), i);
	    rhs.push_back(x_bp);
	    if(x_ap == x_bp) flag = true;
	  }
	  if(flag){
	    assert(!rhs.empty());
	    rhsPrint.push_back(rhs);
	    rhsFinal.push_back(slv.land(rhs));
	    flag = false;
	  }
	  rhs.clear();
	}
	if(!rhsFinal.empty()){
	  slv.l_set_to( slv.limplies(x_ap, slv.lor(rhsFinal)), true);
	  rhsFinal.clear();
	}
	
	// formula output
	if(!rhsPrint.empty()){
	  formula << "( " << getLitName(x_ap) << " -> ( ";
	  for(std::list<bvt>::iterator lbit = rhsPrint.begin(); 
	      lbit != rhsPrint.end(); lbit ++){
	    formula << "(" ;
	    for(bvt::iterator bit = (*lbit).begin(); bit!=(*lbit).end(); bit++){
	      formula << getLitName(*bit) << " & ";
	    }	   
	    formula << ") | "; 
	  }
	  formula << ")) &" << std::endl;
	  rhsPrint.clear();
	}
      }
    }
  }
}

void Encoding2::noMatchAtNextPos()
{
  int i = traceSize-2; 
  literalt x_ap;
  bvt res;
  std::list<bvt> Print;
  bool flag =false;
  //////////////////////////////////////////////
  formula << "****noMatchAtNextPos****" << std::endl; 
  forall_matchSet(mit, matchSet){
    bvt temp;
    forall_match(lit, (**mit)){
      if(last_node->GetTransition(*lit)->GetEnvelope()->isCollectiveType()){
	flag = true;
	break;
      }
      else{
	x_ap = getLiteralFromCB((*lit), i);
	res.push_back(slv.lnot(x_ap));
	temp.push_back(x_ap);
      }
    }
    if (flag){
      bvt t;
      x_ap = getLiteralFromMatches(*mit, i);
      t.push_back(x_ap);
      slv.l_set_to(slv.lnot(x_ap), true);
      Print.push_back(t);
      flag = false;
    }
    else{
      assert(!res.empty());
      slv.l_set_to(slv.lor(res), true); 
      Print.push_back(temp);
      res.clear();
      temp.clear();
    }
  }
  
  // formula output 
  for(std::list<bvt>::iterator lbit = Print.begin(); 
      lbit != Print.end(); lbit ++){
    formula << "(" ;
    for(bvt::iterator bit = (*lbit).begin(); bit!=(*lbit).end(); bit++){
      formula << "!" << getLitName(*bit) << " | ";
    }	   
    formula << ") & "; 
  }
  ////////////////////////////////////////////// 

}

void Encoding2::extensionNextPos()
{
  int i = traceSize-2;
  bvt rhs, rhsFinal, lhs; 
  bvt  rhsBPrint; 
  std::list <bvt> rhsAPrint;
  literalt x_ap, x_apdash, x_bp, x_bpdash;
  bool flag = false;
  ////////////////////////////////////////////// 
  formula << "****extensionNextPos****" << std::endl; 
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)) {    
      x_ap = getLiteralFromCB((*lit), i);
      if(!(last_node->GetTransition(*lit)->GetEnvelope()->isCollectiveType())){
	lhs.push_back(x_ap);
	for(int j=0; j < i; j++){
	  x_apdash = getLiteralFromCB((*lit), j);
	  rhsBPrint.push_back(x_apdash);
	  rhsFinal.push_back(slv.lnot(x_apdash));
	}
	if(rhsFinal.empty()){
	  rhsFinal.push_back(one);
	  rhsBPrint.push_back(one);
	  }
      }
      else {// i.e event is part of collective match
	flag = true;
	break;
      }
    }
    if(!flag){
      assert(!lhs.empty());
      assert(!rhsFinal.empty());
      forall_match(lit, (**mit)){
	forall_transitionLists(iter, last_node->_tlist){
	  forall_transitions(titer, (*iter)->_tlist){
	    Envelope *envB = (*titer).GetEnvelope();
	    if(envB->func_id == FINALIZE) continue;
	    CB B (envB->id, envB->index);
	    if(last_node->isAncestor((*lit),B)){
	      bvt temp;
	      if(!((*titer).GetEnvelope()->isCollectiveType())){
		for (int j=0; j<i; j++){
		  x_bpdash = getLiteralFromEvents(titer, j);
		  temp.push_back(x_bpdash);
		} 
		if(!temp.empty()){
		  rhs.push_back(slv.lor(temp));
		  rhsAPrint.push_back(temp);
		}
		else {
		  rhs.push_back(zero);
		  temp.push_back(zero);
		  rhsAPrint.push_back(temp);
		}
	      }
	      else{
		MatchPtr Bptr = getMatchPtrFromEvent(B);
		for (int j=0; j<i; j++){
		  x_bpdash = getLiteralFromMatches(Bptr, j);
		  temp.push_back(x_bpdash);
		}
		if(!temp.empty()){
		  rhs.push_back(slv.lor(temp));
		  rhsAPrint.push_back(temp);
		  temp.clear();
		}
		else{
		  rhs.push_back(zero);
		  temp.push_back(zero);
		  rhsAPrint.push_back(temp);
		  temp.clear();
		}
	      }
	    }
	    if(rhs.empty()){
	      rhs.push_back(one);
	      rhsAPrint.push_back(rhs);
	    }
	    rhsFinal.push_back(slv.land(rhs));
	    rhs.clear();
	  }
	}
      }
      if(!lhs.empty() && !rhsFinal.empty()){
	slv.l_set_to(slv.land(slv.limplies(slv.land(lhs), slv.land(rhsFinal)), 
			      slv.limplies(slv.land(rhsFinal), slv.land(lhs))), true);
	//formula output
	formula << "( (" ;
	for(bvt::iterator bit = lhs.begin(); bit != lhs.end(); bit++){
	  formula << getLitName(*bit) << " & ";
	}
	formula << ") <-> ("; 
	for(bvt::iterator bit = rhsBPrint.begin(); bit != rhsBPrint.end(); bit++){
	  formula << "!" << getLitName(*bit) << " & ";
	}
	formula << ") & (";
	for(std::list<bvt>::iterator lbit = rhsAPrint.begin(); lbit != rhsAPrint.end(); 
	    lbit++){
	  formula << "(";
	  for(bvt::iterator bit = (*lbit).begin(); bit != (*lbit).end(); bit++){
	    formula << getLitName(*bit) << " | ";  
	  }
	  formula << ") & ";
	}
	formula << ")) & " <<std::endl;
	rhsAPrint.clear(); rhsBPrint.clear();
	lhs.clear();
	rhsFinal.clear();
      }
    }
    else{ // 
      assert(lhs.empty());
      x_ap = getLiteralFromMatches(*mit, i);
      forall_match(lit, (**mit)) {
	forall_transitionLists(iter, last_node->_tlist){
	  forall_transitions(titer, (*iter)->_tlist){
	    Envelope *envB = (*titer).GetEnvelope();
	    if(envB->func_id == FINALIZE) continue;
	    CB B (envB->id, envB->index);
	    if(last_node->isAncestor((*lit), B)){
	      bvt temp;  
	      if(last_node->GetTransition(B)->GetEnvelope()->isCollectiveType()){
		MatchPtr Bptr = getMatchPtrFromEvent(B);
		for(int j=0;j<i;j++){
		  x_bp = getLiteralFromMatches(Bptr, j);
		  temp.push_back(x_bp);
		}
		if(!temp.empty()){
		  rhs.push_back(slv.lor(temp));
		  rhsAPrint.push_back(temp);
		  temp.clear();
		}
		else{
		  rhs.push_back(zero);
		  temp.push_back(zero);
		  rhsAPrint.push_back(temp);
		  temp.clear();
		}
	      }
	      else{
		for(int j=0;j<i;j++){
		  x_bp = getLiteralFromCB(B, j);
		  temp.push_back(x_bp);
		}
		if(!temp.empty()){
		  rhs.push_back(slv.lor(temp));
		  rhsAPrint.push_back(temp);
		  temp.clear();
		}
		else{
		  rhs.push_back(zero);
		  temp.push_back(zero);
		  rhsAPrint.push_back(temp);
		  temp.clear();
		}
	      }
	    }
	    if(rhs.empty()){
	      rhs.push_back(one);
	      rhsAPrint.push_back(rhs);
	    }
	    rhsFinal.push_back(slv.land(rhs));
	    rhs.clear();
	  }
	}
      }
      
      for(int j=0; j<i; j++){
	x_bp = getLiteralFromMatches(*mit,j);
	rhsFinal.push_back(slv.lnot(x_bp));
	rhsBPrint.push_back(x_bp);
      }
      
      if(!rhsFinal.empty()){
	slv.l_set_to(slv.land(slv.limplies(x_ap, slv.land(rhsFinal)), 
			      slv.limplies(slv.land(rhsFinal), x_ap)), true);
	rhsFinal.clear();
	
	//formula output
	formula << "( " ;
	formula << getLitName(x_ap) << " <-> ("; 
	for(bvt::iterator bit = rhsBPrint.begin(); bit != rhsBPrint.end(); bit++){
	  formula << "!" << getLitName(*bit) << " & ";
	}
	formula << ") & (";
	for(std::list<bvt>::iterator lbit = rhsAPrint.begin(); lbit != rhsAPrint.end(); 
	    lbit++){
	  formula << "(";
	  for(bvt::iterator bit = (*lbit).begin(); bit != (*lbit).end(); bit++){
	    formula << getLitName(*bit) << " | ";  
	  }
	  formula << ") & ";
	}
	formula << ")) & " <<std::endl;
	rhsAPrint.clear(); rhsBPrint.clear();
      }
      flag = false;
    }
  }
  ///////////////////////////////////////////////////////////////////////

}



void Encoding2::publish()
{
  tvt result;
  literalt x_ap;
  bool flag = false;
  
  for(int i = 0; i < traceSize -1; i++){
    forall_transitionLists(iter, last_node->_tlist){
      forall_transitions(titer, (*iter)->_tlist){
	if((*titer).GetEnvelope()->func_id == FINALIZE) continue;
	if(!((*titer).GetEnvelope()->isCollectiveType())){
	  x_ap = getLiteralFromEvents(titer, i);
	  switch(slv.l_get(x_ap).get_value()){ 
	  case tvt::TV_TRUE:
	    formula << getLitName(x_ap) << ":1" << std::endl;
	    break;
	  case tvt::TV_FALSE:
	    formula << getLitName(x_ap) << ":0" << std::endl;
	    break;
	  case tvt::TV_UNKNOWN:
	    formula << getLitName(x_ap) << ":UNKNOWN" << std::endl;
	    break;
	  default: assert(false);
	  }
	}
      }
    }
    forall_matchSet(mit, matchSet){
      forall_match(lit, (**mit)){
	if(last_node->GetTransition(*lit)->GetEnvelope()->isCollectiveType()){
	  flag = true;
	  break;
	}	
      }
      if(flag){
	x_ap = getLiteralFromMatches(*mit, i);
	switch(slv.l_get(x_ap).get_value()){ 
	case tvt::TV_TRUE:
	  formula << getLitName(x_ap) << ":1" << std::endl;
	  break;
	case tvt::TV_FALSE:
	  formula << getLitName(x_ap) << ":0" << std::endl;
	  break;
	case tvt::TV_UNKNOWN:
	  formula << getLitName(x_ap) << ":UNKNOWN" << std::endl;
	  break;
	default: assert(false);
	}
	flag = false;
      }
    }
  }
}


void Encoding2::Encoding_Mixed()
{
  createMatchSet();
  //  printMatchSet();
  createMatchLiterals();
  createEventLiterals();

  gettimeofday(&constGenStart, NULL);
  stutteringAtPosition();  
  uniqueAtPosition();
  noRepetition();
  partialOrder();
  extensionNextPos();
  noMatchAtNextPos();
  gettimeofday(&constGenEnd, NULL);
  
  // std::cout << formula.str();
  // std::cout << std::endl;
  
  std::cout << "********* SAT VALUATIONS ************" << std::endl;

  formula.str("");
  formula.clear();

  gettimeofday(&solverStart, NULL);  
  satcheckt::resultt answer = slv.prop_solve();
  gettimeofday(&solverEnd, NULL);  

  formula << "Number of Clauses: " << slv.no_clauses() << std::endl;
  formula << "Number of Variables: " << slv.no_variables() << std::endl;
  formula << "Constraint Generation Time: "
	  << (getTimeElapsed(constGenStart, constGenEnd)*1.0)/1000000 << "sec \n";
  formula << "Solving Time: " << (getTimeElapsed(solverStart, solverEnd)*1.0)/1000000 << "sec \n";

  switch(answer){
  case satcheckt::P_UNSATISFIABLE:
    std::cout << "Formula is UNSAT" <<std::endl;
    break;
  case satcheckt::P_SATISFIABLE:
    std::cout << "Formula is SAT -- DEADLOCK DETECTED" <<std::endl;
    publish();
    break;
    // output the valuations
  default: 
    std::cout << "ERROR in SAT SOLVING" <<std::endl;
    break;
  }
 
  std::cout << formula.str();
  std::cout << std::endl;
 
}
////////////////////////////////////////////////////////////
/////                                                ///////
////        ENCODING PO                              ///////
////////////////////////////////////////////////////////////
void poEncoding::set_width()
{
  width = address_bits();
  
}

unsigned poEncoding::get_width(){
    return width;
}

unsigned poEncoding::address_bits()
{
  assert(eventSize == 0);
  forall_transitionLists(iter, last_node->_tlist){
    eventSize += (*iter)->_tlist.size();
  }
  unsigned res, x=2;
  for(res=1; x<eventSize; res+=1, x*=2);
  return res;
}


void poEncoding::createPossibleMatches()
{
  
  // for non-SR matches
  // ie. 1) only collectives 2) waits 3) Finalizes
  for(int i =0 ; i < _it->_slist.size()-1; i++){
    CB front = _it->_slist[i]->curr_match_set.front();
    Transition *t = _it->_slist[i]->GetTransition(front);
    Envelope *env = t->GetEnvelope();
    // check whether match is a non send-recv one
    if(!(env->isSendType())){
      matchSet.push_back(&(_it->_slist[i]->curr_match_set));
    }
  }
  //for SR matches
  _MIterator mit, mitend;
  mitend = _m->_MSet.end();
  for (mit = _m->_MSet.begin(); mit != mitend; mit++){
    assert(!(*mit).second.empty());
    matchSet.push_back(&((*mit).second));
  }
}



// Match may be S-R, Collective, or Wait
void poEncoding::createMatchLiterals()
{
  std::stringstream uniquepair;
  std::string matchNumeral;
  
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
	uniquepair<<(*lit)._pid;
	uniquepair<<(*lit)._index;
    }
    matchNumeral = uniquepair.str();
    if(matchNumeral.size()){
      literalt X_m = slv.new_variable();
    //insert in to the map
      matchMap.insert(std::pair<std::string, literalt> (matchNumeral, X_m));
      revMatchMap.insert(std::pair<literalt, std::string> (X_m, matchNumeral));
      match2symMap.insert(std::pair<MatchPtr, std::string> (*mit, matchNumeral));
      
      // clear out uniquepair
      uniquepair.str("");
      uniquepair.clear();
    }
  }
}

literalt poEncoding::getMatchLiteral(MatchPtr mptr)
{
  std::string symbol = match2symMap.find(mptr)->second;
  assert(!symbol.empty());
  return matchMap.find(symbol)->second;
}


void poEncoding::createFinalizeWaitLiterals()
{
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *env = (*titer).GetEnvelope();
      CB f(env->id, env->index);
      if((env->func_id == FINALIZE) ||
	 env->isWaitorTestType()){
	literalt X_f = slv.new_variable();
	eventMap.insert(std::pair<CB, literalt> (f, X_f));
	revEventMap.insert(std::pair<literalt, CB>(X_f, f));
      }
    }
  }
}

literalt poEncoding::getFinalizeWaitLiterals(CB f)
{
  std::map<CB, literalt>::iterator iter;
  iter = eventMap.find(f);
  if(iter != eventMap.end())
    return (*iter).second;
  assert(false); // should never reach here
}

void poEncoding::createBVLiterals()
{
 forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *env = (*titer).GetEnvelope();
      if(env->isCollectiveType()) continue;
      CB A (env->id, env->index); 
      bvt Abv; 
      Abv.resize(width);
      for(unsigned i=0; i < width; i++){
	Abv[i] = slv.new_variable();
      }
      bvEventMap.insert(std::pair<CB, bvt >  (A,Abv));
      revBVEventMap.insert(std::pair<bvt, CB>(Abv, A));
    }
  }
  bool flag = false;
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
      Envelope *env = last_node->GetTransition(*lit)->GetEnvelope();
      // only collective w/o finalizes
      if(env->isCollectiveType()){
	flag = true; 
	break;
      }
    }
    if(flag){
      bvt Abv; 
      Abv.resize(width);
      for(unsigned i=0; i < width; i++){
	Abv[i] = slv.new_variable();
      }
      collBVMap.insert(std::pair<MatchPtr, bvt > ((*mit),Abv));
      revCollBVMap.insert(std::pair<bvt, MatchPtr>(Abv, (*mit)));
      flag = false;
    }
  }
}

bvt poEncoding::getBVLiterals(CB A) 
{
  Envelope *envA = last_node->GetTransition(A)->GetEnvelope(); 

  if(!(envA->isCollectiveType())){
    std::map<CB, bvt>::iterator bv_it;
    bv_it = bvEventMap.find(A);
    assert(bv_it != bvEventMap.end());
    return bv_it->second;
  }
  else{
    MatchPtr  Aptr = getMPtr(A);
    std::map<MatchPtr, bvt>::iterator bv_it;
    bv_it = collBVMap.find(Aptr);
    assert(bv_it != collBVMap.end());
    return bv_it->second;
  }
}

MatchPtr poEncoding::getMPtr(CB A) 
{
  bool flag = false;
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
      if((*lit) == A) {
	flag = true;
	break;
      }
    }
    if(flag){
      return (*mit);
    }
  }
  return NULL;
}


void poEncoding::dlock()
{
  bvt lst;
  formula << "****dlock****" << std::endl; 
  formula << "(";
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *env = (*titer).GetEnvelope();
      CB A (env->id, env->index); 
      if(env->func_id == FINALIZE){
	literalt X_f = getFinalizeWaitLiterals(A);
	lst.push_back(slv.lnot(X_f));
	//slv.l_set_to(slv.lnot(X_f), true);
	formula << "!" << getLitName(X_f,1) << " | "; 
      }
    }
  }
  slv.l_set_to(slv.lor(lst), true);
  formula << ")" << std::endl;
}

void poEncoding::m2Clk()
{
  CB s, r;
    
  formula << "****m2Clk****" << std::endl; 
 
  forall_matchSet(mit, matchSet){
    s = (**mit).front();
    Envelope *env = last_node->GetTransition(s)->GetEnvelope();
    if(env->isSendType()){
      r = (**mit).back();
      literalt X_m = getMatchLiteral(*mit);
      bvt Sbv = getBVLiterals(s);
      bvt Rbv = getBVLiterals(r);
      literalt e = bvUtils.equal(Sbv, Rbv);  // [svs]: clk_s = clk_r
      slv.l_set_to(slv.land(slv.limplies(X_m, e), 
			   slv.limplies(e, X_m)), true);
    }
  }
}

void poEncoding::processPO()
{
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope * envA = (*titer).GetEnvelope();
      CB A(envA->id, envA->index);
      for(std::vector<int>::iterator vit = (*titer).get_ancestors().begin();
      	  vit != (*titer).get_ancestors().end(); vit ++){
      	CB B (envA->id, *vit);
      	Envelope * envB = last_node->GetTransition(B)->GetEnvelope();
	// forall_transitions(titerN, (*iter)->_tlist){
	// 	Envelope * envB = (*titerN).GetEnvelope();
	// 	CB B (envB->id, envB->index);
	// 	if(last_node->isAncestor(A,B)){
	bvt Abv, Bbv;
	
	Abv = getBVLiterals(A);
	Bbv = getBVLiterals(B);
	
	literalt c_ba = bvUtils.unsigned_less_than(Bbv, Abv);
	slv.l_set_to(c_ba, true); // PPO constraint
      }
    }
  }
}

void poEncoding:: init()
{
  formula << "****init****" << std::endl; 
  bool AhasanAncestor = false;
  formula << "(";
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      CB A(envA->id, envA->index);
      forall_transitions(titerN, (*iter)->_tlist){
	Envelope *envB = titerN->GetEnvelope();
	CB B(envB->id, envB->index);
	if(last_node->isAncestor(A,B)) {
	  AhasanAncestor = true; 
	  break;
	}
      }
      if(AhasanAncestor){
	AhasanAncestor = false;
	continue;
      }
      else{ // A is the first operation
	
	// Finalize events 
	if(envA->func_id == FINALIZE){
	  literalt X_f = getFinalizeWaitLiterals(A);
	  formula << getLitName(X_f, 1) << " & ";
	  slv.l_set_to(X_f, true);
	}
	if( envA->isRecvType()){//(envA->isSendType() || envA->isRecvType()){
	  bvt lst;
	  forall_matchSet(mit, matchSet){
	    CB Mf = (**mit).front();
	    CB Mb = (**mit).back();
	    if((A == Mf) || (A == Mb)){
	      literalt X_m = getMatchLiteral(*mit);
	 
	      lst.push_back(X_m);
	    }
	  }
	  if(!lst.empty()){
	    formula << "(";
	    for(bvt::iterator bit = lst.begin(); 
		bit != lst.end(); bit++){
	      formula << getLitName((*bit), 0) << " | "; 
	    }
	    formula << ") & ";
	    slv.l_set_to(slv.lor(lst), true);
	  }
	}
	if(envA->isCollectiveType()){ 
	  MatchPtr mptr = getMPtr(A);
	  literalt X_l = getMatchLiteral(mptr);
	  formula << getLitName(X_l, 0) << " & ";
	  slv.l_set_to(X_l, true);
	}
	// waits can have no predecessors under infinite
	// buffering model
	if(envA->isWaitorTestType()){
	  literalt X_w = getFinalizeWaitLiterals(A);
	  formula << getLitName(X_w, 1) << " & ";
	  slv.l_set_to(X_w, true);
	}
      }
    }
  }
  formula << ") & " << std::endl;
}

literalt poEncoding::exclusive(CB q, MatchPtr m)
{
  bvt lst;
  formula << " & (";
  forall_matchSet(mit, matchSet){  
    CB front = (**mit).front();
    CB back = (**mit).back();
    if((q == front) || (q == back)){
      if((*mit) != m){
	literalt X_l = getMatchLiteral(*mit);
	lst.push_back(slv.lnot(X_l));
	formula << "!" <<getLitName(X_l, 0) << " & "; 
      }
    }
  }
  if(!lst.empty()){
    formula << ")"; 
    return slv.land(lst);
  }
  formula << "one)";
  return one;
  //assert(false);
}

literalt poEncoding::predsMatched(CB q)
{
  bvt lst;
  formula << "(";
  // forall_transitionLists(iter, last_node->_tlist){
  //   forall_transitions(titer, (*iter)->_tlist){
  Transition *qT = last_node->GetTransition(q);
  for(std::vector<int>::iterator vit = qT->get_ancestors().begin();
      vit != qT->get_ancestors().end(); vit ++){
    
    CB p(q._pid, (*vit));
    Envelope *envP  = last_node->GetTransition(p)->GetEnvelope();
    // P is send/recv
    if(envP->isSendType() || envP->isRecvType()){
      bvt tmp;
      forall_matchSet(mit, matchSet){
	CB Mf = (**mit).front();
	CB Mb = (**mit).back();
	if((p == Mf) || (p == Mb)){
	  literalt X_m = getMatchLiteral(*mit);
	  tmp.push_back(X_m);
	}
      }
      if(!tmp.empty()){
	formula << "(";
	for(bvt::iterator bit = tmp.begin(); 
	    bit != tmp.end(); bit++){
	  formula << getLitName((*bit), 0) << " | "; 
	}
	formula << ") & ";
	lst.push_back(slv.lor(tmp));
      }
    }
    if(envP->isCollectiveType()){
      MatchPtr m = getMPtr(p);
      literalt X_l = getMatchLiteral(m);
      formula << getLitName(X_l, 0) << " & "; 
      lst.push_back(X_l);
    }
    if(envP->isWaitorTestType()){
      literalt X_w = getFinalizeWaitLiterals(p);
      formula << getLitName(X_w, 1) << " & "; 
      lst.push_back(X_w);
    }
  }
  if(!lst.empty()){
    formula << ")"; 
    return slv.land(lst);
  }
  formula << "one)"; 
  return one;
  //assert(false);
}


void poEncoding:: ext()
{
  formula << "****ext****" << std::endl; 
  forall_matchSet(mit, matchSet){
    CB front = (**mit).front();
    Envelope *envA = last_node->GetTransition(front)->GetEnvelope();
    if(envA->isSendType()){
      literalt X_m = getMatchLiteral(*mit);
      formula << "(" << getLitName(X_m,0) << " <-> (";
      bvt lst;
      forall_match(lit, (**mit)){
	literalt pred = predsMatched(*lit);
	formula << " & ";
	literalt excl = exclusive(*lit, *mit);
	formula << " & ";
	lst.push_back(pred); 
	lst.push_back(excl); 
      }
      if(!lst.empty()){
	formula << ")) & " <<std::endl;
	slv.l_set_to(slv.land(slv.limplies(X_m, slv.land(lst)), 
			      slv.limplies(slv.land(lst), X_m)), true);
      }
      else
	slv.l_set_to(slv.land(slv.limplies(X_m, one), 
			      slv.limplies(one, X_m)), true);
    }
    if(envA->isCollectiveType()){
      literalt X_n = getMatchLiteral(*mit);
      bvt lst;
      formula << "(" << getLitName(X_n,0) << " <-> (";
      forall_match(lit, (**mit)){
	literalt pred = predsMatched(*lit);
	formula << ")) & " <<std::endl;
	lst.push_back(pred);
      }
      if(!lst.empty()){
	slv.l_set_to(slv.land(slv.limplies(X_n, slv.land(lst)), 
			      slv.limplies(slv.land(lst), X_n)), true);
      }
      else
	slv.l_set_to(slv.land(slv.limplies(X_n, one), 
			      slv.limplies(one, X_n)), true);
    }
    if((envA->func_id ==FINALIZE) || 
       envA->isWaitorTestType()){
      bvt lst;
      forall_match(lit, (**mit)){
	literalt X_f = getFinalizeWaitLiterals(*lit);
	formula << "(" << getLitName(X_f,1) << " <-> (";
	literalt pred = predsMatched(*lit);
	formula << ")) & " <<std::endl;
	slv.l_set_to(slv.land(slv.limplies(X_f, pred), 
			      slv.limplies(pred, X_f)), true);
      }
    }
  }
}

std::string poEncoding::getLitName(literalt lt, int type)
{
  
  std::stringstream ss;
  switch(type){
  case 0:{
    ss << "X_" << revMatchMap.find(lt)->second;
    return ss.str();
  }
  case 1: {
    CB c = revEventMap.find(lt)->second;
    ss << "X_" << c._pid << c._index; 
    return ss.str();
  }
  default:
    assert(false);
  }
}



void poEncoding::publish()
{
  tvt result;
  bvt lst0, lst1;
  bool flag = false;

  forall_matchSet(mit, matchSet){
    CB front = (**mit).front();
    Envelope * ef = last_node->GetTransition(front)->GetEnvelope();
    if(ef->isCollectiveType() || ef->isSendType() || 
       ef->isRecvType()){
      literalt X_m = getMatchLiteral(*mit);
      lst0.push_back(X_m);
    }
    if((ef->func_id == FINALIZE) ||
       ef->isWaitorTestType()){
      forall_match(lit, (**mit)){
	literalt X_m = getFinalizeWaitLiterals(*lit);
	lst1.push_back(X_m);
      }
    }
    for(bvt::iterator bit = lst0.begin();
	bit != lst0.end(); bit++){
      switch(slv.l_get(*bit).get_value()){
      case tvt::TV_TRUE:
	formula << getLitName((*bit), 0) << ":1" << std::endl;
	break;
      case tvt::TV_FALSE:
	formula << getLitName((*bit), 0) << ":0" << std::endl;
	break;
      case tvt::TV_UNKNOWN:
	formula << getLitName((*bit), 0) << ":UNKNOWN" << std::endl;
      }
    }

    for(bvt::iterator bit = lst1.begin();
	bit != lst1.end(); bit++){
      switch(slv.l_get(*bit).get_value()){
      case tvt::TV_TRUE:
	formula << getLitName((*bit), 1) << ":1" << std::endl;
	break;
      case tvt::TV_FALSE:
	formula << getLitName((*bit), 1) << ":0" << std::endl;
	break;
      case tvt::TV_UNKNOWN:
	formula << getLitName((*bit), 1) << ":UNKNOWN" << std::endl;
      }
    }
    lst0.clear();
    lst1.clear();
  }
}

void poEncoding::poEnc()
{
  createPossibleMatches();
  set_width();
  createMatchLiterals();
  createFinalizeWaitLiterals();
  createBVLiterals();

  gettimeofday(&constGenStart, NULL);
  init();
  ext();
  m2Clk();
  processPO();
  dlock();
  gettimeofday(&constGenEnd, NULL);
  
  formula.str("");
  formula.clear();

  getTimeElapsed(constGenStart, constGenEnd);
  std::cout << "********* SAT VALUATIONS ************" << std::endl;
  std::cout << "Number of Clauses: " << slv.no_clauses() << std::endl;
  std::cout << "Number of Variables: " << slv.no_variables() << std::endl;
  std::cout << "Constraint Generation Time: "
	    << (getTimeElapsed(constGenStart, constGenEnd)*1.0)/1000000 << "sec \n";

  
  gettimeofday(&solverStart, NULL);
  satcheckt::resultt answer = slv.prop_solve();
  gettimeofday(&solverEnd, NULL);
  
  switch(answer){
  case satcheckt::P_UNSATISFIABLE:
    formula << "Formula is UNSAT" <<std::endl;
    break;
  case satcheckt::P_SATISFIABLE:
    formula  << "Formula is SAT -- DEADLOCK DETECTED" <<std::endl;
    _deadlock_found = true;
    publish();
    break;
    // output the valuations
  default: 
    formula << "ERROR in SAT SOLVING" <<std::endl;
    break;
  }
  //std::cout << slv.constraintStream.str();
  
  std::cout << "Solving Time: " << (getTimeElapsed(solverStart, solverEnd)*1.0)/1000000 << "sec \n";
  size_t peakSize = getPeakRSS();
  std::cout << "Mem (MB): " << peakSize/(1024.0*1024.0) << std::endl;
  std::cout << formula.str();
  std::cout << std::endl;
}
////////////////////////////////////////////////////////////
/////                                                ///////
////        ENCODING 3                               ///////
////////////////////////////////////////////////////////////

void Encoding3::set_width()
{
  width = address_bits();
  
}

unsigned Encoding3::get_width(){
    return width;
}

unsigned Encoding3::address_bits()
{
  unsigned res, x=2;
  for(res=1; x<eventSize; res+=1, x*=2);
  return res;
}


void Encoding3::createEventLiterals ()
{
  
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      if((*titer).GetEnvelope()->func_id == FINALIZE) continue;
      if((*titer).GetEnvelope()->isCollectiveType()) continue;
      literalt m_e = slv.new_variable();
      //slv.set_frozen(m_e);
      literalt i_e = slv.new_variable();
      Envelope *env = (*titer).GetEnvelope();
      CB A (env->id, env->index); 
      // slv.constraintStream << A << " m_e = " << m_e.get()  
      // 			   << ",i_e = " << i_e.get() << std::endl;
      //insert in to the map
      eventMap.insert(std::pair<CB, std::pair<literalt, literalt> > 
		      (A,std::pair<literalt, literalt> (m_e, i_e)));
      revEventMap.insert(std::pair<literalt, CB>(m_e, A));
      eventSize++;
    }
  }
  bool flag = false;
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
      if(last_node->GetTransition(*lit)->GetEnvelope()->isCollectiveType()){
	flag = true; 
	break;
      }
    }
    if(flag){
      literalt m_c = slv.new_variable();
      literalt i_c = slv.new_variable();
      collEventMap.insert(std::pair<MatchPtr, std::pair<literalt, literalt> > 
			  ((*mit),std::pair<literalt, literalt> (m_c, i_c)));
      revCollMap.insert(std::pair<literalt, MatchPtr>(m_c, (*mit)));
      flag = false;
      eventSize++;
    }
  }
}


void Encoding3::printEventMap()
{
  formula << "**** EventMap*****" << std::endl; 
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *env = (*titer).GetEnvelope();
      if(env->func_id == FINALIZE) continue;
      CB A (env->id, env->index);
      literalt m = eventMap.find(A)->second.first;
      literalt i = eventMap.find(A)->second.second;
      formula << A << " " << m.get() << "," << i.get() << std::endl;
      formula << "\t *** RevEventMap *** " << std::endl;
      formula << "\t" << m.get() << "--" << revEventMap.find(m)->second <<std::endl;
    }
  }
}

void Encoding3::createMatchLiterals()
{
  std::stringstream uniquepair;
  std::string matchNumeral;
  
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
      // match literals only for send and receive
      if(last_node->GetTransition(*lit)->GetEnvelope()->isSendType() ||
	 last_node->GetTransition(*lit)->GetEnvelope()->isRecvType()){
	uniquepair<<(*lit)._pid;
	uniquepair<<(*lit)._index;
      }
    }
    matchNumeral = uniquepair.str();
    if(matchNumeral.size()){
      literalt s_m = slv.new_variable();
      slv.constraintStream << matchNumeral << " s_m = " << s_m.get() 
			       << std::endl;
	  
    //insert in to the map
      matchMap.insert(std::pair<std::string, literalt> (matchNumeral, s_m));
      revMatchMap.insert(std::pair<literalt, std::string> (s_m, matchNumeral));
      match2symMap.insert(std::pair<MatchPtr, std::string> (*mit, matchNumeral));
      
      // clear out uniquepair
      uniquepair.str("");
      uniquepair.clear();
    }
  }
}

literalt Encoding3::getClkLiteral(CB A, CB B)
{
  Envelope *envA , *envB;
  envA = last_node->GetTransition(A)->GetEnvelope();
  envB = last_node->GetTransition(B)->GetEnvelope();
  
  bvt Abv, Bbv;
  Abv = getEventBV(A);
  Bbv = getEventBV(B);
  
  if(!envA->isCollectiveType() && !envB->isCollectiveType()){
    std::map<std::pair<CB, CB>, literalt >::iterator res;
    res = clkMap.find(std::pair<CB, CB> (A,B));
    if(res != clkMap.end())
      return res->second;
    else {
      literalt c_ab = bvUtils.unsigned_less_than(Abv, Bbv);
      insertClockEntriesInMap(A, B, c_ab);
      return c_ab;
    }
  }
  else if (envA->isCollectiveType() && !envB->isCollectiveType()){
    std::map<std::pair<MatchPtr, CB>, literalt >::iterator res;
    MatchPtr Aptr = getMPtr(A);
    assert (Aptr != NULL);
    res = clkMapCollEvent.find(std::pair<MatchPtr, CB> (Aptr,B));
    if(res != clkMapCollEvent.end())
      return res->second;
    else{
      literalt c_ab = bvUtils.unsigned_less_than(Abv, Bbv);
      insertClockEntriesInMap(A, B, c_ab);
      return c_ab;
    }
  }
  else if(!envA->isCollectiveType() && envB->isCollectiveType()){
    std::map<std::pair<CB, MatchPtr>, literalt >::iterator res;
    MatchPtr Bptr = getMPtr(B);
    assert (Bptr != NULL);
    res = clkMapEventColl.find(std::pair<CB, MatchPtr> (A,Bptr));
    if(res != clkMapEventColl.end())
      return res->second;
    else{
      literalt c_ab = bvUtils.unsigned_less_than(Abv, Bbv);
      insertClockEntriesInMap(A, B, c_ab);
      return c_ab;
    }
  }
  else{
    std::map<std::pair<MatchPtr, MatchPtr>, literalt >::iterator res;
    MatchPtr Aptr = getMPtr (A);
    MatchPtr Bptr = getMPtr(B);
    assert (Aptr != NULL);
    assert (Bptr != NULL);
    res = clkMapCollColl.find(std::pair<MatchPtr, MatchPtr> (Aptr,Bptr));
    if(res != clkMapCollColl.end())
      return res->second;
    else{
      literalt c_ab = bvUtils.unsigned_less_than(Abv, Bbv);
      insertClockEntriesInMap(A, B, c_ab);
      return c_ab;
    }
  }
}

std::pair<literalt,literalt> Encoding3::getMILiteral(CB A)
{
  Envelope *envA = last_node->GetTransition(A)->GetEnvelope();
  if(!envA->isCollectiveType())
    return eventMap.find(A)->second;
  else {
    MatchPtr Aptr = getMPtr(A);
    assert (Aptr != NULL);
    return collEventMap.find(Aptr)->second;
  }
}

literalt Encoding3::getMatchLiteral(MatchPtr mptr)
{
  std::string symbol = match2symMap.find(mptr)->second;
  return matchMap.find(symbol)->second;
}

MatchPtr Encoding3::getMPtr(CB A) 
{
  bool flag = false;
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
      if((*lit) == A) {
	flag = true;
	break;
      }
    }
    if(flag){
      return (*mit);
    }
  }
  return NULL;
}

std::string Encoding3::getClkLitName(literalt lt, CB A, CB B)
{
  Envelope *envA, *envB;
  envA = last_node->GetTransition(A)->GetEnvelope();
  envB = last_node->GetTransition(B)->GetEnvelope();
  
  std::stringstream ss;
  
  if (!envA->isCollectiveType() && !envB->isCollectiveType()){
    std::pair <CB, CB> p = revClkMap.find(lt)->second;
    ss << "C_" << p.first._pid << p.first._index << "_" 
       << p.second._pid << p.second._index;
    return ss.str();
  }
  else if(envA->isCollectiveType() && !envB->isCollectiveType()){
    std::pair<MatchPtr, CB>  p = revClkMapCollEvent.find(lt)->second;
    ss << "C_";
    forall_match(lit, (*(p.first))){
      ss <<  (*lit)._pid << (*lit)._index;
    }
    ss<< "_" << p.second._pid << p.second._index;
    return ss.str();
  }
  else if(!envA->isCollectiveType() && envB->isCollectiveType()){
   std::pair<CB, MatchPtr>  p = revClkMapEventColl.find(lt)->second;
    ss << "C_" << p.first._pid << p.first._index << "_";
    forall_match(lit, (*(p.second))){
      ss << (*lit)._pid << (*lit)._index;
    }
    return ss.str();
  }
  else{
    std::pair<MatchPtr, MatchPtr> p = revClkMapCollColl.find(lt)->second;
    ss << "C_";
    forall_match(lit, (*(p.first))){
      ss << (*lit)._pid << (*lit)._index;
    }
    ss << "_";
    forall_match(lit, (*(p.second))){
      ss << (*lit)._pid << (*lit)._index;
    }
    return ss.str();
  }
}

std::string Encoding3::getLitName(literalt lt, int type)
{
  
  std::stringstream ss;
  switch(type){
  case 0:{
    ss << "S_" << revMatchMap.find(lt)->second;
    return ss.str();
  }
    
  case 1:{
    CB A = revEventMap.find(lt)->second;
    ss << "M_" << A._pid << A._index;
    return ss.str();  
  }
    
  case 2: {
    MatchPtr Aptr = revCollMap.find(lt)->second;
    ss << "M_";
    forall_match(lit, (*Aptr)){
      ss << (*lit)._pid  << (*lit)._index;
    }
    return ss.str();
    
  }
  case 3: {
    CB A = revEventMap.find(lt)->second;
    ss << "I_" << A._pid  << A._index;
    return ss.str();
  }
  case 4: {
    MatchPtr Aptr = revCollMap.find(lt)->second;
    ss << "I_";
    forall_match(lit, (*Aptr)){
      ss << (*lit)._pid <<(*lit)._index;
    }
    return ss.str();
  }
  default:
    assert(false);
    
  }
}

/*
Constraints 


 */
void Encoding3::createBVEventLiterals()
{
  ///////////////////////////////

 forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      if((*titer).GetEnvelope()->func_id == FINALIZE) continue;
      if((*titer).GetEnvelope()->isCollectiveType()) continue;
      
      Envelope *env = (*titer).GetEnvelope();
      CB A (env->id, env->index); 
      bvt Abv; 
      Abv.resize(width);
      for(unsigned i=0; i < width; i++){
	Abv[i] = slv.new_variable();
      }
      bvEventMap.insert(std::pair<CB, bvt > 
		      (A,Abv));
      revBVEventMap.insert(std::pair<bvt, CB>(Abv, A));
    }
  }
  bool flag = false;
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
      if(last_node->GetTransition(*lit)->GetEnvelope()->isCollectiveType()){
	flag = true; 
	break;
      }
    }
    if(flag){
      bvt Abv; 
      Abv.resize(width);
      for(unsigned i=0; i < width; i++){
	Abv[i] = slv.new_variable();
      }
      collBVMap.insert(std::pair<MatchPtr, bvt > ((*mit),Abv));
      revCollBVMap.insert(std::pair<bvt, MatchPtr>(Abv, (*mit)));
      flag = false;
    }
  }
}

bvt Encoding3::getEventBV(CB A) 
{
  Envelope *envA = last_node->GetTransition(A)->GetEnvelope(); 

  if(!envA->isCollectiveType()){
    std::map<CB, bvt>::iterator bv_it;
    bv_it = bvEventMap.find(A);
    assert(bv_it != bvEventMap.end());
    return bv_it->second;
  }
  else{
    MatchPtr  Aptr = getMPtr(A);
    std::map<MatchPtr, bvt>::iterator bv_it;
    bv_it = collBVMap.find(Aptr);
    assert(bv_it != collBVMap.end());
    return bv_it->second;
  }
}

void Encoding3::insertClockEntriesInMap(CB B, CB A,  literalt c_ba)
{
  Envelope * envA = last_node->GetTransition(A)->GetEnvelope();
  Envelope * envB = last_node->GetTransition(B)->GetEnvelope();

  if(!envA->isCollectiveType() && !envB->isCollectiveType()){
    clkMap.insert(std::pair< std::pair<CB,CB>, literalt> (std::pair<CB, CB> (B,A), c_ba));
    revClkMap.insert(std::pair<literalt, std::pair<CB, CB> > (c_ba,std::pair<CB, CB> (B,A)));
  }
  else if (!envA->isCollectiveType() && envB->isCollectiveType()){
    MatchPtr Bptr = getMPtr(B);
    assert (Bptr != NULL);
    clkMapCollEvent.insert(std::pair< std::pair<MatchPtr,CB>, literalt> (std::pair<MatchPtr, CB>
									 (Bptr,A), c_ba));
    revClkMapCollEvent.insert(std::pair<literalt, std::pair<MatchPtr, CB> > 
			      (c_ba,std::pair<MatchPtr, CB> (Bptr,A)));
  } 
  else if(envA->isCollectiveType() && !envB->isCollectiveType()){
    MatchPtr Aptr = getMPtr(A);
    assert (Aptr != NULL);
    clkMapEventColl.insert(std::pair< std::pair<CB ,MatchPtr>, literalt>
			   (std::pair<CB ,MatchPtr> (B,Aptr), c_ba));
    revClkMapEventColl.insert(std::pair<literalt, std::pair<CB, MatchPtr> > 
			      (c_ba, std::pair<CB, MatchPtr> (B,Aptr)));
  }
  else { // both A and B are collectives
    MatchPtr Aptr = getMPtr(A);
    MatchPtr Bptr = getMPtr(B);
    clkMapCollColl.insert(std::pair< std::pair<MatchPtr ,MatchPtr>, literalt> 
			  (std::pair<MatchPtr ,MatchPtr> (Bptr,Aptr), c_ba));
    revClkMapCollColl.insert(std::pair<literalt, std::pair<MatchPtr, MatchPtr> > 
			     (c_ba, std::pair<MatchPtr, MatchPtr> (Bptr,Aptr)));
    
  }
}


void Encoding3::createClkLiterals()
{
  formula << "****PPO****" << std::endl; 
  slv.constraintStream << "****PPO****" << std::endl; 
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope * envA = (*titer).GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A(envA->id, envA->index);
      for(std::vector<int>::iterator vit = (*titer).get_ancestors().begin();
	  vit != (*titer).get_ancestors().end(); vit ++){
	CB B (envA->id, *vit);
	Envelope * envB = last_node->GetTransition(B)->GetEnvelope();
	if(envB->func_id == FINALIZE) continue;
	bvt Abv, Bbv;
	
	Abv = getEventBV(A);
	Bbv = getEventBV(B);
	
	literalt c_ba = bvUtils.unsigned_less_than(Bbv, Abv);

	insertClockEntriesInMap(B, A, c_ba);

	slv.l_set_to(c_ba, true); // PPO constraint

	formula << getClkLitName(c_ba,B, A) << " &" <<std::endl;
      }
    }
  }
}

void Encoding3::createRFConstraint()
{
  bool flag = false;
  formula << "****RF****" << std::endl;   
  slv.constraintStream << "****RF****" << std::endl; 
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
      if(last_node->GetTransition(*lit)->GetEnvelope()->isSendType() ||
	 last_node->GetTransition(*lit)->GetEnvelope()->isRecvType()){
	flag = true; 
	break;
      }
    }
    if(flag){ // hoping it to be a send-receive match
      assert((**mit).size() == 2);
      CB A = (**mit).front();
      CB B = (**mit).back();
      
      bvt Abv, Bbv;
      
      Abv = getEventBV(A);
      Bbv = getEventBV(B);
      
      //literalt c_ab = getClkLiteral(A, B); 
      literalt e_ab = bvUtils.equal(Abv, Bbv);  // [svs]: clk_a = clk_b
      literalt s_ab = getMatchLiteral(*mit);

      slv.l_set_to(slv.limplies(s_ab, e_ab), true);
      formula << "(" << getLitName(s_ab, 0) << " -> " 
	      << "e_ab" <<  ") & " <<std::endl;
	//getClkLitName(c_ab, A, B) << ") & " <<std::endl;
    }
  }
}

void Encoding3::createRFSomeConstraint()
{
  bvt rhs; 
  literalt s_m, m_a;
  bool flag = false;
  formula << "****RFSOME****" << std::endl; 
  slv.constraintStream << "****RFSOME****" << std::endl; 
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope * envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A(envA->id, envA->index);
      m_a = getMILiteral(A).first;
      if(envA->isRecvType() || envA->isSendType()) {
	forall_matchSet(mit, matchSet){
	  forall_match(lit, (**mit)){
	    if((*lit) == A) {
	      flag = true; 
	      break;
	    }
	  }
	  if(flag){
	    s_m = getMatchLiteral(*mit);
	    rhs.push_back(s_m);
	    flag = false;
	  }
	}
	if(!rhs.empty()){
	  slv.l_set_to(slv.limplies(m_a, slv.lor(rhs)) , true);
	  formula << "(" << getLitName(m_a,1) << " -> (";
	  for(bvt::iterator bit = rhs.begin(); bit != rhs.end(); bit++){
	    formula << getLitName(*bit,0) << " | ";  
	  }
	  formula << ")) &" << std::endl;
	  rhs.clear();
	}
      }
    }
  }
}

void Encoding3::createMatchConstraint()
{
  literalt m_a; 
  bvt rhs;
  bool flag = false;
  formula << "****MatchsetEvent****" << std::endl; 
  slv.constraintStream << "****MatchsetEvent****" << std::endl; 
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
      m_a = getMILiteral(*lit).first;
      rhs.push_back(m_a);
      if(last_node->GetTransition(*lit)->GetEnvelope()->isSendType())
	flag = true;
    }
    if(flag){
      literalt s_m = getMatchLiteral(*mit);
      slv.l_set_to(slv.limplies(s_m, slv.land(rhs)), true);
      formula << "(" << getLitName(s_m, 0) << " -> (";
      for(bvt::iterator bit = rhs.begin(); bit != rhs.end(); bit++){
	formula << getLitName(*bit,1) << " & ";  
      }
      flag = false;
      formula << ")) &" << std::endl;
      
    }
    rhs.clear();
  }
}

void Encoding3::createSerializationConstraint()
{
  formula << "****Serialization****" << std::endl; 
  slv.constraintStream << "****Serialization****" << std::endl; 
  
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope * envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A(envA->id, envA->index);
      forall_transitionLists(iterN, last_node->_tlist){
	forall_transitions(titerN, (*iterN)->_tlist){
	  Envelope * envB = titerN->GetEnvelope(); 
	  if(envB->func_id == FINALIZE) continue;
	  CB B(envB->id, envB->index);
	  if( A!=B){
	    literalt c_ab = getClkLiteral(A,B);
	    literalt c_ba = getClkLiteral(B,A); 
	    if(c_ab != c_ba)
	    slv.l_set_to(slv.lnot(slv.land(c_ab, c_ba)), true);
	    formula << "(!(" << getClkLitName(c_ab, A, B) << " & " 
		    << getClkLitName(c_ba, B, A) << ")) &" <<std::endl;
	  }
	}
      }
    }
  }
}

void Encoding3::createFrConstraint()
{
  literalt s_m;
  formula << "****FR****" << std::endl; 
  slv.constraintStream << "****FR****" << std::endl; 
  forall_matchSet(mit, matchSet){
    CB send = (**mit).front(); // assuming only send-recv matches exist
    CB recv = (**mit).back();
    if(last_node->GetTransition(send)->GetEnvelope()->isSendType()) {
      s_m = getMatchLiteral(*mit);
      assert((**mit).size() == 2);
    
      std::set<CB> image = _m->MImage(recv);
      for(std::set<CB>::iterator sit = image.begin(); 
	  sit != image.end(); sit++){
	if(send != (*sit)){
	  literalt c_send_send = getClkLiteral(send,(*sit));
	  literalt c_recv_send = getClkLiteral(recv, (*sit));
	  slv.l_set_to(slv.limplies(slv.land(s_m, c_send_send), c_recv_send), true);
	  formula << "((" << getLitName(s_m, 0) 
		  << " & " << getClkLitName(c_send_send, send, *sit)
		  << ") -> " << getClkLitName(c_recv_send, recv, *sit)
		  << ") &" <<std::endl;
	}
      }
    }
  }
}

void Encoding3::createUniqueMatchConstraint()
{
  literalt s_ab, s_ac;
  bvt rhs;
  formula << "****UniqueMatchForEvent****" << std::endl; 
  slv.constraintStream << "****UniqueMatchForEvent****" << std::endl; 
  forall_matchSet(mit, matchSet){
    CB send = (**mit).front();
    if(last_node->GetTransition(send)->GetEnvelope()->isSendType()) {
      assert((**mit).size() == 2);
      CB recv = (**mit).back();
      s_ab = getMatchLiteral(*mit);
      formula << "(" << getLitName(s_ab, 0) <<  " -> (";
      forall_matchSet(mitN, matchSet){
	CB sendp = (**mitN).front();
	if(last_node->GetTransition(sendp)->GetEnvelope()->isSendType()) {
	  CB recvp = (**mitN).back();
	  if (send == sendp && recv != recvp) {
	    s_ac = getMatchLiteral(*mitN);
	    rhs.push_back(slv.lnot(s_ac));
	    formula << "!" << getLitName(s_ac, 0) << " & "; 
	  }
	}
      }
      if(!rhs.empty()){
	slv.l_set_to (slv.limplies(s_ab, slv.land(rhs)), true);
	rhs.clear();
      }
      else{
	slv.l_set_to (slv.limplies(s_ab, one), true);
      }
      formula << ")) &" <<std::endl;
    }
  }
}

void Encoding3::uniqueMatchSend()
{
  literalt s_m;
  //bvt lst; 
  formula << "****UniqueMatchSend****" << std::endl; 
  slv.constraintStream << "****UniqueMatchSend****" << std::endl; 
  forall_matchSet(mit, matchSet){
    CB send = (**mit).front(); // assuming only send-recv matches exist
    CB recv = (**mit).back();
    if(last_node->GetTransition(send)->GetEnvelope()->isSendType()) {
      s_m = getMatchLiteral(*mit);
      assert((**mit).size() == 2);
      //lst.push_back(s_m);
      //std::cout << s_m.dimacs() << std::endl;
      std::set<CB> image = _m->MImage(send);
     for(std::set<CB>::iterator sit = image.begin(); 
	  sit != image.end(); sit++){
	if(recv != (*sit)){
	  std::stringstream ss;
	  ss << send._pid << send._index << (*sit)._pid << (*sit)._index;
	  literalt s_n = matchMap.find(ss.str())->second;
	  // lst.push_back(s_n);
	  //std::cout << s_n.dimacs() << std::endl;
	  // slv.l_set_to(slv.limplies(s_m, slv.lnot(s_n)), true);
	  // formula << "((" << getLitName(s_m, 0) 
	  // 	  << " & " << getClkLitName(c_recv_recv, *sit, recv)
	  // 	  << ") -> " << getClkLitName(c_recv_send, *sit, send)
	  // 	  << ") &" <<std::endl;
	  slv.l_set_to(slv.limplies(s_m, slv.lnot(s_n)), true);
	}
      }
     // formulat formula;
     // binomial_encodingt be(slv);
     // be.atmostk(lst, 1, formula);
     // std::cout <<" ----- formula ---- " << std::endl;
     // be.print_formula(std::cout,formula);
     // std::cout <<" ----- end formula ---- " << std::endl;
     //     be.add_to_prop(formula);
    }
    // lst.clear();
  }
}

void Encoding3::uniqueMatchRecv()
{
  literalt s_m;
  //bvt lst;
  formula << "****UniqueMatchSend****" << std::endl; 
  slv.constraintStream << "****UniqueMatchSend****" << std::endl; 
  forall_matchSet(mit, matchSet){
    CB send = (**mit).front(); // assuming only send-recv matches exist
    CB recv = (**mit).back();
    if(last_node->GetTransition(send)->GetEnvelope()->isSendType()) {
      s_m = getMatchLiteral(*mit);
      assert((**mit).size() == 2);
      //  lst.push_back(s_m);
      std::set<CB> image = _m->MImage(recv);
     for(std::set<CB>::iterator sit = image.begin(); 
	  sit != image.end(); sit++){
       if(send != (*sit)){
	 std::stringstream ss;
	  ss << (*sit)._pid << (*sit)._index << recv._pid << recv._index;
	  literalt s_n = matchMap.find(ss.str())->second;
	  //  lst.push_back(s_n);
	  slv.l_set_to(slv.limplies(s_m, slv.lnot(s_n)), true);
	  // formula << "((" << getLitName(s_m, 0) 
	  // 	  << " & " << getClkLitName(c_recv_recv, *sit, recv)
	  // 	  << ") -> " << getClkLitName(c_recv_send, *sit, send)
	  // 	  << ") &" <<std::endl;
	}
     }
     // formulat formula;
     // binomial_encodingt be(slv);
     // be.atmostk(lst, 1, formula); 
     // be.add_to_prop(formula);
    }
    //    lst.clear();
  }
}



void Encoding3::alternativeUniqueMatchConstraint()
{
  literalt s_m;
  formula << "****alternativeUniqueMatch****" << std::endl; 
  slv.constraintStream << "****alternativeUniqueMatch****" << std::endl; 
  forall_matchSet(mit, matchSet){
    CB send = (**mit).front(); // assuming only send-recv matches exist
    CB recv = (**mit).back();
    if(last_node->GetTransition(send)->GetEnvelope()->isSendType()) {
      s_m = getMatchLiteral(*mit);
      assert((**mit).size() == 2);
    
      std::set<CB> image = _m->MImage(send);
     for(std::set<CB>::iterator sit = image.begin(); 
	  sit != image.end(); sit++){
	if(recv != (*sit)){
	  literalt c_recv_recv = getClkLiteral((*sit), recv);
	  literalt c_recv_send = getClkLiteral((*sit), send);
	  slv.l_set_to(slv.limplies(slv.land(s_m, c_recv_recv), c_recv_send), true);
	  formula << "((" << getLitName(s_m, 0) 
		  << " & " << getClkLitName(c_recv_recv, *sit, recv)
		  << ") -> " << getClkLitName(c_recv_send, *sit, send)
		  << ") &" <<std::endl;
	}
      }
    }
  }
}




void Encoding3::allFstIssued ()
{
  bvt c;
  formula << "****allFstIssued****" << std::endl;
  slv.constraintStream << "****allFstIssued****" << std::endl;
  formula << "(";
  bool AhasanAncestor = false;
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A(envA->id, envA->index);
      forall_transitions(titerN, (*iter)->_tlist){
	Envelope *envB = titerN->GetEnvelope();
	if(envB->func_id == FINALIZE) continue;
	CB B(envB->id, envB->index);
	if(last_node->isAncestor(A,B) && envB->isBlockingType()) {
	  AhasanAncestor = true; 
	  break;
	}
      }
      if(AhasanAncestor){
	AhasanAncestor = false;
	continue;
      }
      else{
	literalt i_a = getMILiteral(A).second;
	literalt m_a = getMILiteral(A).first;
	c.push_back(i_a);
	if(envA->isCollectiveType())
	  formula << getLitName(m_a,4) << " & ";
	else
	  formula << getLitName(m_a,3) << " & ";
      }
    }
  }
  formula << ") & " << std::endl;
  slv.l_set_to(slv.land(c), true);
}



void Encoding3::noMoreMatchesPossible()
{
  bvt c, res;
  formula << "****noMoreMatchesPossible****" << std::endl; 
  slv.constraintStream << "****noMoreMatchesPossible****" << std::endl; 
  forall_matchSet(mit, matchSet){
    //    assert((**mit).size() == 2);
    formula << "(";
    forall_match(lit, (**mit)){
      std::pair<literalt,literalt> p = getMILiteral(*lit);

      c.push_back(p.first);
      c.push_back(slv.lnot(p.second));
      // Envelope *envA = last_node->GetTransition(*lit)->GetEnvelope();
      // std::set<int> ancs = last_node->getAllAncestors(*lit);      
      // for(std::set<int>::iterator sit = ancs.begin(); 
      // 	  sit != ancs.end(); sit++){
      // 	CB B((*lit)._pid, *sit);
      // 	Envelope *envB = last_node->GetTransition(B)->GetEnvelope();
      // 	if((envA->func_id == ISEND || envA->func_id == SEND) &&
      // 	   (envA->func_id == envB->func_id) && 
      // 	   (envA->dest == envB->dest) ){
      // 	  std::pair<literalt,literalt> q = getMILiteral(B);
      // 	  c.push_back(slv.lnot(q.first));
      // 	  formula << "!" << getLitName(q.first, 1) << " | ";
	  
      // 	}
      // 	else if ((envA->func_id == IRECV) &&
      // 		 (envA->func_id == envB->func_id) && 
      // 		 (envA->src == envB->src) ){
      // 	  std::pair<literalt,literalt> q = getMILiteral(B);
      // 	  c.push_back(slv.lnot(q.first));
      // 	  formula <<"!" << getLitName(q.first, 1) << " | ";
	  
      // 	}
      // }
      if(last_node->GetTransition(*lit)->GetEnvelope()->isCollectiveType()){
	formula << getLitName(p.first,2) << " | " 
		<< "!" << getLitName(p.first, 4) << " | ";
      }
      else{
	formula << getLitName(p.first,1) << " | " 
		<< "!" << getLitName(p.first, 3) << " | ";
	
      }
    }
    // res.push_back(slv.lor(c));
    slv.l_set_to(slv.lor(c), true);
    c.clear();
    formula << ") &" << std::endl;
  }
  //  slv.l_set_to(slv.land(res), true);
}

void Encoding3::transitiveConstraint()
{
  formula << "****transitiveConstraint****" << std::endl;
  slv.constraintStream << "****transitiveConstraint****" << std::endl;
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A (envA->id, envA->index);
      forall_transitionLists(iterN, last_node->_tlist){
	forall_transitions(titerN, (*iterN)->_tlist){
	  Envelope *envB = titerN->GetEnvelope();
	  if(envB->func_id == FINALIZE) continue;
	  CB B (envB->id, envB->index);
	  if(A != B){
	    literalt c_ab = getClkLiteral(A,B);
	    forall_transitionLists(iterM, last_node->_tlist){
	      forall_transitions(titerM, (*iterM)->_tlist){
		Envelope *envC = titerM->GetEnvelope();
		if(envC->func_id == FINALIZE) continue;
		CB C (envC->id, envC->index);
		if(B != C && C!= A){
		  literalt c_bc = getClkLiteral(B,C);
		  literalt c_ac = getClkLiteral(A,C);
		  slv.l_set_to(slv.limplies(slv.land(c_ab, c_bc), c_ac),true);
		  formula << "((" << getClkLitName(c_ab,A, B) 
			  << " & " << getClkLitName(c_bc, B,C) 
			  << ") -> " << getClkLitName(c_ac, A,C)
			  << ") &" << std::endl;
		}
	      }
	    }	
	  }
        }
      }
    }
  }
}


void Encoding3::alternateAllAncestorsMatched()
{
 bvt rhs;
  formula << "****allAncestorsMatched****" << std::endl;
  slv.constraintStream << "****allAncestorsMatched****" << std::endl;
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A (envA->id, envA->index);
      std::pair<literalt, literalt> p = getMILiteral(A);
      literalt m_a = p.first;
      literalt i_a = p.second;
      if(envA->isCollectiveType())
	formula << "(" << getLitName(m_a,4) << " <-> (";
      else
	formula  << "(" << getLitName(m_a,3) << " <-> (" ;
      
      std::vector<int> ancs = last_node->GetTransition(A)->get_ancestors();
      for(std::vector<int>::iterator vit = ancs.begin(); 
	  vit != ancs.end(); vit++){
	CB B(envA->id, *vit);
	std::pair<literalt, literalt> q = getMILiteral(B);
	//if(last_node->GetTransition(B)->GetEnvelope()->isBlockingType())
	  rhs.push_back(q.first);
      }
      if(!rhs.empty()){
	for(bvt::iterator bit = rhs.begin(); bit!=rhs.end(); bit++){
	  formula << getLitName(*bit, 1) << " & "; 
	}
	 formula << ")";  
	slv.l_set_to(slv.land(slv.limplies(slv.land(rhs),i_a), 
			      slv.limplies(i_a, slv.land(rhs))), true);
	
	rhs.clear();
      }
      else {
	slv.l_set_to(slv.land(slv.limplies(one,i_a), 
			      slv.limplies(i_a, one)), true);
      }
      formula << ") & " << std::endl;
    }
  }
}


void Encoding3::allAncestorsMatched()
{
  bvt rhs;
  formula << "****allAncestorsMatched****" << std::endl;
  slv.constraintStream << "****allAncestorsMatched****" << std::endl;
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A (envA->id, envA->index);
      std::pair<literalt, literalt> p = getMILiteral(A);
      literalt m_a = p.first;
      literalt i_a = p.second;
      if(envA->isCollectiveType())
	formula << "(" << getLitName(m_a,4) << " <-> (";
      else
	formula  << "(" << getLitName(m_a,3) << " <-> (" ;
      forall_transitions(titerN, (*iter)->_tlist){
	Envelope *envB = titerN->GetEnvelope();
	if(envB->func_id == FINALIZE) continue;
	CB B (envB->id, envB->index);
	
	if(last_node->isAncestor(A,B) && envB->isBlockingType()){
	  //if(last_node->isAncestor(A,B)){ 
	  literalt m_b = getMILiteral(B).first; 
	  rhs.push_back(m_b);
	  //	if(envB->isCollectiveType())
	  //formula << getLitName(m_b, 2) << " & ";
	  // else
	  //  formula << getLitName(m_b, 1) << " & ";
	  
	}
      }
      if(!rhs.empty()){
	for(bvt::iterator bit = rhs.begin(); bit!=rhs.end(); bit++){
	  formula << getLitName(*bit, 1) << " & "; 
	}
	 formula << ")";  
	slv.l_set_to(slv.land(slv.limplies(slv.land(rhs),i_a), 
			      slv.limplies(i_a, slv.land(rhs))), true);
	
	rhs.clear();
      }
      else {
	slv.l_set_to(slv.land(slv.limplies(one,i_a), 
			      slv.limplies(i_a, one)), true);
      }
      formula << ") & " << std::endl;
    }
  }
}


void Encoding3::totalOrderOnSends()
{
  formula << "****totalOrderOnSends***" << std::endl;
  slv.constraintStream << "****totalOrderOnSends***" << std::endl;
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A (envA->id, envA->index);
      forall_transitionLists(iterN, last_node->_tlist){
	forall_transitions(titerN, (*iterN)->_tlist){
	  Envelope *envB = titerN->GetEnvelope();
	  if(envB->func_id == FINALIZE) continue;
	  CB B (envB->id, envB->index);
	  if(envA->isSendType() && envB->isSendType() && A != B){
	    literalt m_a = getMILiteral(A).first; 
	    literalt m_b = getMILiteral(B).first;
	    literalt c_ab = getClkLiteral(A,B);
	    literalt c_ba = getClkLiteral(B,A);
	    // slv.l_set_to(slv.limplies(slv.land(m_a, m_b), 
	    // 			      slv.land(slv.limplies(slv.lnot(c_ab), c_ba), 
	    // 				       slv.limplies(c_ba, slv.lnot(c_ab)))), true);
	    slv.l_set_to(slv.land(slv.limplies(slv.lnot(c_ab), c_ba), 
				  slv.limplies(c_ba, slv.lnot(c_ab))), true); 
	    formula << "(!" << getClkLitName(c_ab, A, B) << " <-> "
		    << getClkLitName(c_ba, B, A) << ") &" <<std::endl;
	  }
	}
      }
    }
  }
}

void Encoding3::totalOrderOnRacingSends()
{
  formula << "****totalOrderOnRacingSends***" << std::endl;
  slv.constraintStream << "****totalOrderOnSends***" << std::endl;
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A (envA->id, envA->index);
      forall_transitionLists(iterN, last_node->_tlist){
	forall_transitions(titerN, (*iterN)->_tlist){
	  Envelope *envB = titerN->GetEnvelope();
	  if(envB->func_id == FINALIZE) continue;
	  CB B (envB->id, envB->index);
	  if(envA->isSendType() && envB->isSendType() && (A != B) &&  
	     (envA->dest == envB->dest)){
	    literalt m_a = getMILiteral(A).first; 
	    literalt m_b = getMILiteral(B).first;
	    literalt c_ab = getClkLiteral(A,B);
	    literalt c_ba = getClkLiteral(B,A);
	    // slv.l_set_to(slv.limplies(slv.land(m_a, m_b), 
	    // 			      slv.land(slv.limplies(slv.lnot(c_ab), c_ba), 
	    // 				       slv.limplies(c_ba, slv.lnot(c_ab)))), true);
	    slv.l_set_to(slv.land(slv.limplies(slv.lnot(c_ab), c_ba), 
				  slv.limplies(c_ba, slv.lnot(c_ab))), true); 
	    formula << "(!" << getClkLitName(c_ab, A, B) << " <-> "
		    << getClkLitName(c_ba, B, A) << ") &" <<std::endl;
	  }
	}
      }
    }
  }
}

void Encoding3::matchImpliesIssued()
{

  formula << "****matchImpliesIssued***" << std::endl;
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = (*titer).GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A(envA->id, envA->index);
      literalt m_a = getMILiteral(A).first;
      literalt i_a = getMILiteral(A).second;
      slv.l_set_to(slv.limplies(m_a, i_a), true);
      if(envA->isCollectiveType())
	formula << "(" << getLitName(m_a, 2) << " -> "
		<< getLitName(m_a, 4) << ") &" << std::endl;
      else
	formula << "(" << getLitName(m_a, 1) << " -> "
		<< getLitName(m_a, 3) << ") &" << std::endl;
    }
  }
}

void Encoding3::waitMatch()
{
  formula << "****waitMatch****" << std::endl;
  bvt rhs;
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A(envA->id, envA->index);
      literalt m_a = getMILiteral(A).first;
      if(envA->func_id == WAIT || envA->func_id == WAITALL) {
	std::vector<int> ancs = titer->get_ancestors();
	for(std::vector<int>::iterator sit = ancs.begin(); 
	    sit != ancs.end(); sit++){
	  //	forall_transitions(titerN, (*iter)->_tlist){
	  CB B(envA->id, *sit);
  	  Envelope *envB = last_node->GetTransition(B)->GetEnvelope();
  	  if(envB->func_id == FINALIZE) continue;
	  //if(last_node->isAncestor(A,B)){
	  literalt m_b = getMILiteral(B).first;
	  rhs.push_back(m_b);
	  //}
	}
	if(!rhs.empty()){
	  slv.l_set_to(slv.land(slv.limplies(m_a, slv.land(rhs)),
				slv.limplies(slv.land(rhs), m_a)), true);
	  
	  formula << "(" << getLitName(m_a, 1) << " <-> (";
	  for(bvt::iterator bit = rhs.begin(); bit != rhs.end(); bit++){
	    formula << getLitName(*bit, 1) << " & " ;
	  }
	  formula << ")) &" << std::endl;
	  rhs.clear();
	}
	else{
	  slv.l_set_to(slv.land(slv.limplies(m_a, one),
				slv.limplies(one, m_a)), true);
	  
	}
      }
    }
  }
}

void Encoding3::nonOverTakingMatch()
{
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A(envA->id, envA->index);
      if((envA->func_id == ISEND || envA->func_id == SEND) 
	 || envA->func_id == IRECV){
	std::vector<int> ancs = titer->get_ancestors();      
	for(std::vector<int>::iterator sit = ancs.begin(); 
	    sit != ancs.end(); sit++){
	  CB B(A._pid, *sit);
	  Envelope *envB = last_node->GetTransition(B)->GetEnvelope();
	  if(envA->func_id == envB->func_id) {
	    if((envA->isSendType() && (envA->src == envB->src)) ||
	       (envA->isRecvType() && (envA->src == envB->src))){
	      std::pair<literalt,literalt> p = getMILiteral(A);
	      std::pair<literalt,literalt> q = getMILiteral(B);
	      slv.l_set_to(slv.limplies(p.first, q.first), true);
	      formula <<  "(" << getLitName(p.first, 1) << " -> " 
		      << getLitName(q.first, 1) << ") &";
	    }
	  }
	} 
      }
    }
  }
}

void Encoding3::notAllMatched()
{
  bvt c;
  formula << "****notAllMatched****" << std::endl;
  slv.constraintStream << "****notAllMatched****" << std::endl;
  formula << "("; 
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A(envA->id, envA->index);
      literalt m_a = getMILiteral(A).first;
      c.push_back(slv.lnot(m_a));
      if(envA->isCollectiveType())
	formula << "!" << getLitName(m_a,2) << " | ";
      else
	formula << "!" << getLitName(m_a,1) << " | ";
    }
  }
  formula << ")" << std::endl;
  slv.l_set_to(slv.lor(c), true);
}

void Encoding3::makingMatchesHappenSooner()
{
  literalt s_m;
  bvt lst;
  formula << "****MatchesHappenSooner****" << std::endl; 
  forall_matchSet(mit, matchSet){
    CB send = (**mit).front(); // assuming only send-recv matches exist
    CB recv = (**mit).back();
    if(last_node->GetTransition(send)->GetEnvelope()->isSendType()) {
      s_m = getMatchLiteral(*mit);
      std::vector<int> Sancs = last_node->GetTransition(send)->get_ancestors();
      std::vector<int> Rancs = last_node->GetTransition(recv)->get_ancestors();
      bvt Sbv;
      Sbv = getEventBV(send);
      bvt onebv = bvUtils.build_constant(1,width);
      bvt lst; 
      if (Sancs.empty() && Rancs.empty()){
  	slv.l_set_to(slv.limplies(s_m, bvUtils.is_zero(Sbv)) ,true);
      }
      else{
	if(!Sancs.empty()){
	  for(std::vector<int>::iterator vit = Sancs.begin();
	      vit != Sancs.end(); vit ++){
	    CB c(send._pid, (*vit)); 
	    bvt Cbv = getEventBV(c);
	    literalt l = bvUtils.equal(bvUtils.sub(Sbv, Cbv), onebv);
	    lst.push_back(l);
	  }
	}
	if(!Rancs.empty()){
	  for(std::vector<int>::iterator vit = Rancs.begin();
	      vit != Rancs.end(); vit ++){
	    CB c(recv._pid, (*vit)); 
	    bvt Cbv = getEventBV(c);
	    literalt l = bvUtils.equal(bvUtils.sub(Sbv, Cbv), onebv);
	    lst.push_back(l);
	  }
	}
	slv.l_set_to(slv.limplies(s_m, slv.lor(lst)), true);
      }
    }  
  }
}

void Encoding3::publish()
{
  tvt result;
  literalt x_ap;
  bool flag = false;
  
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = (*titer).GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A(envA->id, envA->index);
      literalt m_a = getMILiteral(A).first;
      literalt i_a = getMILiteral(A).second;
      switch(slv.l_get(m_a).get_value()){ 
      case tvt::TV_TRUE:
	if(envA->isCollectiveType())
	  formula << getLitName(m_a, 2) << ":1" << std::endl;
	else
	  formula << getLitName(m_a, 1) << ":1" << std::endl;
	break;
      case tvt::TV_FALSE:
	if(envA->isCollectiveType())
	  formula << getLitName(m_a,2) << ":0" << std::endl;
	else
	  formula << getLitName(m_a,1) << ":0" << std::endl;
	break;
      case tvt::TV_UNKNOWN:
	if(envA->isCollectiveType())
	  formula << getLitName(m_a,2) << ":UNKNOWN" << std::endl;
	else
	  formula << getLitName(m_a,1) << ":UNKNOWN" << std::endl;
	break;
      default: assert(false);
      }
      switch(slv.l_get(i_a).get_value()){ 
      case tvt::TV_TRUE:
	if(envA->isCollectiveType())
	  formula << getLitName(m_a, 4) << ":1" << std::endl;
	else
	  formula << getLitName(m_a, 3) << ":1" << std::endl;
      	break;
      case tvt::TV_FALSE:
	if(envA->isCollectiveType())
	  formula << getLitName(m_a, 4) << ":0" << std::endl;
	else
	  formula << getLitName(m_a, 3) << ":0" << std::endl;
      	break;
      case tvt::TV_UNKNOWN:
	if(envA->isCollectiveType())
	  formula << getLitName(m_a, 4) << ":UNKNOWN" << std::endl;
	else
	  formula << getLitName(m_a, 3) << ":UNKNOWN" << std::endl;
      	break;
      default: assert(false);
      }
      // forall_transitionLists(iterN, last_node->_tlist){
      // 	forall_transitions(titerN, (*iterN)->_tlist){
      // 	  Envelope *envB = (*titerN).GetEnvelope();
      // 	  if(envB->func_id == FINALIZE) continue;
      // 	  CB B(envB->id, envB->index);
      // 	  if(A != B) {
      // 	    literalt c_ab = getClkLiteral(A,B);
      // 	    switch(slv.l_get(c_ab).get_value()){ 
      // 	    case tvt::TV_TRUE:
      // 	      formula << getClkLitName(c_ab, A, B) << ":1" << std::endl;
      // 	      break;
      // 	    case tvt::TV_FALSE:
      // 	      formula << getClkLitName(c_ab, A, B) << ":0" << std::endl;
      // 	      break;
      // 	    case tvt::TV_UNKNOWN:
      // 	      formula << getClkLitName(c_ab,A, B) << ":UNKNOWN" << std::endl;
      // 	      break;
      // 	    default: assert(false);
      // 	    }	    
      // 	  }
      // 	}
      // }
    }
  }
  forall_matchSet(mit, matchSet){
    CB A = (**mit).front();
    if(last_node->GetTransition(A)->GetEnvelope()->isSendType()){
      literalt s_ab = getMatchLiteral(*mit);
      switch(slv.l_get(s_ab).get_value()){ 
      case tvt::TV_TRUE:
	formula << getLitName(s_ab,0 ) << ":1" << std::endl;
	break;
      case tvt::TV_FALSE:
	formula << getLitName(s_ab, 0) << ":0" << std::endl;
	break;
      case tvt::TV_UNKNOWN:
	formula << getLitName(s_ab, 0) << ":UNKNOWN" << std::endl;
	break;
      default: assert(false);
      }
    }
  }
}


void Encoding3::encodingPartialOrders()
{

  createMatchSet();
  //  printMatchSet();
  //std::cout << formula.str();
  createEventLiterals();
  set_width();
  createBVEventLiterals();
  createMatchLiterals();
  
  gettimeofday(&constGenStart, NULL);
  
  createClkLiterals();
  createRFConstraint();
  createRFSomeConstraint();
  createMatchConstraint();
  //createSerializationConstraint();
  //createFrConstraint();
  // formula.str("");
  // formula.clear();
  //createUniqueMatchConstraint();
  //alternativeUniqueMatchConstraint();
  uniqueMatchSend();
  uniqueMatchRecv();
  // totalOrderOnSends();
  //  totalOrderOnRacingSends();
  //allFstIssued();
  noMoreMatchesPossible();
  //  transitiveConstraint();
  //  allAncestorsMatched();
  alternateAllAncestorsMatched();
  matchImpliesIssued();
  waitMatch();
  //nonOverTakingMatch();
  notAllMatched();
  //  makingMatchesHappenSooner();
  gettimeofday(&constGenEnd, NULL);
  getTimeElapsed(constGenStart, constGenEnd);
  
  //std::cout << formula.str();
  formula.str("");
  formula.clear();
  
  std::cout << "********* SAT VALUATIONS ************" << std::endl;
  std::cout << "Number of Clauses: " << slv.no_clauses() << std::endl;
  std::cout << "Number of Variables: " << slv.no_variables() << std::endl;
  std::cout << "Constraint Generation Time: "
	  << (getTimeElapsed(constGenStart, constGenEnd)*1.0)/1000000 << "sec \n";
  
  gettimeofday(&solverStart, NULL);
  satcheckt::resultt answer = slv.prop_solve();
  gettimeofday(&solverEnd, NULL);
  switch(answer){
  case satcheckt::P_UNSATISFIABLE:
    formula << "Formula is UNSAT" <<std::endl;
    break;
  case satcheckt::P_SATISFIABLE:
    formula  << "Formula is SAT -- DEADLOCK DETECTED" <<std::endl;
    _deadlock_found = true;
    publish();
    break;
    // output the valuations
  default: 
    formula << "ERROR in SAT SOLVING" <<std::endl;
    break;
  }
  //std::cout << slv.constraintStream.str();
  
  std::cout << "Solving Time: " << (getTimeElapsed(solverStart, solverEnd)*1.0)/1000000 << "sec \n";
  size_t peakSize = getPeakRSS();
  std::cout << "Mem (MB): " << peakSize/(1024.0*1024.0) << std::endl;
  std::cout << formula.str();
  std::cout << std::endl;
  
}


