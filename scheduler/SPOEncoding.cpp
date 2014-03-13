#include "SPOEncoding.hpp"

////////////////////////////////////////////////////////////
/////                                                ///////
////        SPO ENCODING                             ///////
////////////////////////////////////////////////////////////

void SPOEncoding::set_width()
{
  width = address_bits();
  
}

unsigned SPOEncoding::get_width(){
    return width;
}

unsigned SPOEncoding::address_bits()
{
  assert(eventSize == 0);
  forall_transitionLists(iter, last_node->_tlist){
    eventSize += (*iter)->_tlist.size();
  }
  unsigned res, x=2;
  for(res=1; x<eventSize; res+=1, x*=2);
  return res;
}


void SPOEncoding::createPossibleMatches()
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
void SPOEncoding::createMatchLiterals()
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
      literalt X_m = slv->new_variable();
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

literalt SPOEncoding::getMatchLiteral(MatchPtr mptr)
{
  std::string symbol = match2symMap.find(mptr)->second;
  assert(!symbol.empty());
  return matchMap.find(symbol)->second;
}


void SPOEncoding::createFinalizeWaitLiterals()
{
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *env = (*titer).GetEnvelope();
      CB f(env->id, env->index);
      if((env->func_id == FINALIZE) ||
	 env->isWaitorTestType()){
	literalt X_f = slv->new_variable();
	eventMap.insert(std::pair<CB, literalt> (f, X_f));
	revEventMap.insert(std::pair<literalt, CB>(X_f, f));
      }
    }
  }
}

literalt SPOEncoding::getFinalizeWaitLiterals(CB f)
{
  std::map<CB, literalt>::iterator iter;
  iter = eventMap.find(f);
  if(iter != eventMap.end())
    return (*iter).second;
  assert(false); // should never reach here
}

void SPOEncoding::createBVLiterals()
{
 forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *env = (*titer).GetEnvelope();
      if(env->isCollectiveType()) continue;
      CB A (env->id, env->index); 
      bvt Abv; 
      Abv.resize(width);
      for(unsigned i=0; i < width; i++){
	Abv[i] = slv->new_variable();
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
	Abv[i] = slv->new_variable();
      }
      collBVMap.insert(std::pair<MatchPtr, bvt > ((*mit),Abv));
      revCollBVMap.insert(std::pair<bvt, MatchPtr>(Abv, (*mit)));
      flag = false;
    }
  }
}

bvt SPOEncoding::getBVLiterals(CB A) 
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

MatchPtr SPOEncoding::getMPtr(CB A) 
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


void SPOEncoding::dlock()
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
	lst.push_back(slv->lnot(X_f));
	//slv->l_set_to(slv->lnot(X_f), true);
	formula << "!" << getLitName(X_f,1) << " | "; 
      }
    }
  }
  slv->l_set_to(slv->lor(lst), true);
  formula << ")" << std::endl;
}

void SPOEncoding::m2Clk()
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
      literalt e = bvUtils->equal(Sbv, Rbv);  // [svs]: clk_s = clk_r
      slv->l_set_to(slv->land(slv->limplies(X_m, e), 
			   slv->limplies(e, X_m)), true);
    }
  }
}

void SPOEncoding::processPO()
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
	
	literalt c_ba = bvUtils->unsigned_less_than(Bbv, Abv);
	slv->l_set_to(c_ba, true); // PPO constraint
      }
    }
  }
}

void SPOEncoding:: init()
{
  bvt lst;
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
	  slv->l_set_to(X_f, true);
	}
	if( envA->isRecvType()){//(envA->isSendType() || envA->isRecvType()){
	 
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
	    //  slv->l_set_to(slv->lor(lst), true);
	  }
	}
	if(envA->isCollectiveType()){ 
	  MatchPtr mptr = getMPtr(A);
	  literalt X_l = getMatchLiteral(mptr);
	  formula << getLitName(X_l, 0) << " & ";
	  slv->l_set_to(X_l, true);
	}
	// waits can have no predecessors under infinite
	// buffering model
	if(envA->isWaitorTestType()){
	  literalt X_w = getFinalizeWaitLiterals(A);
	  formula << getLitName(X_w, 1) << " & ";
	  slv->l_set_to(X_w, true);
	}
      }
    }
  }
   slv->l_set_to(slv->lor(lst), true);
  formula << ") & " << std::endl;
}

literalt SPOEncoding::exclusive(CB q, MatchPtr m)
{
  bvt lst;
  formula << " & (";
  forall_matchSet(mit, matchSet){  
    CB front = (**mit).front();
    CB back = (**mit).back();
    if((q == front) || (q == back)){
      if((*mit) != m){
	literalt X_l = getMatchLiteral(*mit);
	lst.push_back(slv->lnot(X_l));
	formula << "!" <<getLitName(X_l, 0) << " & "; 
      }
    }
  }
  if(!lst.empty()){
    formula << ")"; 
    return slv->land(lst);
  }
  formula << "one)";
  return one;
  //assert(false);
}

literalt SPOEncoding::predsMatched(CB q)
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
	lst.push_back(slv->lor(tmp));
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
    return slv->land(lst);
  }
  formula << "one)"; 
  return one;
  //assert(false);
}


void SPOEncoding:: ext()
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
	slv->l_set_to(slv->land(slv->limplies(X_m, slv->land(lst)), 
			      slv->limplies(slv->land(lst), X_m)), true);
      }
      else
	slv->l_set_to(slv->land(slv->limplies(X_m, one), 
			      slv->limplies(one, X_m)), true);
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
	slv->l_set_to(slv->land(slv->limplies(X_n, slv->land(lst)), 
			      slv->limplies(slv->land(lst), X_n)), true);
      }
      else
	slv->l_set_to(slv->land(slv->limplies(X_n, one), 
			      slv->limplies(one, X_n)), true);
    }
    if((envA->func_id ==FINALIZE) || 
       envA->isWaitorTestType()){
      bvt lst;
      forall_match(lit, (**mit)){
	literalt X_f = getFinalizeWaitLiterals(*lit);
	formula << "(" << getLitName(X_f,1) << " <-> (";
	literalt pred = predsMatched(*lit);
	formula << ")) & " <<std::endl;
	slv->l_set_to(slv->land(slv->limplies(X_f, pred), 
			      slv->limplies(pred, X_f)), true);
      }
    }
  }
}

std::string SPOEncoding::getLitName(literalt lt, int type)
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



void SPOEncoding::publish()
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
      switch(slv->l_get(*bit).get_value()){
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
      switch(slv->l_get(*bit).get_value()){
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

void SPOEncoding::generateConstraints()
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
}

void SPOEncoding::poEnc()
{
  generateConstraints();
 
  if(Scheduler::_formula==true){
    std::ofstream formulaFile;
    std::stringstream ss;
    ss << _it->sch->getProgName() << "."; 
    if(Scheduler::_send_block)
      ss << "b.";
    ss << _it->sch->getNumProcs() << ".formula";
    formulaFile.open(ss.str().c_str());
    formulaFile << formula.str();
    formulaFile.close();
  }  
 
  
  formula.str("");
  formula.clear();

  getTimeElapsed(constGenStart, constGenEnd);
  formula << "********* SAT VALUATIONS ************" << std::endl;
  formula << "Number of Clauses: " <<  static_cast<cnf_solvert *>(slv)->no_clauses() << std::endl;
  formula << "Number of Variables: " << slv->no_variables() << std::endl;
  formula << "Constraint Generation Time: "
	    << (getTimeElapsed(constGenStart, constGenEnd)*1.0)/1000000 << "sec \n";

  
  gettimeofday(&solverStart, NULL);
  satcheckt::resultt answer = slv->prop_solve();
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
  //std::cout << //slv->constraintStream.str();
  
  formula<< "Solving Time: " << (getTimeElapsed(solverStart, solverEnd)*1.0)/1000000 << "sec \n";
  size_t peakSize = getPeakRSS();
  formula << "Mem (MB): " << peakSize/(1024.0*1024.0) << std::endl;

  std::cout << formula.str();
  std::cout << std::endl;
}
