#include "FMEncoding.hpp"
#include <fstream> 

////////////////////////////////////////////////////////////
/////                                                ///////
////        FMEncoding                               ///////
////////////////////////////////////////////////////////////

void FMEncoding::set_width()
{
  width = address_bits();
}

unsigned FMEncoding::get_width(){
  return width;
}

unsigned FMEncoding::address_bits()
{
  unsigned res, x=2;
  for(res=1; x<eventSize; res+=1, x*=2);
  return res;
}

void FMEncoding::isLitCreatedForCollEvent(CB A, literalt & m_e)
{
  Envelope *envA = last_node->GetTransition(A)->GetEnvelope();
  MatchPtr cMatch = getMPtr(A);
  forall_match(lit, (*cMatch)){
    std::map<CB, std::pair<literalt, literalt> >::iterator
      eit = eventMap.find(*lit);
    if(eit != eventMap.end()){
      m_e = eit->second.first;
      return;
    }
  }
  m_e = slv->new_variable();
  return;
}



void FMEncoding::createEventLiterals ()
{
  
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      literalt m_e, i_e;
      Envelope *env = (*titer).GetEnvelope();
      CB A (env->id, env->index); 
      if(env->func_id == FINALIZE) continue;
      if(env->isCollectiveType()){
	isLitCreatedForCollEvent(A, m_e);
      }
      else{
	m_e = slv->new_variable();
      }
      
      i_e = slv->new_variable();


      //insert in to the map
      eventMap.insert(std::pair<CB, std::pair<literalt, literalt> > 
		      (A,std::pair<literalt, literalt> (m_e, i_e)));
      revEventMap.insert(std::pair<literalt, CB>(m_e, A));
      eventSize++;
    }
  }
  // bool flag = false;
  // forall_matchSet(mit, matchSet){
  //   forall_match(lit, (**mit)){
  //     if(last_node->GetTransition(*lit)->GetEnvelope()->isCollectiveType()){
  // 	flag = true; 
  // 	break;
  //     }
  //   }
  //   if(flag){
  //     literalt m_c = slv->new_variable();
  //     literalt i_c = slv->new_variable();
  //     collEventMap.insert(std::pair<MatchPtr, std::pair<literalt, literalt> > 
  // 			  ((*mit),std::pair<literalt, literalt> (m_c, i_c)));
  //     revCollMap.insert(std::pair<literalt, MatchPtr>(m_c, (*mit)));
  //     flag = false;
  //     eventSize++;
  //   }
  // }
}


void FMEncoding::printEventMap()
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

void FMEncoding::createMatchLiterals()
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
      literalt s_m = slv->new_variable();
      // //slv->constraintStream << matchNumeral << " s_m = " << s_m.get() 
      // 			       << std::endl;
	  
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

literalt FMEncoding::getClkLiteral(CB A, CB B)
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
      literalt c_ab = bvUtils->unsigned_less_than(Abv, Bbv);
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
      literalt c_ab = bvUtils->unsigned_less_than(Abv, Bbv);
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
      literalt c_ab = bvUtils->unsigned_less_than(Abv, Bbv);
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
      literalt c_ab = bvUtils->unsigned_less_than(Abv, Bbv);
      insertClockEntriesInMap(A, B, c_ab);
      return c_ab;
    }
  }
}

std::pair<literalt,literalt> FMEncoding::getMILiteral(CB A)
{
  Envelope *envA = last_node->GetTransition(A)->GetEnvelope();
  // if(!envA->isCollectiveType())
  return eventMap.find(A)->second;
  // else {
  //   MatchPtr Aptr = getMPtr(A);
  //   assert (Aptr != NULL);
  //   return collEventMap.find(Aptr)->second;
  // }
}

literalt FMEncoding::getMatchLiteral(MatchPtr mptr)
{
  std::string symbol = match2symMap.find(mptr)->second;
  return matchMap.find(symbol)->second;
}

MatchPtr FMEncoding::getMPtr(CB A) 
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

std::string FMEncoding::getClkLitName(literalt lt, CB A, CB B)
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

std::string FMEncoding::getLitName(literalt lt, int type)
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
void FMEncoding::createBVEventLiterals()
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
	Abv[i] = slv->new_variable();
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
	Abv[i] = slv->new_variable();
      }
      collBVMap.insert(std::pair<MatchPtr, bvt > ((*mit),Abv));
      revCollBVMap.insert(std::pair<bvt, MatchPtr>(Abv, (*mit)));
      flag = false;
    }
  }
}

bvt FMEncoding::getEventBV(CB A) 
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

void FMEncoding::insertClockEntriesInMap(CB B, CB A,  literalt c_ba)
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


void FMEncoding::createClkLiterals()
{
  formula << "****PPO****" << std::endl; 
  //slv->constraintStream << "****PPO****" << std::endl; 
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
	
	literalt c_ba = bvUtils->unsigned_less_than(Bbv, Abv);

	insertClockEntriesInMap(B, A, c_ba);

	slv->l_set_to(c_ba, true); // PPO constraint

	formula << getClkLitName(c_ba,B, A) << " & " <<std::endl;
      }
    }
  }
}

void FMEncoding::createRFConstraint()
{
  bool flag = false;
  formula << "****RF****" << std::endl;   
  //slv->constraintStream << "****RF****" << std::endl; 
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
      if(last_node->GetTransition(*lit)->GetEnvelope()->isSendType() ||
	 last_node->GetTransition(*lit)->GetEnvelope()->isRecvType()){
	flag = true; 
	break;
      }
    }
    if(flag){ // hoping it to be a send-receive match
      
      flag = false;
      
      assert((**mit).size() == 2);
      
      CB A = (**mit).front();
      CB B = (**mit).back();
      
      bvt Abv, Bbv;
      
      Abv = getEventBV(A);
      Bbv = getEventBV(B);
      
      //literalt c_ab = getClkLiteral(A, B); 
      literalt e_ab = bvUtils->equal(Abv, Bbv);  // [svs]: clk_a = clk_b
      literalt s_ab = getMatchLiteral(*mit);

      slv->l_set_to(slv->limplies(s_ab, e_ab), true);
      formula << "(" << getLitName(s_ab, 0) << " -> " 
	      << "e_ab" <<  ") & " <<std::endl;
	//getClkLitName(c_ab, A, B) << ") & " <<std::endl;
    }
  }
}

void FMEncoding::createRFSomeConstraint()
{
  bvt rhs; 
  literalt s_m, m_a;
  bool flag = false;
  formula << "****RFSOME****" << std::endl; 
  //slv->constraintStream << "****RFSOME****" << std::endl; 
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
	  slv->l_set_to(slv->limplies(m_a, slv->lor(rhs)) , true);
	  formula << "(" << getLitName(m_a,1) << " -> (";
	  for(bvt::iterator bit = rhs.begin(); bit != rhs.end(); bit++){
	    formula << getLitName(*bit,0) << " | ";  
	  }
	  formula << ")) &" << std::endl;
	  rhs.clear();
	}
	else {
	  assert(false); // m_a has no match -- NOT POSSIBLE!
	}
      }
    }
  }
}

void FMEncoding::createMatchConstraint()
{
  literalt m_a; 
  bvt rhs;
  bool flag = false;
  formula << "****MatchsetEvent****" << std::endl; 
  //slv->constraintStream << "****MatchsetEvent****" << std::endl; 
  forall_matchSet(mit, matchSet){
    if(last_node->GetTransition((**mit).front())->GetEnvelope()->isSendType())
      forall_match(lit, (**mit)){
	m_a = getMILiteral(*lit).first;
	rhs.push_back(m_a);
      }
    if(!rhs.empty()){
      literalt s_m = getMatchLiteral(*mit);
      slv->l_set_to(slv->limplies(s_m, slv->land(rhs)), true);
      formula << "(" << getLitName(s_m, 0) << " -> (";
      for(bvt::iterator bit = rhs.begin(); bit != rhs.end(); bit++){
	formula << getLitName(*bit,1) << " & ";  
      }
      rhs.clear();
      formula << ")) &" << std::endl;
    }
  }
}



void FMEncoding::uniqueMatchSend()
{
  literalt s_m;
  formula << "****UniqueMatchSend****" << std::endl; 
  ////slv->constraintStream << "****UniqueMatchSend****" << std::endl; 
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
	  std::stringstream ss;
	  ss << send._pid << send._index << (*sit)._pid << (*sit)._index;
	  literalt s_n = matchMap.find(ss.str())->second;
	  formula << "(" << getLitName(s_m, 0) << " -> !"
		  << getLitName(s_n, 0) << ") &" <<std::endl;
	  slv->l_set_to(slv->limplies(s_m, slv->lnot(s_n)), true);
	}
      }
    }
  }
}

void FMEncoding::uniqueMatchRecv()
{
  literalt s_m;
  formula << "****UniqueMatchRecv****" << std::endl; 
  //slv->constraintStream << "****UniqueMatchSend****" << std::endl; 
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
	  std::stringstream ss;
	  ss << (*sit)._pid << (*sit)._index << recv._pid << recv._index;
	  literalt s_n = matchMap.find(ss.str())->second;
	  slv->l_set_to(slv->limplies(s_m, slv->lnot(s_n)), true);
	  formula << "(" << getLitName(s_m, 0) << " -> !"
		  << getLitName(s_n, 0) << ") &" << std::endl;
	  slv->l_set_to(slv->limplies(s_m, slv->lnot(s_n)), true);
	}
      }
    }
  }
}


void FMEncoding::noMoreMatchesPossible()
{
  bvt c;
  formula << "****noMoreMatchesPossible****" << std::endl; 
  //slv->constraintStream << "****noMoreMatchesPossible****" << std::endl; 
  forall_matchSet(mit, matchSet){
    formula << "(";
    forall_match(lit, (**mit)){
      std::pair<literalt,literalt> p = getMILiteral(*lit);
      if(last_node->GetTransition(*lit)->GetEnvelope()->isSendType() ||
	 last_node->GetTransition(*lit)->GetEnvelope()->isRecvType()){
	c.push_back(p.first);
	c.push_back(slv->lnot(p.second));
	formula << getLitName(p.first,1) << " | " 
		<< "!" << getLitName(p.first, 3) << " | ";
      }
    }
    if(!c.empty()){
      slv->l_set_to(slv->lor(c), true);
      c.clear();
    }
    formula << ") &" << std::endl;
  }
}



void FMEncoding::alternateAllAncestorsMatched()
{
  bvt rhs;
  formula << "****allAncestorsMatched****" << std::endl;
  //slv->constraintStream << "****allAncestorsMatched****" << std::endl;
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A (envA->id, envA->index);
      std::pair<literalt, literalt> p = getMILiteral(A);
      literalt m_a = p.first;
      literalt i_a = p.second;
      // if(envA->isCollectiveType())
      // 	formula << "(" << getLitName(m_a,4) << " <-> (";
      //      else
      formula  << "(" << getLitName(m_a,3) << " <-> (" ;
      
      std::vector<int> ancs = last_node->GetTransition(A)->get_ancestors();
      for(std::vector<int>::iterator vit = ancs.begin(); 
	  vit != ancs.end(); vit++){
	CB B(envA->id, *vit);
	std::pair<literalt, literalt> q = getMILiteral(B);
	rhs.push_back(q.first);
      }
      if(!rhs.empty()){
	for(bvt::iterator bit = rhs.begin(); bit!=rhs.end(); bit++){
	  formula << getLitName(*bit, 1) << " & "; 
	}
	 formula << ")";  
	slv->l_set_to(slv->land(slv->limplies(slv->land(rhs),i_a), 
			      slv->limplies(i_a, slv->land(rhs))), true);
	
	rhs.clear();
      }
      else {
	slv->l_set_to(slv->land(slv->limplies(one,i_a), 
			      slv->limplies(i_a, one)), true);
      }
      formula << ") & " << std::endl;
    }
  }
}


void FMEncoding::matchImpliesIssued()
{

  formula << "****matchImpliesIssued***" << std::endl;
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = (*titer).GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      if(!envA->isCollectiveType()){
	CB A(envA->id, envA->index);
	literalt m_a = getMILiteral(A).first;
	literalt i_a = getMILiteral(A).second;
	slv->l_set_to(slv->limplies(m_a, i_a), true);
	formula << "(" << getLitName(m_a, 1) << " -> "
		<< getLitName(m_a, 3) << ") &" << std::endl;
      }
    }
  }
  forall_matchSet(mit, matchSet){
    CB A = (**mit).front();
    Envelope *front = 
      last_node->GetTransition(A)->GetEnvelope();
    
    if(front->isCollectiveType()){
      literalt m_match;
      bvt i_evts;
      std::map<CB, std::pair<literalt, literalt> >::iterator
	eit = eventMap.find(A);
      if(eit != eventMap.end()){
	m_match = eit->second.first;
	forall_match(lit, (**mit)){
	  i_evts.push_back(getMILiteral(*lit).second);
	}
	slv->l_set_to(slv->land(slv->limplies(m_match, slv->land(i_evts)), 
			      slv->limplies(slv->land(i_evts), m_match)), true);
      }
      else
	assert(false);
    }
  }

}



void FMEncoding::notAllMatched()
{
  bvt c;
  formula << "****notAllMatched****" << std::endl;
  //slv->constraintStream << "****notAllMatched****" << std::endl;
  formula << "("; 
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A(envA->id, envA->index);
      literalt m_a = getMILiteral(A).first;
      c.push_back(slv->lnot(m_a));
      // if(envA->isCollectiveType())
      // 	formula << "!" << getLitName(m_a,2) << " | ";
      // else
      formula << "!" << getLitName(m_a,1) << " | ";
    }
  }
  formula << ")" << std::endl;
  slv->l_set_to(slv->lor(c), true);
}

void FMEncoding::waitMatch()
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
	  CB B(envA->id, *sit);
  	  Envelope *envB = last_node->GetTransition(B)->GetEnvelope();
  	  if(envB->func_id == FINALIZE) continue;
	  //if(last_node->isAncestor(A,B)){
	  literalt m_b = getMILiteral(B).first;
	  rhs.push_back(m_b);
	}
	if(!rhs.empty()){
	  slv->l_set_to(slv->land(slv->limplies(m_a, slv->land(rhs)),
				slv->limplies(slv->land(rhs), m_a)), true);
	  formula << "(" << getLitName(m_a, 1) << " <-> (";
	  for(bvt::iterator bit = rhs.begin(); bit != rhs.end(); bit++){
	    formula << getLitName(*bit, 1) << " & " ;
	  }
	  formula << ")) &" << std::endl;
	  rhs.clear();
	  }
	else{
	  slv->l_set_to(slv->land(slv->limplies(m_a, one),
				slv->limplies(one, m_a)), true);
	}
      }
    }
  }
}



void FMEncoding::publish()
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
      switch(slv->l_get(m_a).get_value()){ 
      case tvt::TV_TRUE:
	// if(envA->isCollectiveType())
	//   formula << getLitName(m_a, 2) << ":1" << std::endl;
	// else
	formula << getLitName(m_a, 1) << ":1" << std::endl;
	break;
      case tvt::TV_FALSE:
	// if(envA->isCollectiveType())
	//   formula << getLitName(m_a,2) << ":0" << std::endl;
	// else
	formula << getLitName(m_a,1) << ":0" << std::endl;
	break;
      case tvt::TV_UNKNOWN:
	// if(envA->isCollectiveType())
	//   formula << getLitName(m_a,2) << ":UNKNOWN" << std::endl;
	// else
	formula << getLitName(m_a,1) << ":UNKNOWN" << std::endl;
	break;
      default: assert(false);
      }
      switch(slv->l_get(i_a).get_value()){ 
      case tvt::TV_TRUE:
	// if(envA->isCollectiveType())
	//   formula << getLitName(m_a, 4) << ":1" << std::endl;
	// else
	formula << getLitName(m_a, 3) << ":1" << std::endl;
	break;
      case tvt::TV_FALSE:
	// if(envA->isCollectiveType())
	//   formula << getLitName(m_a, 4) << ":0" << std::endl;
	// else
	formula << getLitName(m_a, 3) << ":0" << std::endl;
      	break;
      case tvt::TV_UNKNOWN:
	// if(envA->isCollectiveType())
	//   formula << getLitName(m_a, 4) << ":UNKNOWN" << std::endl;
	// else
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
      // 	    switch(slv->l_get(c_ab).get_value()){ 
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
      switch(slv->l_get(s_ab).get_value()){ 
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

void FMEncoding::generateConstraints()
{
 createMatchSet();
  //  printMatchSet();
  //std::cout << formula.str();
 createEventLiterals();
 set_width();
 createBVEventLiterals();
 createMatchLiterals();
 
 gettimeofday(&constGenStart, NULL);
  
 createClkLiterals(); // partial order constraint + clock difference
 uniqueMatchSend(); // unique match for send constraint
 uniqueMatchRecv(); // unique match for recv constraint
 createRFSomeConstraint(); // Match correct
 createMatchConstraint(); //Matched Only
 noMoreMatchesPossible(); // No more matches possible
 alternateAllAncestorsMatched(); // All ancestors matched  
 notAllMatched();  // not all matched
 matchImpliesIssued(); // match only  issued
 createRFConstraint(); // clock equality
 waitMatch();
 
 gettimeofday(&constGenEnd, NULL);
 getTimeElapsed(constGenStart, constGenEnd);
 
}

void FMEncoding::encodingPartialOrders()
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
  
  std::cout << "********* SAT VALUATIONS ************" << std::endl;
  std::cout << "Number of Clauses: " <<  static_cast<cnf_solvert *>(slv)->no_clauses() << std::endl;
  std::cout << "Number of Variables: " << slv->no_variables() << std::endl;
  std::cout << "Constraint Generation Time: "
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
  
  std::cout << "Solving Time: " << (getTimeElapsed(solverStart, solverEnd)*1.0)/1000000 << "sec \n";
  size_t peakSize = getPeakRSS();
  std::cout << "Mem (MB): " << peakSize/(1024.0*1024.0) << std::endl;
  std::cout << formula.str();
  std::cout << std::endl;
    
}


#if 0

// void FMEncoding::createSerializationConstraint()
// {
//   formula << "****Serialization****" << std::endl; 
//   //slv->constraintStream << "****Serialization****" << std::endl; 
  
//   forall_transitionLists(iter, last_node->_tlist){
//     forall_transitions(titer, (*iter)->_tlist){
//       Envelope * envA = titer->GetEnvelope();
//       if(envA->func_id == FINALIZE) continue;
//       CB A(envA->id, envA->index);
//       forall_transitionLists(iterN, last_node->_tlist){
// 	forall_transitions(titerN, (*iterN)->_tlist){
// 	  Envelope * envB = titerN->GetEnvelope(); 
// 	  if(envB->func_id == FINALIZE) continue;
// 	  CB B(envB->id, envB->index);
// 	  if( A!=B){
// 	    literalt c_ab = getClkLiteral(A,B);
// 	    literalt c_ba = getClkLiteral(B,A); 
// 	    if(c_ab != c_ba)
// 	    slv->l_set_to(slv->lnot(slv->land(c_ab, c_ba)), true);
// 	    formula << "(!(" << getClkLitName(c_ab, A, B) << " & " 
// 		    << getClkLitName(c_ba, B, A) << ")) &" <<std::endl;
// 	  }
// 	}
//       }
//     }
//   }
// }

// void FMEncoding::createFrConstraint()
// {
//   literalt s_m;
//   formula << "****FR****" << std::endl; 
//   //slv->constraintStream << "****FR****" << std::endl; 
//   forall_matchSet(mit, matchSet){
//     CB send = (**mit).front(); // assuming only send-recv matches exist
//     CB recv = (**mit).back();
//     if(last_node->GetTransition(send)->GetEnvelope()->isSendType()) {
//       s_m = getMatchLiteral(*mit);
//       assert((**mit).size() == 2);
    
//       std::set<CB> image = _m->MImage(recv);
//       for(std::set<CB>::iterator sit = image.begin(); 
// 	  sit != image.end(); sit++){
// 	if(send != (*sit)){
// 	  literalt c_send_send = getClkLiteral(send,(*sit));
// 	  literalt c_recv_send = getClkLiteral(recv, (*sit));
// 	  slv->l_set_to(slv->limplies(slv->land(s_m, c_send_send), c_recv_send), true);
// 	  formula << "((" << getLitName(s_m, 0) 
// 		  << " & " << getClkLitName(c_send_send, send, *sit)
// 		  << ") -> " << getClkLitName(c_recv_send, recv, *sit)
// 		  << ") &" <<std::endl;
// 	}
//       }
//     }
//   }
// }
// void FMEncoding::createUniqueMatchConstraint()
// {
//   literalt s_ab, s_ac;
//   bvt rhs;
//   formula << "****UniqueMatchForEvent****" << std::endl; 
//   //slv->constraintStream << "****UniqueMatchForEvent****" << std::endl; 
//   forall_matchSet(mit, matchSet){
//     CB send = (**mit).front();
//     if(last_node->GetTransition(send)->GetEnvelope()->isSendType()) {
//       assert((**mit).size() == 2);
//       CB recv = (**mit).back();
//       s_ab = getMatchLiteral(*mit);
//       formula << "(" << getLitName(s_ab, 0) <<  " -> (";
//       forall_matchSet(mitN, matchSet){
// 	CB sendp = (**mitN).front();
// 	if(last_node->GetTransition(sendp)->GetEnvelope()->isSendType()) {
// 	  CB recvp = (**mitN).back();
// 	  if (send == sendp && recv != recvp) {
// 	    s_ac = getMatchLiteral(*mitN);
// 	    rhs.push_back(slv->lnot(s_ac));
// 	    formula << "!" << getLitName(s_ac, 0) << " & "; 
// 	  }
// 	}
//       }
//       if(!rhs.empty()){
// 	slv->l_set_to (slv->limplies(s_ab, slv->land(rhs)), true);
// 	rhs.clear();
//       }
//       else{
// 	slv->l_set_to (slv->limplies(s_ab, one), true);
//       }
//       formula << ")) &" <<std::endl;
//     }
//   }
// }

// void FMEncoding::alternativeUniqueMatchConstraint()
// {
//   literalt s_m;
//   formula << "****alternativeUniqueMatch****" << std::endl; 
//   //slv->constraintStream << "****alternativeUniqueMatch****" << std::endl; 
//   forall_matchSet(mit, matchSet){
//     CB send = (**mit).front(); // assuming only send-recv matches exist
//     CB recv = (**mit).back();
//     if(last_node->GetTransition(send)->GetEnvelope()->isSendType()) {
//       s_m = getMatchLiteral(*mit);
//       assert((**mit).size() == 2);
    
//       std::set<CB> image = _m->MImage(send);
//      for(std::set<CB>::iterator sit = image.begin(); 
// 	  sit != image.end(); sit++){
// 	if(recv != (*sit)){
// 	  literalt c_recv_recv = getClkLiteral((*sit), recv);
// 	  literalt c_recv_send = getClkLiteral((*sit), send);
// 	  slv->l_set_to(slv->limplies(slv->land(s_m, c_recv_recv), c_recv_send), true);
// 	  formula << "((" << getLitName(s_m, 0) 
// 		  << " & " << getClkLitName(c_recv_recv, *sit, recv)
// 		  << ") -> " << getClkLitName(c_recv_send, *sit, send)
// 		  << ") &" <<std::endl;
// 	}
//       }
//     }
//   }
// }
// void FMEncoding::allFstIssued ()
// {
//   bvt c;
//   formula << "****allFstIssued****" << std::endl;
//   //slv->constraintStream << "****allFstIssued****" << std::endl;
//   formula << "(";
//   bool AhasanAncestor = false;
//   forall_transitionLists(iter, last_node->_tlist){
//     forall_transitions(titer, (*iter)->_tlist){
//       Envelope *envA = titer->GetEnvelope();
//       if(envA->func_id == FINALIZE) continue;
//       CB A(envA->id, envA->index);
//       forall_transitions(titerN, (*iter)->_tlist){
// 	Envelope *envB = titerN->GetEnvelope();
// 	if(envB->func_id == FINALIZE) continue;
// 	CB B(envB->id, envB->index);
// 	if(last_node->isAncestor(A,B) && envB->isBlockingType()) {
// 	  AhasanAncestor = true; 
// 	  break;
// 	}
//       }
//       if(AhasanAncestor){
// 	AhasanAncestor = false;
// 	continue;
//       }
//       else{
// 	literalt i_a = getMILiteral(A).second;
// 	literalt m_a = getMILiteral(A).first;
// 	c.push_back(i_a);
// 	if(envA->isCollectiveType())
// 	  formula << getLitName(m_a,4) << " & ";
// 	else
// 	  formula << getLitName(m_a,3) << " & ";
//       }
//     }
//   }
//   formula << ") & " << std::endl;
//   slv->l_set_to(slv->land(c), true);
// }
// void FMEncoding::transitiveConstraint()
// {
//   formula << "****transitiveConstraint****" << std::endl;
//   //slv->constraintStream << "****transitiveConstraint****" << std::endl;
//   forall_transitionLists(iter, last_node->_tlist){
//     forall_transitions(titer, (*iter)->_tlist){
//       Envelope *envA = titer->GetEnvelope();
//       if(envA->func_id == FINALIZE) continue;
//       CB A (envA->id, envA->index);
//       forall_transitionLists(iterN, last_node->_tlist){
// 	forall_transitions(titerN, (*iterN)->_tlist){
// 	  Envelope *envB = titerN->GetEnvelope();
// 	  if(envB->func_id == FINALIZE) continue;
// 	  CB B (envB->id, envB->index);
// 	  if(A != B){
// 	    literalt c_ab = getClkLiteral(A,B);
// 	    forall_transitionLists(iterM, last_node->_tlist){
// 	      forall_transitions(titerM, (*iterM)->_tlist){
// 		Envelope *envC = titerM->GetEnvelope();
// 		if(envC->func_id == FINALIZE) continue;
// 		CB C (envC->id, envC->index);
// 		if(B != C && C!= A){
// 		  literalt c_bc = getClkLiteral(B,C);
// 		  literalt c_ac = getClkLiteral(A,C);
// 		  slv->l_set_to(slv->limplies(slv->land(c_ab, c_bc), c_ac),true);
// 		  formula << "((" << getClkLitName(c_ab,A, B) 
// 			  << " & " << getClkLitName(c_bc, B,C) 
// 			  << ") -> " << getClkLitName(c_ac, A,C)
// 			  << ") &" << std::endl;
// 		}
// 	      }
// 	    }	
// 	  }
//         }
//       }
//     }
//   }
// }

// void FMEncoding::allAncestorsMatched()
// {
//   bvt rhs;
//   formula << "****allAncestorsMatched****" << std::endl;
//   //slv->constraintStream << "****allAncestorsMatched****" << std::endl;
//   forall_transitionLists(iter, last_node->_tlist){
//     forall_transitions(titer, (*iter)->_tlist){
//       Envelope *envA = titer->GetEnvelope();
//       if(envA->func_id == FINALIZE) continue;
//       CB A (envA->id, envA->index);
//       std::pair<literalt, literalt> p = getMILiteral(A);
//       literalt m_a = p.first;
//       literalt i_a = p.second;
//       if(envA->isCollectiveType())
// 	formula << "(" << getLitName(m_a,4) << " <-> (";
//       else
// 	formula  << "(" << getLitName(m_a,3) << " <-> (" ;
//       forall_transitions(titerN, (*iter)->_tlist){
// 	Envelope *envB = titerN->GetEnvelope();
// 	if(envB->func_id == FINALIZE) continue;
// 	CB B (envB->id, envB->index);
	
// 	if(last_node->isAncestor(A,B) && envB->isBlockingType()){
// 	  //if(last_node->isAncestor(A,B)){ 
// 	  literalt m_b = getMILiteral(B).first; 
// 	  rhs.push_back(m_b);
// 	  //	if(envB->isCollectiveType())
// 	  //formula << getLitName(m_b, 2) << " & ";
// 	  // else
// 	  //  formula << getLitName(m_b, 1) << " & ";
	  
// 	}
//       }
//       if(!rhs.empty()){
// 	for(bvt::iterator bit = rhs.begin(); bit!=rhs.end(); bit++){
// 	  formula << getLitName(*bit, 1) << " & "; 
// 	}
// 	 formula << ")";  
// 	slv->l_set_to(slv->land(slv->limplies(slv->land(rhs),i_a), 
// 			      slv->limplies(i_a, slv->land(rhs))), true);
	
// 	rhs.clear();
//       }
//       else {
// 	slv->l_set_to(slv->land(slv->limplies(one,i_a), 
// 			      slv->limplies(i_a, one)), true);
//       }
//       formula << ") & " << std::endl;
//     }
//   }
// }

// void FMEncoding::totalOrderOnSends()
// {
//   formula << "****totalOrderOnSends***" << std::endl;
//   //slv->constraintStream << "****totalOrderOnSends***" << std::endl;
//   forall_transitionLists(iter, last_node->_tlist){
//     forall_transitions(titer, (*iter)->_tlist){
//       Envelope *envA = titer->GetEnvelope();
//       if(envA->func_id == FINALIZE) continue;
//       CB A (envA->id, envA->index);
//       forall_transitionLists(iterN, last_node->_tlist){
// 	forall_transitions(titerN, (*iterN)->_tlist){
// 	  Envelope *envB = titerN->GetEnvelope();
// 	  if(envB->func_id == FINALIZE) continue;
// 	  CB B (envB->id, envB->index);
// 	  if(envA->isSendType() && envB->isSendType() && A != B){
// 	    literalt m_a = getMILiteral(A).first; 
// 	    literalt m_b = getMILiteral(B).first;
// 	    literalt c_ab = getClkLiteral(A,B);
// 	    literalt c_ba = getClkLiteral(B,A);
// 	    // slv->l_set_to(slv->limplies(slv->land(m_a, m_b), 
// 	    // 			      slv->land(slv->limplies(slv->lnot(c_ab), c_ba), 
// 	    // 				       slv->limplies(c_ba, slv->lnot(c_ab)))), true);
// 	    slv->l_set_to(slv->land(slv->limplies(slv->lnot(c_ab), c_ba), 
// 				  slv->limplies(c_ba, slv->lnot(c_ab))), true); 
// 	    formula << "(!" << getClkLitName(c_ab, A, B) << " <-> "
// 		    << getClkLitName(c_ba, B, A) << ") &" <<std::endl;
// 	  }
// 	}
//       }
//     }
//   }
// }

// void FMEncoding::totalOrderOnRacingSends()
// {
//   formula << "****totalOrderOnRacingSends***" << std::endl;
//   //slv->constraintStream << "****totalOrderOnSends***" << std::endl;
//   forall_transitionLists(iter, last_node->_tlist){
//     forall_transitions(titer, (*iter)->_tlist){
//       Envelope *envA = titer->GetEnvelope();
//       if(envA->func_id == FINALIZE) continue;
//       CB A (envA->id, envA->index);
//       forall_transitionLists(iterN, last_node->_tlist){
// 	forall_transitions(titerN, (*iterN)->_tlist){
// 	  Envelope *envB = titerN->GetEnvelope();
// 	  if(envB->func_id == FINALIZE) continue;
// 	  CB B (envB->id, envB->index);
// 	  if(envA->isSendType() && envB->isSendType() && (A != B) &&  
// 	     (envA->dest == envB->dest)){
// 	    literalt m_a = getMILiteral(A).first; 
// 	    literalt m_b = getMILiteral(B).first;
// 	    literalt c_ab = getClkLiteral(A,B);
// 	    literalt c_ba = getClkLiteral(B,A);
// 	    // slv->l_set_to(slv->limplies(slv->land(m_a, m_b), 
// 	    // 			      slv->land(slv->limplies(slv->lnot(c_ab), c_ba), 
// 	    // 				       slv->limplies(c_ba, slv->lnot(c_ab)))), true);
// 	    slv->l_set_to(slv->land(slv->limplies(slv->lnot(c_ab), c_ba), 
// 				  slv->limplies(c_ba, slv->lnot(c_ab))), true); 
// 	    formula << "(!" << getClkLitName(c_ab, A, B) << " <-> "
// 		    << getClkLitName(c_ba, B, A) << ") &" <<std::endl;
// 	  }
// 	}
//       }
//     }
//   }
// }
// void FMEncoding::nonOverTakingMatch()
// {
//   forall_transitionLists(iter, last_node->_tlist){
//     forall_transitions(titer, (*iter)->_tlist){
//       Envelope *envA = titer->GetEnvelope();
//       if(envA->func_id == FINALIZE) continue;
//       CB A(envA->id, envA->index);
//       if((envA->func_id == ISEND || envA->func_id == SEND) 
// 	 || envA->func_id == IRECV){
// 	std::vector<int> ancs = titer->get_ancestors();      
// 	for(std::vector<int>::iterator sit = ancs.begin(); 
// 	    sit != ancs.end(); sit++){
// 	  CB B(A._pid, *sit);
// 	  Envelope *envB = last_node->GetTransition(B)->GetEnvelope();
// 	  if(envA->func_id == envB->func_id) {
// 	    if((envA->isSendType() && (envA->src == envB->src)) ||
// 	       (envA->isRecvType() && (envA->src == envB->src))){
// 	      std::pair<literalt,literalt> p = getMILiteral(A);
// 	      std::pair<literalt,literalt> q = getMILiteral(B);
// 	      slv->l_set_to(slv->limplies(p.first, q.first), true);
// 	      formula <<  "(" << getLitName(p.first, 1) << " -> " 
// 		      << getLitName(q.first, 1) << ") &";
// 	    }
// 	  }
// 	} 
//       }
//     }
//   }
// }
// void FMEncoding::makingMatchesHappenSooner()
// {
//   literalt s_m;
//   bvt lst;
//   formula << "****MatchesHappenSooner****" << std::endl; 
//   forall_matchSet(mit, matchSet){
//     CB send = (**mit).front(); // assuming only send-recv matches exist
//     CB recv = (**mit).back();
//     if(last_node->GetTransition(send)->GetEnvelope()->isSendType()) {
//       s_m = getMatchLiteral(*mit);
//       std::vector<int> Sancs = last_node->GetTransition(send)->get_ancestors();
//       std::vector<int> Rancs = last_node->GetTransition(recv)->get_ancestors();
//       bvt Sbv;
//       Sbv = getEventBV(send);
//       bvt onebv = bvUtils.build_constant(1,width);
//       bvt lst; 
//       if (Sancs.empty() && Rancs.empty()){
//   	slv->l_set_to(slv->limplies(s_m, bvUtils.is_zero(Sbv)) ,true);
//       }
//       else{
// 	if(!Sancs.empty()){
// 	  for(std::vector<int>::iterator vit = Sancs.begin();
// 	      vit != Sancs.end(); vit ++){
// 	    CB c(send._pid, (*vit)); 
// 	    bvt Cbv = getEventBV(c);
// 	    literalt l = bvUtils.equal(bvUtils.sub(Sbv, Cbv), onebv);
// 	    lst.push_back(l);
// 	  }
// 	}
// 	if(!Rancs.empty()){
// 	  for(std::vector<int>::iterator vit = Rancs.begin();
// 	      vit != Rancs.end(); vit ++){
// 	    CB c(recv._pid, (*vit)); 
// 	    bvt Cbv = getEventBV(c);
// 	    literalt l = bvUtils.equal(bvUtils.sub(Sbv, Cbv), onebv);
// 	    lst.push_back(l);
// 	  }
// 	}
// 	slv->l_set_to(slv->limplies(s_m, slv->lor(lst)), true);
//       }
//     }  
//   }
// }
#endif
