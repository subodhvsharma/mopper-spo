#include "OptEncoding.hpp"
#include <fstream> 
#include "stdlib.h" 
#include "solver-src/sat/cardinality.h"

////////////////////////////////////////////////////////////
/////                                                ///////
////        OptEncoding                               ///////
////////////////////////////////////////////////////////////

void OptEncoding::set_width()
{
  width = address_bits();
}

unsigned OptEncoding::get_width(){
  return width;
}

unsigned OptEncoding::address_bits()
{
  unsigned res, x=2;
  //TODO change x*=2 to x<<1?
  for(res=1; x<eventSize; res+=1, x*=2);
  return res;
}

void OptEncoding::isLitCreatedForCollEvent(CB A, literalt & m_e)
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

// for MultiRecvs, this function creates 
// m_e and i_e variables only for the bottom 
// event of the multireceives
void OptEncoding::createEventLiterals ()
{
  formula <<" createEventLiterals- m_a, i_a" <<std::endl;
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      literalt m_e, i_e;
      Envelope *env = (*titer).GetEnvelope();
      CB A (env->id, env->index); 
      if(env->func_id == FINALIZE) continue;

      if(env->isMultiRecv && !env->isbottom) continue;
      
      if(env->isCollectiveType()){
	isLitCreatedForCollEvent(A, m_e);
      }
      else{ // belonging to R_Bar U R where 
	// the blocking wildcard is a bottom
	m_e = slv->new_variable();
	
      }
      
      i_e = slv->new_variable();


      //insert in to the map
      eventMap.insert(std::pair<CB, std::pair<literalt, literalt> > 
		      (A,std::pair<literalt, literalt> (m_e, i_e)));
      revEventMap.insert(std::pair<literalt, CB>(m_e, A));
      
      //debug print 
      formula << A << ": m:=" <<m_e.get() << ",\t" << "i:=" << i_e.get() <<std::endl; 
      eventSize++;
    }
  }
}


void OptEncoding::printEventMap()
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

/*
  S_ab when b is not a multirecv OR
  S_ac when b is a multirecv and (a,b) \in M^+, where c is bottom
 */
void OptEncoding::createMatchLiterals()
{
  formula << "createMatchLiterals -- S_ab" <<std::endl;
  std::stringstream uniquepair;
  std::string matchNumeral;
  bool flag = false;
  
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
      Envelope *env = last_node->GetTransition(*lit)->GetEnvelope();
      // match literals only for send and receive
      if(env->isSendType() || env->isRecvType()){
	// skip to the next match
	if(env->isMultiRecv){
	  flag = true;
	  break;
	}
	uniquepair << (*lit)._pid;
	uniquepair << (*lit)._index;
      }
    }
    // if match has a recv that is a part of Multirecv
    // then skip to the next match
    if(flag){ 
      flag = false;
      uniquepair.str("");
      uniquepair.clear();
      continue;
    }
    // else continue with the match and create S_ab
    matchNumeral = uniquepair.str();
    if(matchNumeral.size()){
      literalt s_m = slv->new_variable();
      //debug print
      formula << "s_" << matchNumeral << " = " << s_m.get()<< std::endl;

      matchMap.insert(std::pair<std::string, literalt> (matchNumeral, s_m));
      revMatchMap.insert(std::pair<literalt, std::string> (s_m, matchNumeral));
      match2symMap.insert(std::pair<MatchPtr, std::string> (*mit, matchNumeral));
      // clear out uniquepair
      uniquepair.str("");
      uniquepair.clear();
    }
  }

  // create S_ab when b is a MultiRecv
  std::list<std::pair<CB, CB> >::iterator mrit; 
  // for each multiRecv set
  for (mrit = multiRs.receives.begin(); 
       mrit != multiRs.receives.end(); mrit ++){
    std::set <CB> multiRecvImg; 
    // for each recv in the multiRecv
    for (int i = (*mrit).first._index; 
	 i <= (*mrit).second._index; i++){
      CB t ((*mrit).first._pid, i);
      // get the matchSet Image of recv
      std::set<CB> tempImg = _m->MImage(t);
      // insert it to the combined set 
      multiRecvImg.insert(tempImg.begin(), tempImg.end());
    }
    
    CB bottom = (*mrit).second;
    std::set<literalt> temp;
    for (std::set<CB>::iterator sit = multiRecvImg.begin();
	 sit != multiRecvImg.end(); sit ++){
      std::pair<CB, CB> multirecv_match = std::pair<CB, CB>(*sit, bottom);
      // add to the set of overapprox matches
      _m->Update(multirecv_match);
      // get the pointer of the match and add it to the matchSet
      _MIterator _mit = _m->IsPresent(multirecv_match);
      assert (_mit != _m->_MSet.end());
      matchSet.insert(&((*_mit).second));

      literalt s_m = slv->new_variable();
      uniquepair<<(*sit)._pid;
      uniquepair<<(*sit)._index;
      uniquepair<<bottom._pid;
      uniquepair<<bottom._index;

      matchNumeral = uniquepair.str();
      
      //debug print
      formula << "s_" << matchNumeral << " = " << s_m.get()<< std::endl;
      
      matchMap_MultiRecv.insert(std::pair<std::string, literalt> (matchNumeral, s_m));
      revMatchMap_MultiRecv.insert(std::pair<literalt, std::string> (s_m, matchNumeral));
      temp.insert(s_m);
       
      // clear out uniquepair
      uniquepair.str("");
      uniquepair.clear();
    }
    match2symMap_MultiRecv.insert(std::pair<CB, std::set<literalt> > (bottom, temp));
  }
}

literalt OptEncoding::getClkLiteral(CB A, CB B)
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

std::pair<literalt,literalt> OptEncoding::getMILiteral(CB A)
{
  Envelope *envA = last_node->GetTransition(A)->GetEnvelope();
  // if(!envA->isCollectiveType())
  return eventMap.find(A)->second;
}

literalt OptEncoding::getMatchLiteral(MatchPtr mptr)
{
  CB send = (*mptr).front(); 
  CB recv = (*mptr).back();
  Envelope *envR = last_node->GetTransition(recv)->GetEnvelope();
  
  if (!envR->isMultiRecv){
    std::string symbol = match2symMap.find(mptr)->second;
    return matchMap.find(symbol)->second;
  }
  else {
    assert (envR->isMultiRecv && envR->isbottom);

    std::stringstream uniquepair;
    std::string matchNumeral;

    uniquepair<<send._pid;
    uniquepair<<send._index;
    uniquepair<<recv._pid;
    uniquepair<<recv._index;
    matchNumeral = uniquepair.str(); 

    return matchMap_MultiRecv.find(matchNumeral)->second;
  }
}


MatchPtr OptEncoding::getMPtr(CB A) 
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

std::string OptEncoding::getClkLitName(literalt lt, CB A, CB B)
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

std::string OptEncoding::getLitName(literalt lt, int type)
{
  
  std::stringstream ss;
  switch(type){
  case 0:{
    if(revMatchMap.find(lt) != revMatchMap.end())
      ss << "S_" << revMatchMap.find(lt)->second;
    else if(revMatchMap_MultiRecv.find(lt)!= revMatchMap_MultiRecv.end())
      ss << "S_" << revMatchMap_MultiRecv.find(lt)->second;
    else
      assert(false);
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
void OptEncoding::createBVEventLiterals()
{
  
  formula << "createBVEventLiterals - BV_a" << std::endl;
  
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      if((*titer).GetEnvelope()->func_id == FINALIZE) continue;
      if((*titer).GetEnvelope()->isCollectiveType()) continue;
      
      Envelope *env = (*titer).GetEnvelope();
      if (env->isMultiRecv){
	if(!(env->istop || env->isbottom)) continue;
      }
      CB A (env->id, env->index); 
      bvt Abv; 
      Abv.resize(width);
      
      formula << A << ":BV["; 
      for(unsigned i=0; i < width; i++){
	Abv[i] = slv->new_variable();
	formula << Abv[i].get() << ", ";
      }
      formula << std::endl;
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

bvt OptEncoding::getEventBV(CB A) 
{
  Envelope *envA = last_node->GetTransition(A)->GetEnvelope(); 

  if(!envA->isCollectiveType()){
    //assert(!envA->isMultiRecv || envA->isbottom);
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

void OptEncoding::insertClockEntriesInMap(CB B, CB A,  literalt c_ba)
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

/* 
   Checks for each  blocking R(*) -- an uninterrupted sequence
   of blocking R(*) events and puts them in a multireceive entry.
 */
void OptEncoding:: discoverMultiReceives()
{
 
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(siter, (*iter)->_tlist){
      Envelope *env = (*siter).GetEnvelope();
      CB top(env->id, env->index);
      bool blk_wldcrd_recv = (env->isRecvType() && 
			      env->isBlockingType() && 
			      (env->src == WILDCARD));
      if(!blk_wldcrd_recv)
	continue;
      //      else if (multiRs.isPresent(top)) continue;
      else if (multiRs.isPresent(top)) continue;
      else {
	CB bottom (-1, -1);
	for (TIter eiter = siter+1;
	     eiter != (*iter)->_tlist.end(); 
	     eiter++){
	  Envelope *envN = (*eiter).GetEnvelope();
	  CB n (envN->id, envN->index);
	  if((envN->isRecvType() && envN->isBlockingType() && 
	      (envN->src == WILDCARD))){
	    bottom = n;
	    envN->isMultiRecv = true;
	    envN->corresponding_top_index = top._index;
	  }
	  else 
	    break;
  	}
	if(bottom._pid != -1) // check if bottom is not NULL
	  multiRs.receives.push_back(std::pair<CB, CB>(top, bottom));
      }
    }
  }
  // now update the relevant vars in the envelope of top,bottom receives:
  std::list<std::pair<CB, CB> >::iterator mrit; 
  for (mrit = multiRs.receives.begin(); mrit != multiRs.receives.end(); mrit ++){
    CB top = (*mrit).first;
    CB bottom = (*mrit).second;
    Envelope * envTop = last_node->GetTransition(top)->GetEnvelope();
    Envelope * envBottom = last_node->GetTransition(bottom)->GetEnvelope();
    envTop->istop = true;
    envTop->isMultiRecv = true;
    envBottom->isbottom = true;
    // envBottom->corresponding_top_index = top._index;
    envTop->corresponding_bottom_index = bottom._index;
    envBottom->corresponding_top_id = top._pid;
    envBottom->cardinality = bottom._index - top._index + 1;
  }
  //debug print 
  //  std::cout << multiRs.print() << std::endl;
}

// partial order constraint + clock difference  
// 12, 21
void OptEncoding::createClkLiterals()
{
  formula << "****createClkLiterals****" << std::endl; 
  //  slv->constraintStream << "****createClkLiterals****" << std::endl; 
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      
      Envelope * envB = (*titer).GetEnvelope();
      
      if(envB->func_id == FINALIZE) continue;
      
      CB B(envB->id, envB->index);
      

      if(!envB->isMultiRecv || envB->isbottom) {
	CB t;
	Transition *transTop;
	if(envB->isbottom){
	  t = CB (envB->id, envB->corresponding_top_index);
	  transTop = last_node->GetTransition(t);
	}
	else{
	  transTop = &(*titer);
	}
	std::vector<int> & ancsLst ((*transTop).get_ancestors());
	
	for(std::vector<int>::iterator vit = ancsLst.begin();
	    vit != ancsLst.end(); vit ++){
	  
	  CB A (envB->id, *vit);
	  Envelope * envA = last_node->GetTransition(A)->GetEnvelope();
	  
	  if (envA->isMultiRecv) assert(envA->isbottom);
	  
	  bvt Abv, Bbv;
	  
	  Abv = getEventBV(A);
	  Bbv = getEventBV(B);
	  
	  literalt c_ab = bvUtils->unsigned_less_than(Abv, Bbv);
	  
	  insertClockEntriesInMap(A, B, c_ab);
	  
	  slv->l_set_to(c_ab, true); 
	  
	  //debug print 
	  formula << getClkLitName(c_ab,A, B) << " & " <<std::endl;
	  // slv->constraintStream << c_ab.get() <<":=";
	  // slv->constraintStream << "BV_"<<A <<"[";
	  // forall_literals(it, Abv)
	  //   slv->constraintStream << (*it).get()<< ", ";
	  // slv->constraintStream << "] < " <<"BV_" <<B<<"[";
	  // forall_literals(it, Bbv)
	  //   slv->constraintStream << (*it).get()<< ", ";
	  // slv->constraintStream << "]" <<std::endl;

	}
      }
    }
  }
  
  // forall_transitionLists(iter, last_node->_tlist){
  //   forall_transitions(titer, (*iter)->_tlist){
      
  //     Envelope * envA = (*titer).GetEnvelope();
      
  //     if(envA->func_id == FINALIZE) continue;
      
  //     if(envA->isbottom) // && envA->index!=envA->corresponding_top_index)
  //     {
  //       CB A(envA->id, envA->index);
  // 	assert(envA->corresponding_top_id != -1); 
  // 	assert(envA->corresponding_top_index != -1); 
  //       CB B(envA->id, envA->corresponding_top_index);

  // 	bvt Abv, Bbv;
  // 	Abv = getEventBV(A);
  // 	Bbv = getEventBV(B);
	
  // 	literalt c_ba;
  // 	// if (A != B) { 
  // 	//   c_ba = bvUtils->unsigned_less_than(Bbv, Abv);
  // 	// }
  // 	// else { //[svs]: for singleton blocking wildcards top = bottom
  // 	//   c_ba = bvUtils->equal(Bbv, Abv); 
  // 	// }
	
  // 	c_ba = bvUtils->lt_or_le(true, Bbv, Abv, bv_utilst::UNSIGNED);
  // 	insertClockEntriesInMap(B, A, c_ba);
  // 	slv->l_set_to(c_ba, true);
  // 	formula << getClkLitName(c_ba,B, A) << " & " <<std::endl;
  //     }
  //   }
  // }
}

// CONSTRAINT: 19 clock equality; S_ab => clk_a = clk_b
void OptEncoding::createRFConstraint()
{
  bool flag = false;
  formula << "****createRFConstraint****" << std::endl;   
  //  slv->constraintStream << "****createRFConstraint****" << std::endl; 
  forall_matchSet(mit, matchSet){
    forall_match(lit, (**mit)){
      if(last_node->GetTransition(*lit)->GetEnvelope()->isSendType() ||
	 last_node->GetTransition(*lit)->GetEnvelope()->isRecvType()){
	flag = true; 
	break;
      }
    }
    if(flag){ // hoping it to be a send-receive match

      CB A = (**mit).front();
      CB B = (**mit).back();

      Envelope * envR = last_node->GetTransition(B)->GetEnvelope();
 
      if (envR->isMultiRecv && !envR->isbottom) {
	flag = false;
	continue;
      }
      bvt Abv;
      Abv = getEventBV(A);
      literalt s_ab = getMatchLiteral(*mit);

      if (envR->isbottom){ 
	
	assert (envR->corresponding_top_index != -1); 
	CB B_top(envR->corresponding_top_id, envR->corresponding_top_index);
	CB B_bot(envR->id, envR->index);
      
	bvt Bbv_bot, Bbv_top;
      
	Bbv_bot = getEventBV(B_bot);
	Bbv_top = getEventBV(B_top);
      
	literalt e_abtop = bvUtils->lt_or_le(true,Bbv_top,Abv,bvUtils->UNSIGNED);
	//  unsigned_less_than(Bbv_top, Abv);  // [svs]: clk_a = clk_b
	literalt e_abbot = bvUtils->lt_or_le(true,Abv,Bbv_bot,bvUtils->UNSIGNED);
	// unsigned_less_than(Abv, Bbv_bot);  // [svs]: clk_a = clk_b
	
	//DEBUG PRINT
	slv->l_set_to(slv->limplies(s_ab, e_abtop), true);
	slv->l_set_to(slv->limplies(s_ab, e_abbot), true);
	formula << "(" << getLitName(s_ab, 0) << " -> " 
	   	<< A << "between (" 
		<< B_top <<  "," <<  B_bot << ") & " <<std::endl;

      }
      else {
	bvt Bbv = getEventBV(B);
	literalt e_ab = bvUtils->equal(Abv, Bbv);  // [svs]: clk_a = clk_b
	
	slv->l_set_to(slv->limplies(s_ab, e_ab), true);
	formula << "(" << getLitName(s_ab, 0) << " -> " 
		<< A << " = " << B <<  ") & " <<std::endl;
      }
    }
  }
}

//function: For a given CB, it identifies all the 
//          images from M+ and obtain the relevant 
//          match-pairs
void OptEncoding::construct_multirecv_match(bvt & rhs, Envelope * env)
{
  CB A(env->id, env->index);
  assert(env->isMultiRecv && env->isbottom);
  
  std::map<CB, std::set<literalt> >::iterator it = match2symMap_MultiRecv.find(A);
  if( it != match2symMap_MultiRecv.end()){
    rhs.assign(it->second.begin(), it->second.end());
    assert(rhs.size() == it->second.size());
  }
  else assert(false);
  
}

void OptEncoding::construct_nonmultirecv_match(bvt & rhs, Envelope *envA)
{
  literalt s_m;
  bool flag = false;

  CB A(envA->id, envA->index);
  assert(!envA->isMultiRecv);

  forall_matchSet(mit, matchSet){
    Envelope *envB = last_node->GetTransition((**mit).back())->GetEnvelope();
    forall_match(lit, (**mit)){
      if((*lit) == A) {
	if(envA->isSendType()){
	  // skip if Recv match for Send is a multirecv
	  if(envB->isMultiRecv)
	    continue;
	}
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
  
  if(envA->isSendType()){
    // when send's match is a multirecv
    std::list<std::pair<CB, CB> >::iterator mrit; 
    // for each multiRecv set
    for (mrit = multiRs.receives.begin(); 
	 mrit != multiRs.receives.end(); mrit ++){
      CB bottom = (*mrit).second;
      
      std::stringstream uniquepair;
      std::string matchNumeral;
      
      uniquepair << A._pid; 
      uniquepair << A._index;
      uniquepair << bottom._pid; 
      uniquepair << bottom._index;
      
      matchNumeral = uniquepair.str();
      if(matchMap_MultiRecv.find(matchNumeral) != matchMap_MultiRecv.end()){
	s_m = matchMap_MultiRecv.find(matchNumeral)->second; 
	rhs.push_back(s_m); 
      }
    }
  }
}

// Match correct: m_a <-> exactly(card(a), U s_ab/ba)
// Match count: atmost(card(a), U s_ba)
// 13,14
void OptEncoding::createRFSomeConstraint()
{
  bvt rhs; 
  literalt s_m, m_a;
  bool flag = false;
  bool bottomFlag = false;
  formula << "****RFSOME****" << std::endl; 
  //slv->constraintStream << "****RFSOME****" << std::endl; 
 
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
    
      Envelope * envA = titer->GetEnvelope();
      CB A(envA->id, envA->index);            
      int cardinality;

      if(envA->isRecvType() || envA->isSendType()) {
	// Skip if multirecv and not bottom
	if(envA->isMultiRecv && !envA->isbottom) continue; 
	else {// either not multiRecv or multiRecv that is bottom
	  m_a = getMILiteral(A).first;
	  if(envA->isbottom) { // if bottom
	    cardinality = envA->cardinality;  
	    // get the s_m from all the matches for bottom
	    construct_multirecv_match(rhs, envA);
	  }
	  else {// either a Send or Recv which is not a multirecv
	    cardinality = 1;
	    construct_nonmultirecv_match(rhs, envA);
	  }
	  if(!rhs.empty()){

	    formulat fo_atmost; 
	    totalizer_encodingt se(*slv);
	    se.atmostk(rhs, cardinality, fo_atmost);
	    se.add_to_prop(fo_atmost);
	    //literalt card_lit_atmost = se.get_lit_for_formula(fo_atmost);
	    
	    
	    formulat fo_exactly;
	    se.exactlyk(rhs, cardinality, fo_exactly);
	    //se.add_to_prop(fo_exactly);
	    literalt card_lit_exactly = se.get_lit_for_formula(fo_exactly);


	     slv->l_set_to(slv->limplies(m_a, card_lit_exactly) , true);
	     slv->l_set_to(slv->limplies(card_lit_exactly, m_a) , true);
	     maCardMap[m_a]=card_lit_exactly;
	     maInputMap[m_a]=std::pair<bvt,unsigned>(rhs,cardinality);
	    
	    //DEBUG PRINT
	    formula << "(m_" <<A <<"<->" 
		    << "(" << cardinality <<", {";
	    // if (cardinality == 1){
	    //   forall_literals(it, rhs){
	    // 	formula << getLitName(*it, 0) << ",";
	    //   }
	    // }
	    //else{
	    forall_literals(it, rhs){
	      formula << getLitName(*it, 0) << ",";
	    }
	      //}
	    formula << "}) &" << std::endl;
	    rhs.clear();
	  }
	  else {
	    assert(false); // m_a has no match -- NOT POSSIBLE!
	  }
	}
      }
    }
  }
}

// Constraint: S_ab => r_a /\ r_b
// Matched => constituents ready
void OptEncoding::createMatchReadyConstraint()
{
  literalt r_a; 
  bvt rhs;
  bool flag = false;
  formula << "****MatchReadyEvent****" << std::endl; 
  //slv->constraintStream << "****MatchsetEvent****" << std::endl; 
  forall_matchSet(mit, matchSet){
    Envelope *envS = last_node->GetTransition((**mit).front())->GetEnvelope();
    Envelope *envR = last_node->GetTransition((**mit).back())->GetEnvelope();
    if(envS->isSendType()){
      if(envR->isMultiRecv && !envR->isbottom) continue;
      
      literalt s_m = getMatchLiteral(*mit);
      
      formula << "(";
      formula << getLitName(s_m, 0) ;
      formula << " -> (";

      forall_match(lit, (**mit)){
	r_a = getMILiteral(*lit).second;
	rhs.push_back(r_a);
	formula << getLitName(getMILiteral(*lit).first, 3) << " & ";
      }
      
      if(!rhs.empty()){
	formula << ")) &" << std::endl;
	slv->l_set_to(slv->limplies(s_m, slv->land(rhs)), true);
	rhs.clear();
	
      }
    }
    else continue; 
  }
}

// Constraint: S_ab => m_a /\ m_b
// Matched Only
void OptEncoding::createMatchConstraint()
{
  literalt m_a; 
  bvt rhs;
  bool flag = false;
  formula << "****MatchsetEvent****" << std::endl; 
  //slv->constraintStream << "****MatchsetEvent****" << std::endl; 
  forall_matchSet(mit, matchSet){
    Envelope *envS = last_node->GetTransition((**mit).front())->GetEnvelope();
    Envelope *envR = last_node->GetTransition((**mit).back())->GetEnvelope();
    if(envS->isSendType()){
      if(envR->isMultiRecv && !envR->isbottom) continue;
      forall_match(lit, (**mit)){
	m_a = getMILiteral(*lit).first;
	rhs.push_back(m_a);
      }
    }
    else continue;
    
    if(!rhs.empty()){
      literalt s_m = getMatchLiteral(*mit);
      slv->l_set_to(slv->limplies(s_m, slv->land(rhs)), true);
      //formula << "(" << getLitName(s_m, 0) << " -> (";
      //for(bvt::iterator bit = rhs.begin(); bit != rhs.end(); bit++){
	//formula << getLitName(*bit,1) << " & ";  
      //}
      rhs.clear();
      //formula << ")) &" << std::endl;
    }
  }
}


//Constraint:  unique match for send constraint
void OptEncoding::uniqueMatchSend()
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


//Constraint: unique match for recv constraint
void OptEncoding::uniqueMatchRecv()
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

// Constraint: \/_{match(a,b)} (m_a \/ ~r_a)
// 15
void OptEncoding::noMoreMatchesPossible()
{
  bvt c;
  bool flag = false;
  formula << "****noMoreMatchesPossible****" << std::endl; 
  //slv->constraintStream << "****noMoreMatchesPossible****" << std::endl; 
  forall_matchSet(mit, matchSet){
    formula << "(";
    forall_match(lit, (**mit)){
      Envelope * envA = last_node->GetTransition(*lit)->GetEnvelope();
      Envelope * envB = last_node->GetTransition((**mit).back())->GetEnvelope();
      if(envA->isSendType() ||envA->isRecvType()){
	if(envA->isMultiRecv && !envA->isbottom) {
	  flag =true; break;
	}
	if(envA->isSendType() && envB->isMultiRecv && !envB->isbottom){
	  flag =true; break;
	}
	std::pair<literalt,literalt> p = getMILiteral(*lit);
	c.push_back(p.first);
	c.push_back(slv->lnot(p.second));
	formula << getLitName(p.first,1) << " | " 
		<< "!" << getLitName(p.first, 3) << " | ";
      }
    }
    if(flag){
      flag = false; continue;
    }
    if(!c.empty()){
      slv->l_set_to(slv->lor(c), true);
      c.clear();
    }
    formula << ") &" << std::endl;
  }
}


// Constraint: r_b <=> /\_{a \in Imm'(b)} m_a
// 16
void OptEncoding::alternateAllAncestorsMatched()
{
  bvt rhs;
  formula << "****allAncestorsMatched****" << std::endl;
  //slv->constraintStream << "****allAncestorsMatched****" << std::endl;
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A (envA->id, envA->index);
      if(envA->isMultiRecv && !envA->isbottom) continue;
      std::pair<literalt, literalt> p = getMILiteral(A);
      literalt m_a = p.first;
      literalt i_a = p.second;
      // if(envA->isCollectiveType())
      // 	formula << "(" << getLitName(m_a,4) << " <-> (";
      //      else
      formula  << "(" << getLitName(m_a,3) << " <-> (" ;
      //[svs]: is bottom then go to top of multiRecv; 
      //then obtain the ancestors of top
      if (envA->isbottom) {
	//formula << "viatop ";
	A._pid = envA->corresponding_top_id;
	A._index = envA->corresponding_top_index;
	envA = last_node->GetTransition(A)->GetEnvelope();
      }
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
	formula << "1 )";
      }
      formula << ") & " << std::endl;
    }
  }
}


//CONSTRAINT: /\_{a \in C} m_a => r_a
// 18
void OptEncoding::matchImpliesIssued()
{

  formula << "****matchImpliesIssued***" << std::endl;
  //  forall_matchSet(mit, matchSet){
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      
      Envelope * envA = titer->GetEnvelope();
      CB A  (envA->id, envA->index);
      // CB A = (**mit).front();
      // CB B = (**mit).back();
      // Envelope * envA = last_node->GetTransition(A)->GetEnvelope();
      // Envelope * envB = last_node->GetTransition(B)->GetEnvelope();
      
      if(envA->isCollectiveType() || envA->func_id == FINALIZE)
	continue;
      
      if(envA->isMultiRecv && !envA->isbottom) continue;
      
      // if(envB->isbottom){
      
      // literalt s_ab = getMatchLiteral(*mit);    
      // }
      literalt m_a = getMILiteral(A).first;      
      literalt i_a = getMILiteral(A).second;
            
      // slv->l_set_to(slv->limplies(s_ab, i_a), true);
      // slv->l_set_to(slv->limplies(s_ab, i_b), true);
      //formula << getLitName(s_ab, 0) << " -> " << getLitName(i_a, 3) << " &" << std::endl;
      formula << getLitName(m_a, 1) << " -> " << getLitName(m_a, 3) << " &" << std::endl;
      
      slv->l_set_to(slv->limplies(m_a, i_a),true);
    }
  }

  // for collectives
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


// CONSTRAINT: \/_{a \in C} ~m_a
// 17
void OptEncoding::notAllMatched()
{
  bvt c;
  formula << "****notAllMatched****" << std::endl;
  //slv->constraintStream << "****notAllMatched****" << std::endl;
  formula << "("; 
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      CB A(envA->id, envA->index);

      if(envA->func_id == FINALIZE) continue;

      if(envA->isMultiRecv && !envA->isbottom) continue;

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

void OptEncoding::waitMatch()
{
  formula << "****waitMatch****" << std::endl;
  bvt rhs;
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = titer->GetEnvelope();
      if(envA->func_id == FINALIZE) continue;
      CB A(envA->id, envA->index);
      if(envA->func_id == WAIT || envA->func_id == WAITALL) {
	literalt m_a = getMILiteral(A).first;
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
	  // formula << "(" << getLitName(m_a, 1) << " <-> (";
	  // for(bvt::iterator bit = rhs.begin(); bit != rhs.end(); bit++){
	  //   formula << getLitName(*bit, 1) << " & " ;
	  // }
	  // formula << ")) &" << std::endl;
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

void OptEncoding::publish()
{
  tvt result;
  literalt x_ap;
  bool flag = false;
  
  forall_transitionLists(iter, last_node->_tlist){
    forall_transitions(titer, (*iter)->_tlist){
      Envelope *envA = (*titer).GetEnvelope();
      CB A(envA->id, envA->index);
      if(envA->func_id == FINALIZE) continue;
      
      if(envA->isMultiRecv && !envA->isbottom) continue;
      

      literalt m_a = getMILiteral(A).first;
      literalt i_a = getMILiteral(A).second;
      switch(slv->l_get(m_a).get_value()){ 
      case tvt::TV_TRUE:
	// if(envA->isCollectiveType())
	//   formula << getLitName(m_a, 2) << ":1" << std::endl;
	// else
	formula << getLitName(m_a, 1) << ":1" << std::endl;
	assert(slv->l_get(m_a)==slv->l_get(maCardMap[m_a]));
	{
	unsigned set_inputs=0;
	for(bvt::iterator in_it=maInputMap[m_a].first.begin();
			 in_it!=maInputMap[m_a].first.end();in_it++)
	{
		if(slv->l_get(*in_it).is_true()) set_inputs++;
	}
	assert(maInputMap[m_a].second==set_inputs);
	}
	break;
      case tvt::TV_FALSE:
	// if(envA->isCollectiveType())
	//   formula << getLitName(m_a,2) << ":0" << std::endl;
	// else
	formula << getLitName(m_a,1) << ":0" << std::endl;
	assert(slv->l_get(m_a)==slv->l_get(maCardMap[m_a]));
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
    CB B = (**mit).back();
    
    Envelope* recv = last_node->GetTransition(B)->GetEnvelope();
    if(recv->isMultiRecv && !recv->isbottom) continue;

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

void OptEncoding::generateConstraints()
{
  

  discoverMultiReceives();
  createMatchSet();
  //  printMatchSet();
  //std::cout << formula.str();
  createEventLiterals();
  set_width();
  createBVEventLiterals();
  createMatchLiterals();
  
  gettimeofday(&constGenStart, NULL);
  
  createClkLiterals(); // partial order constraint + clock difference
// VOJTA: three below are removed, I think it's not needed if we have 2 implications for Match correct)
//  uniqueMatchSend(); // unique match for send constraint
//  uniqueMatchRecv(); // unique match for recv constraint
  createRFSomeConstraint(); // Match correct
  //  createMatchConstraint(); //Matched Only
  noMoreMatchesPossible(); // No more matches possible
  alternateAllAncestorsMatched(); // All ancestors matched  
  notAllMatched();  // not all matched
  matchImpliesIssued(); // match only  issued
  createRFConstraint(); // clock equality
  createMatchReadyConstraint();
  waitMatch();
  
  gettimeofday(&constGenEnd, NULL);
  getTimeElapsed(constGenStart, constGenEnd);
 
}

void OptEncoding::encodingPartialOrders()
{

  generateConstraints();
#if 1    
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
#endif
}


