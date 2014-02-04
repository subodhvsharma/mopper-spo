#include "Wu.hpp"
#include "utility.hpp"

extern bool is_eql(std::pair<CB, CB> p1, std::pair<CB, CB> p2);

//extern static int redrule1cnt;
//extern static int redrule2cnt;

W::W() {

}

std::ostream & operator<<(std::ostream &os, const W &c)
{
  
// std::vector<WE>::const_iterator it, it_end;

  // it_end = c._WSet.end();
  
  // os << "W["<< std::endl;
  
  // if(c._WSet.empty()){
  //   os <<  "EMPTY _WSet" << std::endl;
  // }
  
  // else {
  // for (it = c._WSet.begin(); it !=it_end;  it ++ ){
  //   os << (*it).first << "," << (*it).second <<std::endl;
  //   // os << "[" << (*it).first.first << "," << (*it).second.first << "]" 
  //   //    << "," << "[" << (*it).first.second << "," << (*it).second.second << "]" std::endl;
  // }
  // os <<"]\n";
  // }

  std::multimap<WE, WE, mapComp>::const_iterator it , it_end;
  it_end = c._WSet.end();

  
  if(c._WSet.empty()){
    os <<  "EMPTY _WSet" << std::endl;
  }

  else {
    os << "W["<< std::endl;
    for (it = c._WSet.begin(); it !=it_end;  it ++ ){
     os << "[" << (*it).first.first << "," << (*it).second.first << "]" 
        << "-->" 
	<< "[" << (*it).first.second << "," << (*it).second.second << "]" 
	<< std::endl;
  }
  os <<"]\n";
  }


  return os;
}

// _WIterator W::IsPresent(WE  & p)
// {
//   CB c1 = p.first;
//   CB c2 = p.second;
  
//   if(c1._pid == -1 || c2._pid == -1 ||
//      c1._index == -1 || c2._index == -1) 
//     assert(false);
  
//   // if(c1.first == -1 || c1.second == -1 ||
//   //    c2.first == -1 || c2.second == -1)
//   //   assert(false);
  
//   _WIterator it, it_end;
  
  
//   it_end = _WSet.end();
  
//   for(it = _WSet.begin(); it != it_end; it++)
//     if( is_eql(p, (*it)) )
//       return it;

//   return it; 
// }



_WIterator W::IsPresent(std::pair<CB,CB> p)
{
  // a is the key <pid1, pid2>
  // b is the index values <ind1, ind2>
  std::pair <int, int> a = std::pair<int, int>(p.first._pid, p.second._pid);
  
  std::pair <int, int> b = std::pair<int, int>(p.first._index, p.second._index);
 
  if(a.first == -1 || a.second == -1 ||
     b.first == -1 || b.second == -1) 
    assert(false);
  
  _WIterator it, it_end;
  
  
  it_end = _WSet.end();
  
  std::pair <_WIterator, _WIterator> ret;
  
  ret = _WSet.equal_range(a);
  

  for(it = ret.first; it != ret.second; it++)
    if((*it).second.first == b.first && (*it).second.second == b.second)
      return it;

  return it_end; 
}

bool W::AreWOrdered(std::pair<CB, CB> p, Node *n)
{
  if(IsPresent(p) != _WSet.end()) return true;
  
  else{
    CB from = p.first;
    CB to = p.second;
    
    std::pair <_WIterator, _WIterator> ret;
    ret = _WSet.equal_range(std::pair<int, int>(from._pid, to._pid));
    
    _WIterator it;
    for(it = ret.first; it != ret.second; it ++){
      int findex = (*it).second.first;
      int tindex = (*it).second.second;
      
      if(findex < from._index && tindex > to._index){
	CB fromAncs(from._pid, findex);
	CB toDesc (to._pid, tindex);
	
	if(n->isAncestor(from, fromAncs) && n->isAncestor(toDesc, to))
	  return true;
      }
      
    }
    return false;
  }
  return false;
}




/* Not called at the moment */

 void W::RemoveWE(std::pair<CB, CB> p)
 {
//   _WIterator  i = IsPresent(p);

//   if(i != _WSet.end())
//     _WSet.erase(i);
   
   std::pair <int, int> a = std::pair<int, int>(p.first._pid, p.second._pid);
 
   std::pair <int, int> b = std::pair<int, int>(p.first._index, p.second._index);
   
   _WIterator it = IsPresent(p);
   
   if(it != _WSet.end()){
     _WSet.erase(it);

      //Debug Print
      // std::cout << "removed a wait-for edge: "
      // 		<< p.first  
      // 		<<  " ---> "  
      // 		<< p.second
      // 		<< std::endl;

   }

 }

// void W::AddWE(std::pair<CB, CB> p)
// {
//     _WIterator it = IsPresent(p);

//     if(it == _WSet.end()){
//       _WSet.push_back(p);
      
//       //Debug Print
//       std::cout << "added a wait-for edge: " << p.first << " ---> " << p.second << std::endl;
//     }

   
// }


void W::AddWE(std::pair<CB, CB> p)
{

  std::pair <int, int> a = std::pair<int, int>(p.first._pid, p.second._pid);
  
  std::pair <int, int> b = std::pair<int, int>(p.first._index, p.second._index);

  _WIterator it = IsPresent(p);

    if(it == _WSet.end()){
      _WSet.insert(std::pair <WE, WE> (a,b));
      
      //Debug Print
      // std::cout << "added a wait-for edge: "
      // 		<< p.first  
      // 		<<  " ---> "  
      // 		<< p.second
      // 		<< std::endl;
    }
   
}



void W::RefineW()
{
 /*
      for each edge a--->b
      remove any edge Desc+(a) --->Ancs*(b)
     */
    _WIterator it_end;
    _WIterator it1, it2;
    
    bool restart;


    do{
      
      restart = false;
      it_end = _WSet.end();
       
     
      for(it1 = _WSet.begin(); it1 != it_end; it1++){
	
	CB a = CB ((*it1).first.first, (*it1).second.first); 
	CB b = CB ((*it1).first.second, (*it1).second.second); 
	
    		
    	for(it2 = _WSet.begin(); it2 != it_end; it2++){
    	  
	  // CB c = (*it2).first;
    	  // CB d = (*it2).second;
	  CB c = CB ((*it2).first.first, (*it2).second.first); 
	  CB d = CB ((*it2).first.second, (*it2).second.second); 
	  
	  if(c == a && d._pid == b._pid && d._index < b._index){
	    RemoveWE(std::pair<CB, CB>(c,d));
	    restart = true;
	    break;
	  }
	  
	  if(c._pid == a._pid && c._index > a._index && 
	     d._pid == b._pid && d._index <= b._index){
	    
	    RemoveWE(std::pair<CB, CB>(c,d));
	    restart = true;
	    break;
	  }
	
    	}
	if(restart){
	  break;
	}
	
      }
    }while(restart);
}


void W::AddWESet(CB cfrom, std::set <int> scb, int pid) {

  std::set<int>::iterator it, it_end;
  it_end = scb.end();

  //  std::cout << cfrom << " to aset: [ " ;
  
  for(it = scb.begin(); it != it_end; it++) {
    //    CB cto = *(new CB(pid, *it));
    CB cto(pid, *it);
  
    //std::cout << *it << " " ;
    
    AddWE(std::pair<CB, CB>(cfrom, cto));
  }

  //std::cout << "]\n"; 
}

void W::AddWESet(std::set<int> cfrom, int pid, CB to) {

  std::set<int>::iterator it, it_end;
  it_end = cfrom.end();

  //  std::cout << cfrom << " to aset: [ " ;
  
  for(it = cfrom.begin(); it != it_end; it++) {
    //    CB cto = *(new CB(pid, *it));
    CB cf(pid, *it);
  
    //std::cout << *it << " " ;
    
    AddWE(std::pair<CB, CB>(cf, to));
  }

  //std::cout << "]\n"; 
}


// TO DO -- CHECK THIS FUNCTION THOROUGHLY
void W::TransitiveClosure(Node *nlast)
{
  
  _WIterator _vit, _vitend, _vit1, _vit2;
  bool restart;
  
  
  // __restart:

  do{
    restart = false;
    _vitend = _WSet.end();
    
    //    std::cout << "=============Restarting ==============" <<std::endl;
    //   std::cout << "_WSet size = " <<_WSet.size() << std::endl;

    for(_vit = _WSet.begin(); _vit != _vitend; _vit++){
      
      //      CB a = (*_vit).first;   // a
      // CB b = (*_vit).second;  // b
      
      CB a = CB ((*_vit).first.first, (*_vit).second.first); 
      CB b = CB ((*_vit).first.second, (*_vit).second.second); 

      
      //Debug Print
      //std::cout << " a--->b" <<std::endl;
      //std::cout << a << "---->" << b <<std::endl;
      
      /*
  	iterate over each entry of _WSet c--->d
  	add a--->d iff
  	1) c is Ancs*(b) 
  	2) d is not in Ancs^+(a)
  	3) a --> Desc*(d) does not exist
      */
      
      
      
      for(_vit1 = _WSet.begin(); _vit1 != _vitend; _vit1++) {
	
  	// CB c= (*_vit1).first;  //c
  	// CB d = (*_vit1).second; // d

	CB c = CB ((*_vit1).first.first, (*_vit1).second.first); 
	CB d = CB ((*_vit1).first.second, (*_vit1).second.second); 
 
 	bool flag = true;;
	
  	//Debug Print
	
  	//std::cout << "\t " << c << "---->" << d <<std::endl;
  	//std::cout.flush();
	
  	if(c._pid == b._pid && c._index <= b._index){
  	  // proceed only when c in Ancs*(b)
  	  if( d._pid != a._pid) {
  	    // make sure d is not from Proc(a) -- avoiding circularity  
  	    for(_vit2 = _WSet.begin(); _vit2 != _vitend; _vit2++) {
  	      // check if a --> _vit2.second: _vit2.second is in the 
  	      // desc*(d)
	      CB e = CB ((*_vit2).first.first, (*_vit2).second.first); 
	      CB f = CB ((*_vit2).first.second, (*_vit2).second.second); 

  	      if( e == a && f._pid == d._pid 
  		  && f._index >= d._index){
  		flag = false;
  		continue;
  	      }
  	    }
  	    if (flag){ 
  	      AddWE(std::pair<CB, CB>(a, d));
  	      //std::cout << "breaking out of inner loop" <<std::endl;
  	      restart = true;
  	      break;
  	    }
  	  }
  	  else{
  	    if(d._index > a._index){
  	      AddWE(std::pair<CB, CB>(a, d));
  	      restart = true;
  	      //std::cout << "just found a deadlock breaking out of inner loop" <<std::endl;
  	      break;
  	    }
  	  }
	  
  	}
	
      }

      if(restart){
  	//std::cout << "breaking out of outer loop" <<std::endl;
  	break;
      }
    }
    //std::cout << "restart value : " << restart <<std::endl;
  }while(restart);
}

/*Returns the last WE edge */
std::pair<CB, CB> W::LastWE(std::pair<CB, CB> p)
{
  CB from = p.first;
  CB to = p.second;
  
  int src_pid = from._pid;
  int dest_pid = to._pid;
  
  _WIterator _vit, _vitend;
  
  _vitend = _WSet.end();

  for(_vit = _WSet.begin(); _vit != _vitend; _vit++){
    
    //    CB _wfrom = (*_vit).first;
    //    CB _wto = (*_vit).second;
    
    CB _wfrom = CB ((*_vit).first.first, (*_vit).second.first);
    CB _wto = CB ((*_vit).first.second, (*_vit).second.second);;

    if( _wfrom._pid == src_pid && _wto._pid == dest_pid){

      if( _wfrom._index >= from._index && _wto._index >= to._index ){

	from = _wfrom;
	to = _wto;

      }
    }
  }

  return (std::pair<CB, CB>(from, to));
}



void W::_WConstructInternal(Node *ncurr, Node *nlast) {
  
  int _psrc = ncurr->curr_match_set.front()._pid; // sending process pid
  int _pdst = ncurr->curr_match_set.back()._pid;  // recv process pid

  std::vector<int> _list;
  std::set<int> _aset;
  
  _aset.clear();
  _list.clear();
  
  // std::cout << "computing WF for match-set: [ " 
  // 	    << ncurr->curr_match_set.front() << "," 
  // 	    <<ncurr->curr_match_set.back() << " ]" <<std::endl; 

  Envelope *efront = ncurr->GetTransition(ncurr->curr_match_set.front())->GetEnvelope();
  Envelope *eback =  ncurr->GetTransition(ncurr->curr_match_set.back())->GetEnvelope();
  
  if (efront->isSendType()){
   
    /* Scurr ---> x | x = ImmediateAncs(First(M^o(Scurr))) */
    std::set<CB> coi = MPtr->MImage(ncurr->curr_match_set.front());
    CB firstcb = MPtr->FirstM(coi, _pdst);
    
    _list.push_back(firstcb._index);
    _aset = getImmediateAncestorList(ncurr, _pdst, _list);
    
    if(!_aset.empty())  
      AddWESet(ncurr->curr_match_set.front(), _aset, _pdst); 
    
    
    _aset.clear();
    _list.clear();
    
    /* y --->First*(M^o(Scurr)) | y = ImmediateDesc(Scurr) */
    _list.push_back(ncurr->curr_match_set.front()._index);
    _aset = getImmediateDescendantList(nlast, _psrc, _list);
    
    if(!_aset.empty())
      AddWESet( _aset, _psrc, firstcb); 
    
   _aset.clear();
   _list.clear();
   
   
   /* z --->Scurr | z = ImmediateDesc(Last(M^o(Scurr))) */
   CB lastcb = MPtr->LastM(coi, _pdst);
   _list.push_back(lastcb._index);
   _aset = getImmediateDescendantList(nlast, _pdst, _list);
   
   if(!_aset.empty())
     AddWESet( _aset, _pdst, ncurr->curr_match_set.front()); 
   
  _aset.clear();
  _list.clear();
  }
 
  if ( eback->isRecvTypeOnly() &&  !(eback->src == WILDCARD)){
    
    /* Rcurr ---> x | x = ImmediateAncs(First(M^o(Rcurr))) */
    std::set<CB> coi = MPtr->MImage(ncurr->curr_match_set.back());
    CB firstcb = MPtr->FirstM(coi, _psrc);
    
    _list.push_back(firstcb._index);
    _aset = getImmediateAncestorList(ncurr, _psrc, _list);
    
    if(!_aset.empty())  
      AddWESet(ncurr->curr_match_set.back(), _aset, _psrc); 
    
    _aset.clear();
    _list.clear();
    
    /* y --->First*(M^o(Rcurr)) | y = ImmediateDesc(Rcurr) */
    _list.push_back(ncurr->curr_match_set.back()._index);
    _aset = getImmediateDescendantList(nlast, _pdst, _list);
    
    if(!_aset.empty())
      AddWESet( _aset, _pdst, firstcb); 
    
    _aset.clear();
    _list.clear();

    /* z --->Rcurr | z = ImmediateDesc(Last(M^o(Rcurr))) */
    CB lastcb = MPtr->LastM(coi, _psrc);
    _list.push_back(lastcb._index);
    _aset = getImmediateDescendantList(nlast, _psrc, _list);
    
    if(!_aset.empty())
      AddWESet( _aset, _psrc, ncurr->curr_match_set.back()); 
    
    _aset.clear();
    _list.clear();
  }
  
  if(efront->func_id == BARRIER){
    
    std::list<CB>::iterator bit, bit1, bitend;
    bitend = ncurr->curr_match_set.end();
    
    for(bit = ncurr->curr_match_set.begin(); bit != bitend; bit++){

      CB tob = *bit;
      
      _list.push_back(tob._index);
      _aset =  getImmediateAncestorList(ncurr, tob._pid , _list);
      
      for(bit1 = ncurr->curr_match_set.begin(); bit1 != bitend; bit1++){
	
	if((*bit1) == tob) continue;
	
	else{
	  if(!_aset.empty())
	    AddWESet((*bit1), _aset, tob._pid ); 
	}
      }
      _aset.clear();
      _list.clear();

    }
  }
}



void W::_WConstruct(ITree *itree) {
  Node *ncurr, *nlast;

  // get the last node of itree
  nlast = itree->_slist[itree->_slist.size()-1];

  std::vector<Node*>::iterator _slist_it, _slist_it_end;

  _slist_it_end = itree->_slist.end();

  int i = 0;

  for(_slist_it = itree->_slist.begin(); 
      _slist_it != _slist_it_end; _slist_it++, ++i) {
    
    ncurr = *(_slist_it);
    
    /* check to make sure the curr_match_set is not garbage
     For collective operations -- curr_match_set is not 
     populated correctly by ISP and therefore it can contain
     garbage values.
     NOT A GOOD FIX -- svs
    */
    if(ncurr->curr_match_set.back()._pid >= ncurr->NumProcs() || 
       ncurr->curr_match_set.back()._pid < 0)
      continue;
    
    Envelope *env = ncurr->GetTransition(ncurr->curr_match_set.back())->GetEnvelope();

    //std::cout << *(ncurr->GetTransition(ncurr->curr_match_set.back()))<<std::endl;
    //std::cout << i << std::endl;

    if((ncurr->curr_match_set.size() == 2 && env->isRecvTypeOnly()) ||
       env->func_id == BARRIER){
      
      //std::cout<< "WCounstructDet called for Node with match \n"
      //<<ncurr->curr_match_set.front()<<ncurr->curr_match_set.back()<<std::endl;

          _WConstructInternal(ncurr, nlast);
    }
  }
}     




//////////////////////////////////////////////////////
//                                                /// 
//       Refinement Rules for M^o                ///  
///////////////////////////////////////////////////

bool W::ApplyRefineRuleOne(Node *n, int &redrule1cnt) 
{
  /*
   * Algorithm:
   * for each wfr a->b
   *  for each c in Desc*(a) 
   *      for each d in Ancs*(b)
   *          if (c,d) in M
   *              remove (c,d) from M
   */
  
  // std::cout << " ==================================="  << std::endl;
  // std::cout << " Starting Refinement Rule 1"  << std::endl;  
  // std::cout << " ==================================="  << std::endl;

  _WIterator wit, witend;
  bool remove_flag = false;
  bool result = false;

  _MIterator mit, mitend;
  
  
  witend = _WSet.end();

  for(wit = _WSet.begin(); wit != witend; wit++) {
    
    // a--->b 
    CB a ((*wit).first.first, (*wit).second.first); 
    CB b ((*wit).first.second, (*wit).second.second); 

    // std::cout << " Evaluating M^o edges for the WF: [ "
    // 	      << a << "," << b << " ]" <<std::endl;  
    
    
    std::pair<_MIterator, _MIterator> ret;

    // std::cout << "Applying refinement for wait-for:";
    // std::cout << a << " ---->"<< b << ":" <<std::endl; 
    
  _restart:
    mitend = MPtr->_MSet.end();
    // ret = MPtr->_MSet.equal_range((*wit).first);
    
    // for(mit = ret.first; mit != ret.second; mit++){
    for(mit = MPtr->_MSet.begin(); mit != mitend; mit++){
      // c --- d
      CB c  = (*mit).second.front(); // ((*mit).first.first, (*mit).second.first);
      CB d =  (*mit).second.back();// ((*mit).first.second, (*mit).second.second);
      
      //std::cout << c << " ----"<< d << std::endl; 

      // std::cout << " Evaluating M^o edges [ "
      // 		<< c << "," << d << " ]" <<std::endl;  
      
      if( c._pid == a._pid && d._pid == b._pid) {
	if(c._index == a._index && d._index == b._index)
	  remove_flag = true;
	else {
	  if(c._index > a._index && d._index == b._index){
	    if(n->isAncestor(c, a))
	      remove_flag = true;
	  }
	  else if(c._index > a._index && d._index < b._index) {
	    if(n->isAncestor(c, a) && n->isAncestor(b,d))
	      remove_flag = true;
	  }
	}
      }
      
      else if (c._pid == b._pid && d._pid == a._pid){
	if(c._index == b._index && d._index == a._index)
	  remove_flag = true;
	else {
	  if( d._index > a._index && c._index == b._index){
	    if(n->isAncestor(d, a))
	      remove_flag = true;
	  }
	  else  if(d._index > a._index && c._index < b._index){
	      if( n->isAncestor(d,a) && n->isAncestor(b,c))
		remove_flag = true;
	    }
	}
      }
      else continue;
      
      if(remove_flag){
	
	redrule1cnt++;
	MPtr->_MSet.erase(mit);
	//Debug Print
	std::cout << "removed a match edge: "
		  << c  
		  <<  " --- "  
		  << d
		  << std::endl;
	
	//	flag = true;
	result = true;
	remove_flag = false;
	goto _restart;
	//break;
      }
      // if(flag){ 
      // 	flag = false;
      // 	goto _restart;
      // }
      
    }
  }
  return result;
}

bool W::Balance(Node *n, CB recv, CB send)
{

  // std::vector<int> priorRecv, tmp;
 
  std::set<CB> Msends;
  
  std::set<int> priorRecv;
  
  std::set<int> tmp = n->getAllAncestors(recv);
  
  std::set<int>::iterator tit;
  
  //  std::cout << "tmp size" << tmp.size() << std::endl;
  /*priorRecv = GetAllPriorRecv(recv); */
  
  for( tit = tmp.begin(); tit != tmp.end(); tit++){
    
    Transition* t  = n->GetTransition(recv._pid, *tit);
    
    if(t->GetEnvelope()->isRecvTypeOnly()){

      priorRecv.insert(*tit);
      
    }
  
  }

  // std::cout << "Count of prior receive of " 
  // 	    << recv << ":" << priorRecv.size() <<std::endl;
    
  /*for each recv in priorRecv get the potential Match set
    excluding any send that is Wait-for ordered w.r.t "send"
  */
  
  for(tit = priorRecv.begin(); tit != priorRecv.end(); tit++){

    CB r (recv._pid, *tit);
    
    std::set<CB> tmp1 = MPtr->MImage(r);
    std::set<CB> tmp2;
    
    std::set<CB>::iterator sit;

    // std::cout << "MImage of the recv "  
    // 	      << r << " is:" <<std::endl;

    for(sit = tmp1.begin(); sit != tmp1.end(); sit++){

      //      std::cout <<  *sit <<std::endl;  

      if(!AreWOrdered(std::pair<CB,CB>(*sit, send), n))
  	if( (*sit)._pid == send._pid){
  	  if((*sit)._index != send._index)
  	    if(!n->isAncestor(*sit, send))
  	      tmp2.insert(*sit); 
  	}
  	else tmp2.insert(*sit); 
    }
     
    // std::cout << "Size of Mimage of prior receive  "
    // 	      << r << ":" << tmp2.size() << std::endl;
    
    if (tmp2.size() == 0)
      return false;

    else
      Msends.insert(tmp2.begin(), tmp2.end());
  }

  if(priorRecv.size() > Msends.size())
    return false;
  
  return true;
  
}

bool W::ApplyRefineRuleTwo(Node *n, int & redrule2cnt)
{
  /*
   * Algorithm
   * - For each potential match edge [a,b](barring the actual match edge) in M
   * - see if every "b" type operation in the Ancs+(b) has a legal match
   * - while doing the previous check, make sure that no sends of type a 
   *   are non -overtaking ordered 
   */
  
  // std::cout << " ==================================="  << std::endl;
  // std::cout << " Starting Refinement Rule 2"  << std::endl;  
  // std::cout << " ==================================="  << std::endl;


  _MIterator mit, mitend;
  
  mitend = MPtr->_MSet.end();
  

  bool ret =false;
  bool remove_flag = false;

 _restart:
    
  for(mit =  MPtr->_MSet.begin(); mit != mitend; mit++){
    
    CB a = (*mit).second.front(); //((*mit).first.first, (*mit).second.first); 
    CB b = (*mit).second.back(); // ((*mit).first.second, (*mit).second.second); 
    
    Transition * t1 = n->GetTransition(a);
    Transition * t2 = n->GetTransition(b);
    
    if (t1->GetEnvelope()->src == WILDCARD)  {

      if(!Balance(n,a,b)){
	remove_flag = true;
	ret = true;
      }
    }
    
    else if(t2->GetEnvelope()->src == WILDCARD){
      
      // std::cout	<<  " --- "  << std::endl;
      // std::cout << "Computing balance of : " 
      // 		<< a  
      // 		<<  " --- "  
      // 		<< b
      // 		<< std::endl;
      
      if(!Balance(n,b,a)){
	
	remove_flag = true;
	
      }
    }
    
    else continue;
    
    if(remove_flag){

      redrule2cnt++;
      MPtr->_MSet.erase(mit);
      remove_flag = false;
 
      //Debug Print
      std::cout << "removed a match edge: "
      		<< a  
      		<<  " --- "  
      		<< b
      		<< std::endl;
      
      ret = true;
      
      goto _restart;
    }
    
  }
  
  return ret;
}


void W::RemoveMatchedSends(std::set<CB> &res, std::vector<std::list<CB> > l, CB send)
{
  std::vector<std::list<CB> >::iterator lit, lit_end;
 
  lit_end = l.end();
  
  for(lit = l.begin(); lit != lit_end; lit++){
    
    CB s = (*lit).front();
    
    std::set<CB>::iterator mit; 

    mit = res.find(s);
    
    if( mit != res.end()){

      res.erase(mit);
      // std::cout << "Removed the matched send from collective Mo: " 
      // 		<< s << std::endl;
      
    }
    if ( s == send) break;

  }
  
}


void W::RemoveWorderedSends(std::set<CB> &res, CB s, Node *n)
{

  std::set<CB>::iterator rit, rit_end;
  //  rit_begin = res.begin();

 _restart:
  rit_end = res.end(); 
  for (rit = res.begin(); rit != rit_end; rit ++){
    
    if (AreWOrdered(std::pair<CB, CB> (*rit, s), n ) ||
	n->isAncestor(*rit, s)){
      
      //rit_begin = --rit;
      // std::cout << "Removing the W ordered send from collective Mo: "
      // 		<<  *rit <<std::endl;
      res.erase(*rit); 
      
      goto _restart;
      
    } 

  }
}
// void W::ChooseFirst(std::set<CB> &res)
// {
//   std::set<CB>::iterator rit, rit_end, rit1;

//   rit_end = res.end();

//   std::set<CB> tmp;
  
//   for(rit = res.begin(); rit != rit_end; rit ++){

//     CB min;

//     min = *rit;
    
//     for(rit1 = res.begin(); rit1 != rit_end; rit1 ++){
      
//       if ( min._pid == (*rit1)._pid && min._index > (*rit1)._index)
// 	min = *rit1;
      
//     }

//     tmp.insert(min);
    
//   }

//   res.clear();

//   res.insert(tmp.begin(), tmp.end());
  
// }

// std::set<CB> W::FindEnabledSends(CB s, CB r, std::vector<std::list<CB> > l, Node *n)
// {

  
//   /*r -- its a receive
//    res = M^o(r) -- Potential match image of operation c */
//   std::set<CB> res = MPtr->MImage(r);
  
//   /*res <--- res / l --- remove all those sends that have matched so far
//     NOTE: Does it include the target of Wait-for dependency S??
//    */
//   RemoveMatchedSends(res, l);

//   /*
//     Remove any send that is Wait-for ordered or IntraMB ordered w.r.t. S
//   */
//   RemoveWorderedSends(res, s, n);
  

//   /*
//     Choose the first ordered send from each process
//    */
//   ChooseFirst(res);

//   return res;

// }

CB W::isSendTrgtofWait(CB s, CB r, Node *n)
{

  std::pair<_WIterator, _WIterator> ret; 

  ret = _WSet.equal_range(std::pair<int, int> (r._pid, s._pid));
  
  _WIterator wit;
  
  for(wit = ret.first; wit != ret.second; wit ++){
    
    CB from = CB ((*wit).first.first, (*wit).second.first); 
    CB to = CB ((*wit).first.second, (*wit).second.second); 
    
    if(from._index > r._index){
      if(n->isAncestor(from,r)){
	if( to._index == s._index)
	  return from;
	else {
	  if(to._index > s._index)
	    if(n->isAncestor(to, s))
	      return from;
	}
      }
    }
  }
  return CB(-1, -1);
}



bool W::DeadlockDetection(std::vector<std::list <CB> > al, Node *last, int &spid)
{

  // std::cout << " ==================================="  << std::endl;
  // std::cout << " Starting Deadlock detection"  << std::endl;  
  // std::cout << " ==================================="  << std::endl;



  std::vector<std::list<CB> >::iterator ait, aitend;

  aitend = al.end();

  for(ait = al.begin(); ait != aitend; ait ++){
    
    if((*ait).size() == 2){

      CB front = (*ait).front();
      CB back = (*ait).back();

      Envelope *fronte = last->GetTransition(front)->GetEnvelope();
      Envelope *backe =  last->GetTransition(back)->GetEnvelope();
      
      if( fronte->isSendType() && backe->isRecvTypeOnly() ) {
	
	// std::cout << " Evaluating Recv in match-set: [ " 
	// 	  << front << "," << back << " ]"
	// 	  << std::endl;  
	
	if(backe->src != WILDCARD){

	  // std::cout << " Recv " 
	  // 	    << back << " is deterministic"
	  // 	    << std::endl; 
	  
	  /* coi = M^o(back)*/
	  std::set<CB> coi = MPtr->MImage(back);
	  
	  /* lastofR = Last(M^o(back))*/
	  CB lastofR = MPtr->LastM(coi, front._pid);
	  
	  /* check if lastofR has a potential edge to an ancestor of back*/
	  /* which mean checking if first(M^o(lastofR)) is in ancestor of back*/
	  std::set<CB> coiR = MPtr->MImage(lastofR);
	  CB firstofS = MPtr->FirstM(coiR, back._pid);
	  
	  if(last->isAncestor(back, firstofS)){
	    
	    std::cout << "DEADLOCK FOUND: The last match for operation " <<back
		      << " is: "<< lastofR << " which finds a match in: "
		      << firstofS << std::endl;
	    return true;;
	  }
	}

	/* either an R* or a det receive */
	// std::cout << " Checking of Send:  " 
	// 	  << front << "is a target of Wait-for dependency" 
	// 	  << std::endl; 

	CB WaitSrc = isSendTrgtofWait(front, back, last);

	// std::cout << " Source of Wait for dependency is:  " 
	// 	  << WaitSrc  << std::endl; 
	
	if (!(WaitSrc._pid == -1)){ 
	  
	  /* get all receive calls starting from "back 
	     up to and include "WaitSrc"
	  */
	  std::vector<std::list<CB> >::iterator it;	  
	  std::set<CB> Rset;
	  
	  for(it = ait; it != aitend; it ++){
	    
	    if((*it).size() == 2){
	      CB bk = (*it).back();
	      CB ft = (*it).front();
	      Envelope *bke =  last->GetTransition(back)->GetEnvelope();
	      if( bke->isRecvTypeOnly() && bk._pid == back._pid ) {
		Rset.insert(bk);
		if(bk == WaitSrc) break;
	      }
	      if(ft == WaitSrc)break;
	    }
	    else{
	      if (last->GetTransition((*it).front())->GetEnvelope()->func_id == BARRIER){
		std::list<CB>::iterator iter;
		bool brflag =false;
		for(iter = (*ait).begin(); iter != (*ait).end(); iter++){
		  if((*iter) == WaitSrc) { 
		    brflag = true; break;
		  }
		}
		if (brflag) break;
		
	      }
	      
	    }
	    
	  }

	  /* get the receive call's M^o sets */
	  // std::cout << "RSet: " <<std::endl;
	  //print(Rset);

	  std::set<CB>collectiveM = MPtr->collectMo(Rset);
	  //print(collectiveM);

	  RemoveMatchedSends(collectiveM, al, front);
	  //print(collectiveM);

	  
	  RemoveWorderedSends(collectiveM,front, last);
	  //print(collectiveM);


	  if(Rset.size() <= collectiveM.size() ){
	    std::cout << "DEADLOCK FOUND: The operation " <<front
		      << " can be delayed until "<<  WaitSrc <<std::endl;
	    return true;;
	  }
	}
      }
    }
  }
  return false;
}

void print(std::set<CB> l){

  std::set<CB>::iterator lit, lit_end;

  lit_end = l.end();

  std::cout << "[" << std::endl;
  
  for (lit = l.begin(); lit != lit_end; lit ++){

    std::cout << *lit << std::endl;
    
  }
  std::cout << "]" << std::endl;
  
}
