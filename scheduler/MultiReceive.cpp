#include "MultiReceive.hpp"
#include <cassert>


bool multiReceive::isPresent(CB a)
{
  int pid = a._pid;
  int indx = a._index;
  
  std::list<std::pair <CB, CB> >::iterator lit; 
  for (lit = receives.begin(); lit != receives.end(); lit++){
    if(pid != (*lit).first._pid) continue;
    else {
      int top_indx  = (*lit).first._index;
      int bottom_indx = (*lit).second._index;
      if ((top_indx <= indx) && 
	  (indx <= bottom_indx))
	return true;
    }
  }
  return false;
  // for a multireceive can we also merge the match-sets of 
  // all the receives in the multireceive.
}

void multiReceive::print()
{
  std::list<std::pair <CB, CB> >::iterator lit; 
  std::cout << " MultiReceives: [ \n";
  for (lit = receives.begin(); lit != receives.end(); lit++){
    std::cout << "<" 
	      << (*lit).first << " "
	      << (*lit).second << ">" 
	      <<std::endl;
  }
  std::cout << " MultiReceives: ] \n";
}

