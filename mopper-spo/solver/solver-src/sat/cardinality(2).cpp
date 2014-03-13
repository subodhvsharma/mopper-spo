#include "cardinality.h"
#include <cmath>
#include<algorithm>
#include <iterator>
#ifdef DEBUG
#include <iostream>
#endif

/*****************************************************************************\
 *
 * Function : atmostone
 *
 * Input : literals
 *
 * Output : formula
 *
 * Purpose : Given set of literals {x1..xn} in literals
 * return \wedge _{i \neq j } \neg x_i \vee \neg x_j
 * in formula
 *
 */
 bool binomial_encodingt::atmostone(const bvt& literals,
    formulat& formula)
{
  unsigned int size=literals.size();
  formula.clear();
  if(size==0) return false;
  for(unsigned int i=0;i<size;i++)
  {
    for(unsigned int j=i+1;j<size;j++)
    {
      bvt clause;
      clause.push_back(!literals[i]);
      clause.push_back(!literals[j]);
      formula.push_back(clause);
    }
  }
  return true;
}
/*****************************************************************************\
 *
 * Function : atmostk
 *
 * Input : literals, k
 *
 * Output : formula
 *
 * Purpose : given set of literals G ={x1..xn} in literals
 * return \wedge _{|S|=k+1, S \subseteq G} \vee _{x_i \in S} \neg x_i
 *
 * returns false if input is ill-formed such as k==0 or
 * set G is empty
 */
 bool binomial_encodingt::atmostk(const bvt& literals,
    unsigned int k,formulat& formula)
  {
   unsigned int size=literals.size();
   if(size==0 || k==0) return false;
   // if size of G is less than k then
   // it is trivially true
   // add TRUE to the formula and return
   if(size<=k)
   {
#if 0
   //  literalt l = prop.new_variable();
   //  l.make_true();
   //  bvt clause;
   //  clause.push_back(l);
   //  formula.push_back(clause);
   //
#endif
	   //this is trivially true so return an empty formula
     formula.clear();
     return true;
   }

       std::list<std::list<literalt> > subsets;

       subsets_k(literals,k+1,subsets);

       for(typename std::list<std::list<literalt> >::iterator it=subsets.begin();
           it!=subsets.end();it++)
       {
         bvt clause;
         for(typename std::list<literalt>::iterator lit=it->begin();
             lit!=it->end();lit++)
         {
           clause.push_back(!(*lit));
         }
         formula.push_back(clause);

       }

    return true;
  }

 bool commander_encodingt::atmostk(const bvt& literals,
    unsigned int k, formulat& formula, unsigned int gsize)
{
    unsigned int size=literals.size();

    //group size should always be greater than k, termination
    //is not guaranteed otherwise
    //size has to be nonzero
    if(gsize<=k || size==0 || k==0 ) return false;
    //if size<=k it is trivially true, return an empty formula
    if(size<=k) {formula.clear();return true;}
    //ngroup - number of groups
    unsigned int ngroup;
    {
     // double tmp = ceil((static_cast<double>(size))/gsize);
     // ngroup = static_cast<unsigned int>(tmp);
      ngroup = ((size-1)/gsize)+1;
    }
    // if there is only one group, just go for binomial
    // encoding and return
    //According to the paper, if n < 7 or n <= k+s (k+gropsize)
    // commander encoding does not lead to a smaller subproblem
    // compared to binomial encoding
    //so just go for the binomial encoding
    if(ngroup==1 || size < 7 || size <= k+gsize)
    {
      binomial_encodingt be(prop);
      formulat nformula;

      bool result = be.atmostk(literals,k,nformula);
#ifdef DEBUG
      print_formula(std::cout,nformula);
#endif
      formula.splice(formula.begin(),nformula);
      return result;
    }

    unsigned int lgroupsize = size - ((ngroup-1)*gsize);

    // commander variables
    bvt commanders;
    for(unsigned int i=0;i<ngroup;i++)
    {
      //commander variables for group i
      bvt gcommanders;

      //this group should have G_i \cup {\neg c_i,j | j \in {1..k}}
      bvt thisgroup;
    

      // gstart should point to the beginning
      //of group i
      bvt::const_iterator gstart = literals.begin();
      std::advance(gstart,i*gsize);

      //gend should point to the end of group i
      bvt::const_iterator gend;

      //for all the groups number of commander
      // variables to be introduced is k
      // but for the last group it should be the size
      // of the group if it is less than k
      unsigned int numcvar=k;
      if(i==ngroup-1)
      {
        gend = literals.end();
	numcvar= k>lgroupsize?lgroupsize:k;
      }
      else
      {
        gend = gstart;
        std::advance(gend,gsize);
      }

     
      for(unsigned int tmp=0;tmp<numcvar;tmp++)
      {
        // populate numcvar-commander variables with
        //fresh literals.
        //NOTE : constructor of literalt has to
        //be called to get a fresh unused variable no
          literalt l= prop.new_variable();
          gcommanders.push_back(l);
          thisgroup.push_back(!l);

      }

   // remember that insert method inserts [gstart,gend)
      // so gend should point to the next element of the
      //last element of group i
      thisgroup.insert(thisgroup.begin(),gstart,gend);


      // encode =numcvar constraints on G_i \cup {\neg c_i,j | 1<=j<=k}
      binomial_encodingt be(prop);
      formulat nformula;
      
      bool result = be.exactlyk(thisgroup,numcvar,nformula);
#ifdef DEBUG
      print_formula(std::cout,nformula);
#endif
      if(!result) return result;

      formula.splice(formula.begin(),nformula);

      //breaking symmetry \forall 1<=j<=k-1, c_i,j => c_i,j+1
      for(unsigned int tmp=0;tmp<numcvar-1;tmp++)
      {
        bvt clause;
        clause.push_back(!gcommanders[tmp]);
        clause.push_back(gcommanders[tmp+1]);
        formula.push_back(clause);
      }

      commanders.insert(commanders.begin(),gcommanders.begin(),gcommanders.end());
    }

    //recurse on commander variables
    formulat nformula;
    bool result=atmostk(commanders,k,nformula,gsize);
#ifdef DEBUG
      print_formula(std::cout,nformula);
#endif
    if(!result) return result;
    formula.splice(formula.begin(),nformula);

#ifdef DEBUG
      print_formula(std::cout,formula);
#endif
    return true;


}

 bool commander_encodingt::atmostk(const bvt& literals,
    unsigned int k,formulat& formula)
{

  // the paper "SAT Encodings of the At-most-k Constraint"
  //by Alan M Frisch and Paul A Giannaros suggests
  //k+2 to be a good choice for groupsize
  return atmostk(literals,k,formula,k+2);
}


