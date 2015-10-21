#include "cardinality.h"
#include <cassert>
#include <cmath>
#include<algorithm>
#include <iterator>
#ifdef DEBUG
#include <iostream>
#endif

typedef std::list<literalt> literalst;
#if 0 //DEBUG
void print_literals(bvt& literals)
{
  std::cout << "printing literals";
  unsigned int size=literals.size();
  for(unsigned int i=0;i<size;i++)
  {
    std::cout<< " " << literals[i] ;
  }
  std::cout << std::endl;
}
#endif
/***************************************************************************\
 * Function : add_to_prop
 *
 * Input : formula
 *
 * Output : 
 *
 * Purpose : given a list of clause/bvt/vector of literals add it to the
 * solver prop
 *
 * This separate method is provided so that it does not force people to add
 * cardinality constraint/formula in the solver if they do not wish. All
 * other encoding methods just returns the formula without adding to a solver
 */

void encodingt::add_to_prop(formulat& formula)
{
  for(formulat::iterator it=formula.begin();
      it!=formula.end();it++)
  {
    prop.lcnf((*it));
  }
}
bool encodingt::atmostzero(const bvt& literals,formulat& formula)
{
	for(bvt::const_iterator lit=literals.begin();lit!=literals.end();lit++)
	{
		bvt clause;
		clause.push_back(!(*lit));
		formula.push_back(clause);
	}
	return true;
}
/***************************************************************************\
 * Function : encodingt::get_lit_for_formula
 *
 * Input : formula
 *
 * Output : literal
 *
 * Purpose : given a list of clause/bvt/vector of literals add it to the
 * solver prop and return an equiisfiable literal
 *
 * This separate method is provided so that it does not force people to add
 * cardinality constraint/formula in the solver if they do not wish. All
 * other encoding methods just returns the formula without adding to a solver
 */


literalt encodingt::get_lit_for_formula(formulat& formula)
{
  bvt tmp_formula;
  for(formulat::iterator it=formula.begin();
      it!=formula.end();it++)
  {

    literalt l =prop.lor(*it);

    tmp_formula.push_back(l);

  }
     literalt f = prop.land(tmp_formula);

  return f;

}
/*****************************************************************************\
 *
 *
 * Function : encodingt::get_enabling_lit_for_formula
 *
 * Input : formula
 *
 * Output : literal
 *
 * Purpose : given a list of clauses/bvt/vector of literals add it to the
 * solver prop and return a literal l. When l is used in set_assumptions,
 * it forces the formula to become satisfiable. For better efficiency,
 * use !l in set_assumptions when the formula need not be satisfied.
 *
 * NOTE : l is NOT equiisfiable to the formula
 *
 *
 *
 *
 */
literalt encodingt::get_enabling_lit_for_formula(formulat& formula)
{
  //bvt tmp_formula;
	literalt l=prop.new_variable();
	literalt not_l = !l;

  for(formulat::iterator it=formula.begin();
      it!=formula.end();it++)
  {

    it->push_back(not_l);
    prop.lcnf(*it);


  }
  return l;

}
/***************************************************************************
 *  Function : encodingt::set_enabling_lit_for_formula
 *
 *  Input : l - literal, formula
 *
 *  Output :
 *
 *  Purpose : every clause c in the formula is modified as c \vee \neg l.
 *              This modified formula is added to the solver. Now
 *              whenever l is TRUE, formula is enforced.
 *  Precondition : Literal l must be a valid literal in the solver
 *
 */
 void encodingt::set_enabling_lit_for_formula(formulat& formula,literalt l)
{

	literalt not_l = !l;

  for(formulat::iterator it=formula.begin();
      it!=formula.end();it++)
  {

    it->push_back(not_l);
    prop.lcnf(*it);


  }
  return ;

}
/*****************************************************************************\
 * Function : encodingt::atleastk
 *
 * Input : literals, k 
 *
 * OUtput : true/false, formula
 *
 * Purpose : Returns false if input literals,k is ill-formed. Returns true and
 * formula in cnf form to encode >=k(x1...xn) constraints over literals
 * (x1...xn)
 *
 * Note that >=k(x1...xn) is same as <=(n-k)(\neg x1....\neg xn)
 * ***************************************************************************/

bool encodingt::atleastk(const bvt& literals,
    const unsigned int k,formulat& formula)
{
  if(!sanity_check(literals,k,formula)) return false;
  formula.clear();
  unsigned int size = literals.size();
  if(k==0)
  {
    //trivially true
    return true;
  }
  else if(k==1)
  {
	  //just add a clause
	  formula.push_back(literals);
	  return true;
  }
  else if(size==k)
  {
    // if size==k it means that all the literals should be satisfied
    // so just AND them together
    for(bvt::const_iterator it=literals.begin();it!=literals.end();it++)
    {
      bvt clause;
      clause.push_back(*it);
      formula.push_back(clause);
    }
    return true;
  }

  else if(size > k)
  {

    bvt nliterals;
    for(bvt::const_iterator it=literals.begin();it!=literals.end();it++)
    {
      nliterals.push_back(!(*it));
    }

    return atmostk(nliterals,size-k,formula);

  }
  else
  {
    formula.clear();
    return false;
  }
}

/*****************************************************************************\
 * Function : encodingt::atleastone
 *
 * Input : literals
 *
 * Output : formula, true/false
 *
 * Purpose : returns false if literals is ill-formed, returns formula that 
 * encode >=1(x1...xn) over given set of literals (x1....xn). Essentially
 * it is just a clause x1 \vee x2 \vee ..\vee xn
 * ***************************************************************************/
bool encodingt::atleastone(const bvt& literals,formulat&formula)
{
  if(!sanity_check(literals,1,formula)) return false;
  formula.clear();
  bvt clause;
  for(bvt::const_iterator it=literals.begin();it!=literals.end();it++)
  {
    clause.push_back(*it);
  }
  formula.push_back(clause);
  return true;

}
/*****************************************************************************\
 * Function : encogint::exactlyk
 *
 * Input : literals, k
 *
 * Output : formula, true/false
 *
 * Purpose: returns false on ill-formed input, returns =k(x1...xn) constraints
 * encoded in formula
 * =k(x1....xn) <=> <=k(x1...xn) \wedge >= (x1...xn)
 * ***************************************************************************/
bool encodingt::exactlyk(const bvt& literals,
    const unsigned int k,formulat& formula)
{
  if(!sanity_check(literals,k,formula)) return false;

  unsigned int size=literals.size();
  if(k==0) return encodingt::atmostzero(literals,formula);
  if(size==k)
  {
    return atleastk(literals,k,formula);
  }
  else if(k > size)
  {
    formula.clear();
    return false;
  }

  bool result = false;

  formulat atmostformula,atleastformula;

  result = atmostk(literals,k,atmostformula);
  result = result && atleastk(literals,k,atleastformula);

// #ifdef DEBUG
//   std::cout << "At most formula " << std::endl;
//   print_formula(std::cout,atmostformula);
//   std::cout << "At least formula " << std::endl;
//   print_formula(std::cout,atleastformula);
// #endif

  formula.splice(formula.begin(),atmostformula);
  formula.splice(formula.begin(),atleastformula);

  return result;

}


/*****************************************************************************\
 *
 * Function : binomial_encodingt::atmostone
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
  if(!sanity_check(literals,1,formula)) return false;
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
 * Function : binomial_encodingt::atmostk
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
 *
 *
 * WARNING : for non trivial n and k it has to generate n 
 * choose k subset which could be a huge number. This may not scale for
 * large values of n and k
 */
bool binomial_encodingt::atmostk(const bvt& literals,
    unsigned int k,formulat& formula)
{
  unsigned int size=literals.size();
  if(!sanity_check(literals,k,formula)) return false;
  // if size of G is less than k then
  // it is trivially true
  // add TRUE to the formula and return
  if(size<=k)
  {
    //this is trivially true so return an empty formula
    formula.clear();
    return true;
  }
  else if(k==0) return encodingt::atmostzero(literals,formula);
  else if(k==1) return atmostone(literals,formula);

  std::list<std::list<literalt> > subsets;

  subsets_k(literals,k+1,subsets);

  for(typename std::list<literalst>::iterator it=subsets.begin();
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

/****************************************************************************\
 *Function : commander_encodingt::atmostk

Input : literals, k , gsize

Output : formula

Purpose : Given a set of literals (x1...xn) generate <=k(x1...xn) constraints
in cnf form and store it in formula, gsize is a parameter used to subdivide
the problem into smaller problems
 *
 * **************************************************************************/
bool commander_encodingt::atmostk(const bvt& literals,
    unsigned int k, formulat& formula, unsigned int gsize)
{
  unsigned int size=literals.size();

  //group size should always be greater than k, termination
  //is not guaranteed otherwise
  //size has to be nonzero
  if(gsize<=k || !sanity_check(literals,k,formula)) return false;
  if(k==0) return encodingt::atmostzero(literals,formula);
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

    commanders.insert(commanders.begin(),gcommanders.begin(),
        gcommanders.end());
  }

  //recurse on commander variables
  formulat nformula;
  bool result=atmostk(commanders,k,nformula,gsize);
  if(!result) return result;
  formula.splice(formula.begin(),nformula);

  return true;


}
/*****************************************************************************\
 *
 * Function : commander_encodingt::atmostk
 *
 * Input : literals, k
 *
 * Output : true/false, formula
 *
 * Purpose : returns false on ill-formed input otherwise returns formula
 * that encodes <=k(x1...xn) using commander encoding (see paper reference
 * at the top of cardinality.h)
 *
 * NOTE : Use this version as public interface, other overloaded function
 * with parameter gsize is protected and not to be messed with
 *
 * WARNING : For non-trivial (very large) n = literals.size() and k
 * this does not scale well as it relies on binomial encoding of size
 * k+2 \choose k which could be huge for large k. Also, binomial encoding
 * in turn uses a recursive subset enumeration method
 * ***************************************************************************/
bool commander_encodingt::atmostk(const bvt& literals,
    unsigned int k,formulat& formula)
{

  // the paper "SAT Encodings of the At-most-k Constraint"
  //by Alan M Frisch and Paul A Giannaros suggests
  //k+2 to be a good choice for groupsize
  return atmostk(literals,k,formula,k+2);
}

/*****************************************************************************\
 * Function : sequential_encodingt::atmostk
 *
 * Input : literals, k
 *
 * Output : true/false, formula
 *
 * Purpose : use sequential encoding as mentioned in the paper (see the top of
 * cardinality.h) to encode atmostk constraints in the formula, return false
 * if inputs are ill-formed
 * ***************************************************************************/
bool sequential_encodingt::atmostk(const bvt& literals,
    unsigned int k,formulat& formula)
{
  // From the paper "SAT Encodings of the At-most-k Constraint"
  //by Alan M Frisch and Paul A Giannaros 

  bool result = sanity_check(literals,k,formula);
  if(!result) return result;

  unsigned int size=literals.size();

  if(k>=size) return true;
  unsigned int n=size;

  //literalt R[n-1][k]; allocating huge memory in stack segment gives fault
  // os use "new" operator to allocate R[n-1][k]
  literalt** R = new literalt*[n-1];
  for(unsigned int i=0;i<n-1;i++)
  {
	  R[i]=new literalt[k];
  }

  for(unsigned int i=0;i<n-1;i++)
  {
    for(unsigned int j=0;j<k;j++)
    {
      R[i][j]=prop.new_variable();
    }

  }

  bvt clause;

  //Formula(1) for i==0 from the paper
  clause.push_back(!literals[0]);
  clause.push_back(R[0][0]);
  formula.push_back(clause);
  clause.clear();

  //Formula(2) from the paper
  for(unsigned int j=1;j<k;j++)
  {
    clause.push_back(!R[0][j]);
    formula.push_back(clause);
    clause.clear();
  }


  //Formula(5) for i=n for the paper
  //The paper has a typo in Formula(5)
  // it should be \neg Xi \vee \neg Ri-1,k
  clause.push_back(!literals[n-1]);
  clause.push_back(!R[n-2][k-1]);
  formula.push_back(clause);
  clause.clear();


  for(unsigned int i=1;i<n-1;i++)
  {
    //Formula(1) for i==1 to n-1
    clause.push_back(!literals[i]);
    clause.push_back(R[i][0]);
    formula.push_back(clause);
    clause.clear();

    //Formula(3) for j==1
    clause.push_back(!R[i-1][0]);
    clause.push_back(R[i][0]);  
    formula.push_back(clause);
    clause.clear();

    for(unsigned int j=1;j<k;j++)
    {
      //Formula(3) for j==2 to k
      clause.push_back(!R[i-1][j]);
      clause.push_back(R[i][j]);
      formula.push_back(clause);
      clause.clear();

      //Formula(4)
      clause.push_back(!literals[i]);
      clause.push_back(!R[i-1][j-1]);
      clause.push_back(R[i][j]);
      formula.push_back(clause);
      clause.clear();

    }

    //Formula(5) for i==2 to n-1
    clause.push_back(!literals[i]);
    clause.push_back(!R[i-1][k-1]);
    formula.push_back(clause);
    clause.clear();

    //For Formula(5) case i==1 is covered by
    // Formula(2), besides for i==1, Ri-1,k is not
    // valid
  }

  //clean up the dynamically allocated memory
  for(unsigned int i=0;i<n-1;i++)
  {
	  delete R[i];
  }
  delete R;
  return true;

}
/*****************************************************************************\
 * Function : sequential_encoding_internalt::atmostk
 *
 * Input : literals, k
 *
 * Output : true/false, formula
 *
 * Purpose : use sequential encoding as mentioned in the paper (see the top of
 * cardinality.h) to encode atmostk constraints in the formula, return false
 * if inputs are ill-formed
 * ***************************************************************************/
bool sequential_encoding_internalt::atmostk(const bvt& literals,
    unsigned int k)
{
  // From the paper "SAT Encodings of the At-most-k Constraint"
  //by Alan M Frisch and Paul A Giannaros 
if(already_used) return false;
formulat tmp_formula;
  bool result = sanity_check(literals,k,tmp_formula);
  if(!result) return result;

  unsigned int size=literals.size();

  if(k>=size) return true;
  unsigned int n=size;
  //literalt R[n-1][k]; for large values of n and k seg fault occurs due to
  // stack segment limitation so allocate memory in heap using "new" operator

  literalt** R = new literalt*[n-1];
   for(unsigned int i=0;i<n-1;i++)
   {
 	  R[i]=new literalt[k];
   }

  for(unsigned int i=0;i<n-1;i++)
  {
    for(unsigned int j=0;j<k;j++)
    {
      R[i][j]=prop.new_variable();
    }

  }

  bvt clause;

  //Formula(1) for i==0 from the paper
  clause.push_back(!literals[0]);
  clause.push_back(R[0][0]);
  formula.push_back(clause);
  clause.clear();

  //Formula(2) from the paper
  for(unsigned int j=1;j<k;j++)
  {
    clause.push_back(!R[0][j]);
    formula.push_back(clause);
    clause.clear();
  }


  //Formula(5) for i=n for the paper
  //The paper has a typo in Formula(5)
  // it should be \neg Xi \vee \neg Ri-1,k
  clause.push_back(!literals[n-1]);
  clause.push_back(!R[n-2][k-1]);
  formula.push_back(clause);
  clause.clear();


  for(unsigned int i=1;i<n-1;i++)
  {
    //Formula(1) for i==1 to n-1
    clause.push_back(!literals[i]);
    clause.push_back(R[i][0]);
    formula.push_back(clause);
    clause.clear();

    //Formula(3) for j==1
    clause.push_back(!R[i-1][0]);
    clause.push_back(R[i][0]);  
    formula.push_back(clause);
    clause.clear();

    for(unsigned int j=1;j<k;j++)
    {
      //Formula(3) for j==2 to k
      clause.push_back(!R[i-1][j]);
      clause.push_back(R[i][j]);
      formula.push_back(clause);
      clause.clear();

      //Formula(4)
      clause.push_back(!literals[i]);
      clause.push_back(!R[i-1][j-1]);
      clause.push_back(R[i][j]);
      formula.push_back(clause);
      clause.clear();

    }

    //Formula(5) for i==2 to n-1
    clause.push_back(!literals[i]);
    clause.push_back(!R[i-1][k-1]);
    formula.push_back(clause);
    clause.clear();

    //For Formula(5) case i==1 is covered by
    // Formula(2), besides for i==1, Ri-1,k is not
    // valid

  }

  if(k>1)
  {
	  //Either we have already seen k "TRUE" literals or we have seen
	  // k-1 "TRUE" literals and the next one is also "TRUE"
    equi_lit = prop.lor(R[n-2][k-1],prop.land(literals[n-1],R[n-2][k-2]));
  }
  else
  {
	  //take care of boundary condition if k==1
    equi_lit = prop.lor(R[n-2][k-1],literals[n-1]);
  }
    already_used = true;
    //clean up the dynamically allocated memory
     for(unsigned int i=0;i<n-1;i++)
     {
   	  delete R[i];
     }
     delete R;
  return true;

}

bool sequential_encoding_internalt::atleastk(const bvt& literals,
    const unsigned int k)
{
	if(already_used) return false;
	formulat tmp_formula;
  if(!sanity_check(literals,k,tmp_formula)) return false;
  unsigned int size = literals.size();
  if(k==0)
  {
    //trivially true
    return true;
  }
  else if(size==k)
  {
    // if size==k it means that all the literals should be satisfied
    // so just AND them together
    for(bvt::const_iterator it=literals.begin();it!=literals.end();it++)
    {
      bvt clause;
      clause.push_back(*it);
      formula.push_back(clause);
    }
    equi_lit = encodingt::get_lit_for_formula(formula);
    already_used=true;
    return true;
  }

  else if(size > k)
  {

    bvt nliterals;
    for(bvt::const_iterator it=literals.begin();it!=literals.end();it++)
    {
      nliterals.push_back(!(*it));
    }

    return atmostk(nliterals,size-k);

  }
  else
  {
    formula.clear();
    already_used=true;
    return false;
  }
  already_used=true;
  return true;
}
bool sequential_encoding_internalt::exactlyk(const bvt& literals,
    const unsigned int k)
{
  if(!sanity_check(literals,k,formula)) return false;

  unsigned int size=literals.size();

  if(size==k)
  {
    return atleastk(literals,k);
  }
  else if(k > size)
  {
    formula.clear();
    already_used=true;
    return false;
  }

  bool result = false;


  result = atmostk(literals,k);
  literalt atmost_l = equi_lit;
// #ifdef DEBUG
//   std::cout << "At most formula.." << std::endl;
//   print_formula(std::cout);
// #endif
  already_used=false;

  result = result && atleastk(literals,k);
  literalt atleast_l=equi_lit;
// #ifdef DEBUG
//   std::cout << "Full formula.." << std::endl;
//   print_formula(std::cout);
// #endif

  equi_lit = prop.land(atmost_l,atleast_l);


  return result;

}

literalt sequential_encoding_internalt::get_lit_for_formula()
{
  bvt tmp_formula;

  for(formulat::iterator it=formula.begin();
      it!=formula.end();it++)
  {
    literalt l =prop.lor(*it);
    tmp_formula.push_back(l);

  }
  prop.land(tmp_formula);
  return equi_lit;

}


bool totalizer_encodingt::atmostk(const bvt& literals,unsigned int k,formulat& formula)
{
	if(!sanity_check(literals,k,formula)) return false;

	if(k==0) return encodingt::atmostzero(literals,formula);
	unsigned int size=literals.size();
	//if size==k nothing needs to be done
	if(size==k) return true;

	bvt oliterals;
	bool result=atmostk(k+1,literals,oliterals,formula);
	if(!result || oliterals.size()<=k) return false;

	//now implement the comparator

	bvt clause;
	clause.push_back(!oliterals[k]);
	formula.push_back(clause);

	return true;


}


bool totalizer_encodingt::exactlyk(const bvt& literals,unsigned int k, formulat& formula)
{
	if(!sanity_check(literals,k,formula)) return false;

	unsigned int size=literals.size();
    if(k==0) return encodingt::atmostzero(literals,formula);
	if(size==k) return encodingt::atleastk(literals,k,formula);
	if(size<k) return false;

    bvt oliterals;
    bool result=exactlyk(k+1,literals,oliterals,formula);
    if(!result || oliterals.size() <=k) return false;

    //comparator
//at least k
    for(unsigned int i=0;i<k;i++)
    {
    	bvt clause;
    	clause.push_back(oliterals[i]);
    	formula.push_back(clause);
    }
//at most k
    bvt clause;
    clause.push_back(!oliterals[k]);
    formula.push_back(clause);

    return true;
}

bool totalizer_encodingt::atleastk(const bvt& literals,unsigned int k,formulat& formula)
{
	if(!sanity_check(literals,k,formula)) return false;

	unsigned int size=literals.size();
	if(k==0) return true;
	if(k==1) return encodingt::atleastone(literals,formula);
	//if size==k nothing needs to be done
	if(size==k) return encodingt::atleastk(literals,k,formula);

	if(k>size) return false;

	bvt oliterals;
	//TODO : should we still pass k+1 for atleastk as well ? (lowerbound)
	bool result=atleastk(k+1,literals,oliterals,formula);
	if(!result || oliterals.size()<=k) return false;

	//now implement the comparator
for(unsigned int i=0;i<k;i++)
{
	bvt clause;
	clause.push_back(oliterals[i]);
	formula.push_back(clause);
}


	return true;


}
bool totalizer_encodingt::atmostk(unsigned int k,const bvt& iliterals, bvt& oliterals,formulat& formula)
{

  if(iliterals.size()==0 || k==0) return false;

	if(iliterals.size()==1)
  {
	  oliterals.push_back(iliterals.front());
	  return true;
  }

	unsigned int size=iliterals.size();

	formulat lformula,rformula;
	bvt linputs, rinputs;
	bvt loutputs,routputs;

	unsigned int lsize=size>>1;
	unsigned int rsize=size-lsize;
	bvt::const_iterator myit = iliterals.begin();
	bvt::const_iterator myit1=myit+lsize;
	bvt::const_iterator myit2=iliterals.end();

	linputs.insert(linputs.begin(),myit,myit1);
	rinputs.insert(rinputs.begin(),myit1,myit2);

	//since the totalizer sum is always upto k+1,
	//if lsize many input literals are passed, value of
	// k should be lsize-1
	unsigned int lk=k>=lsize?lsize:k;
	unsigned int rk=k>=rsize?rsize:k;

	bool result=atmostk(lk,linputs,loutputs,lformula);
	if(!result) return result;
	result = result && atmostk(rk,rinputs,routputs,rformula);
	if(!result) return result;

	// running sum has to be done for k (k+1 with respect to original call)
	for(unsigned int i=0;i<k;i++)
	{
		literalt l=prop.new_variable();
		oliterals.push_back(l);
	}


	for(unsigned int i=0;i<lk;i++)
	{
		for(unsigned int j=0;j<rk;j++)
		{
			if((i+j+2)<=k)
			{
				bvt clause;
				clause.push_back(!loutputs[i]);
				clause.push_back(!routputs[j]);
				clause.push_back(oliterals[i+j+1]);
				formula.push_back(clause);
			}
		}
	}

	for(unsigned int i=0;i<lk;i++)
	{
		bvt clause;
		clause.push_back(!loutputs[i]);
		clause.push_back(oliterals[i]);
		formula.push_back(clause);
	}

	for(unsigned int i=0;i<rk;i++)
	{
			bvt clause;
			clause.push_back(!routputs[i]);
			clause.push_back(oliterals[i]);
			formula.push_back(clause);
	}
// #ifdef DEBUG
// 	print_formula(std::cout,formula);
// #endif
#if 0
	//for cardinality-sum 1 to k+1
	for(unsigned int l=1;l<=k+1;l++)
	{
		for(unsigned int i=0;i<loutputs.size();i++)
		{

			if((l > (i+1)) && (routputs.size()>=(l-(i+1))))
			{
				bvt clause;
				clause.push_back(!loutputs[i]);

				clause.push_back(!routputs[l-(i+1)-1]);
				clause.push_back(oliterals[l-1]);
				formula.push_back(clause);
			}
			else if(l==(i+1))
			{
				bvt clause;
				clause.push_back(!loutputs[i]);
				clause.push_back(oliterals[i]);
				formula.push_back(clause);
			}
		}
	}


	//for cardinality-sum 1

	bvt clause;
	clause.push_back(!loutputs[0]);
	clause.push_back(oliterals[0]);
	formula.push_back(clause);

	clause.clear();
	clause.push_back(!routputs[0]);
	clause.push_back(oliterals[0]);
	formula.push_back(clause);

#endif
	if(lformula.size()>0)
	formula.splice(formula.begin(),lformula);
	if(rformula.size()>0)
	formula.splice(formula.begin(),rformula);
// #ifdef DEBUG
// 	print_formula(std::cout,formula);
// #endif
	return true;

}

bool totalizer_encodingt::atleastk(unsigned int k,const bvt& iliterals, bvt& oliterals,formulat& formula)
{

  if(iliterals.size()==0 || k==0) return false;

	if(iliterals.size()==1)
  {
	  oliterals.push_back(iliterals.front());
	  return true;
  }

	unsigned int size=iliterals.size();

	formulat lformula,rformula;
	bvt linputs, rinputs;
	bvt loutputs,routputs;

	unsigned int lsize=size>>1;
	unsigned int rsize=size-lsize;
	bvt::const_iterator myit = iliterals.begin();
	bvt::const_iterator myit1=myit+lsize;
	bvt::const_iterator myit2=iliterals.end();

	linputs.insert(linputs.begin(),myit,myit1);
	rinputs.insert(rinputs.begin(),myit1,myit2);

	unsigned int lk=k>=lsize?lsize:k;
	unsigned int rk=k>=rsize?rsize:k;

	bool result=atleastk(lk,linputs,loutputs,lformula);
	if(!result) return result;
	result = result && atleastk(rk,rinputs,routputs,rformula);
	if(!result) return result;

	//k output literals to ensure atleastk (k+1 wrt original call to atleastk)
	for(unsigned int i=0;i<k;i++)
	{
		literalt l=prop.new_variable();
		oliterals.push_back(l);
	}


	for(unsigned int i=0;i<lk;i++)
	{
		for(unsigned int j=0;j<rk;j++)
		{
			if((i+j)<(k))
			{
				bvt clause;
				clause.push_back(loutputs[i]);
				clause.push_back(routputs[j]);
				clause.push_back(!oliterals[i+j]);
				formula.push_back(clause);
			}
		}
	}

	//boundary condition
	for(unsigned int i=lk;i<k;i++)
	{
		bvt clause;
		clause.push_back(routputs[i-lk]);
		clause.push_back(!oliterals[i]);
		formula.push_back(clause);
	}

	for(unsigned int i=rk;i<k;i++)
	{
			bvt clause;
			clause.push_back(loutputs[i-rk]);
			clause.push_back(!oliterals[i]);
			formula.push_back(clause);
	}
// #ifdef DEBUG
// 	print_formula(std::cout,formula);
// #endif
#if 0
	//for cardinality-sum 1 to k+1
	for(unsigned int l=1;l<=k+1;l++)
	{
		for(unsigned int i=0;i<loutputs.size();i++)
		{

			if((l > (i+1)) && (routputs.size()>=(l-(i+1))))
			{
				bvt clause;
				clause.push_back(!loutputs[i]);

				clause.push_back(!routputs[l-(i+1)-1]);
				clause.push_back(oliterals[l-1]);
				formula.push_back(clause);
			}
			else if(l==(i+1))
			{
				bvt clause;
				clause.push_back(!loutputs[i]);
				clause.push_back(oliterals[i]);
				formula.push_back(clause);
			}
		}
	}


	//for cardinality-sum 1

	bvt clause;
	clause.push_back(!loutputs[0]);
	clause.push_back(oliterals[0]);
	formula.push_back(clause);

	clause.clear();
	clause.push_back(!routputs[0]);
	clause.push_back(oliterals[0]);
	formula.push_back(clause);

#endif
	if(lformula.size()>0)
	formula.splice(formula.begin(),lformula);
	if(rformula.size()>0)
	formula.splice(formula.begin(),rformula);
// #ifdef DEBUG
// 	print_formula(std::cout,formula);
// #endif
	return true;

}


bool totalizer_encodingt::exactlyk(unsigned int k,const bvt& iliterals, bvt& oliterals,formulat& formula)
{

  if(iliterals.size()==0 || k==0) return false;

  //for a single literal it is directly mapped to an output literal
	if(iliterals.size()==1)
  {
	  oliterals.push_back(iliterals.front());
	  return true;
  }

	unsigned int size=iliterals.size();


	//divide the input literals into two almost equivalent part
	formulat lformula,rformula;
	bvt linputs, rinputs;
	bvt loutputs,routputs;

	unsigned int lsize=size>>1;
	unsigned int rsize=size-lsize;
	bvt::const_iterator myit = iliterals.begin();
	bvt::const_iterator myit1=myit+lsize;
	bvt::const_iterator myit2=iliterals.end();

	linputs.insert(linputs.begin(),myit,myit1);
	rinputs.insert(rinputs.begin(),myit1,myit2);

	//limit the k passed to the child to min(k,childinputsize)
	unsigned int lk=k>=lsize?lsize:k;
	unsigned int rk=k>=rsize?rsize:k;


	//return false if any child nodes return false
	bool result=exactlyk(lk,linputs,loutputs,lformula);
	if(!result) return result;
	result = result && exactlyk(rk,rinputs,routputs,rformula);
	if(!result) return result;





	//k output literals to ensure exactlyk (k+1 wrt original call to exactlyk)
	for(unsigned int i=0;i<k;i++)
	{
		literalt l=prop.new_variable();
		oliterals.push_back(l);
	}


	for(unsigned int i=0;i<lk;i++)
		{
			for(unsigned int j=0;j<rk;j++)
			{
				if((i+j+2)<=k)
				{
					bvt clause;
					clause.push_back(!loutputs[i]);
					clause.push_back(!routputs[j]);
					clause.push_back(oliterals[i+j+1]);
					formula.push_back(clause);
				}
			}
		}

		for(unsigned int i=0;i<lk;i++)
		{
			bvt clause;
			clause.push_back(!loutputs[i]);
			clause.push_back(oliterals[i]);
			formula.push_back(clause);
		}

		for(unsigned int i=0;i<rk;i++)
		{
				bvt clause;
				clause.push_back(!routputs[i]);
				clause.push_back(oliterals[i]);
				formula.push_back(clause);
		}



	for(unsigned int i=0;i<lk;i++)
	{
		for(unsigned int j=0;j<rk;j++)
		{
			if((i+j)<(k))
			{
				bvt clause;
				clause.push_back(loutputs[i]);
				clause.push_back(routputs[j]);
				clause.push_back(!oliterals[i+j]);
				formula.push_back(clause);
			}
		}
	}
// #ifdef DEBUG
// 	print_formula(std::cout,formula);
// #endif
	//boundary condition
	for(unsigned int i=lk;i<k;i++)
	{
		bvt clause;
		clause.push_back(routputs[i-lk]);
		clause.push_back(!oliterals[i]);
		formula.push_back(clause);
	}

	for(unsigned int i=rk;i<k;i++)
	{
			bvt clause;
			clause.push_back(loutputs[i-rk]);
			clause.push_back(!oliterals[i]);
			formula.push_back(clause);
	}
// #ifdef DEBUG
// 	print_formula(std::cout,formula);
// #endif
#if 0
	//for cardinality-sum 1 to k+1
	for(unsigned int l=1;l<=k+1;l++)
	{
		for(unsigned int i=0;i<loutputs.size();i++)
		{

			if((l > (i+1)) && (routputs.size()>=(l-(i+1))))
			{
				bvt clause;
				clause.push_back(!loutputs[i]);

				clause.push_back(!routputs[l-(i+1)-1]);
				clause.push_back(oliterals[l-1]);
				formula.push_back(clause);
			}
			else if(l==(i+1))
			{
				bvt clause;
				clause.push_back(!loutputs[i]);
				clause.push_back(oliterals[i]);
				formula.push_back(clause);
			}
		}
	}


	//for cardinality-sum 1

	bvt clause;
	clause.push_back(!loutputs[0]);
	clause.push_back(oliterals[0]);
	formula.push_back(clause);

	clause.clear();
	clause.push_back(!routputs[0]);
	clause.push_back(oliterals[0]);
	formula.push_back(clause);

#endif

	//merge the formula returned by child nodes
	if(lformula.size()>0)
	formula.splice(formula.begin(),lformula);
	if(rformula.size()>0)
	formula.splice(formula.begin(),rformula);
// #ifdef DEBUG
// 	print_formula(std::cout,formula);
// #endif
	return true;

}
/*****************************************************************************
 *
 * Function : totalizer_encoding_iwt
 *
 * Input : prop, literals
 *
 * Output : None
 *
 *
 * Purpose : It's a constructor which constructs atmostk cardinality-sum
 * (CP 2014 paper "Incremental Cardinality Constraints for MaxSAT)
 * and sets the "status" to false if anything fails.
 *
 * If succeeds, the formula is already added to the solver.
 *
 *
 ****************************************************************************/
#if 0
totalizer_encoding_iwt::totalizer_encoding_iwt(propt& _prop,
		const bvt& literals,unsigned int _k): totalizer_encodingt(_prop),iliterals(literals)
{
	formulat formula;
	unsigned int size=iliterals.size();
	unsigned int k=(_k==0||size<=_k)?size:_k;
	status = sanity_check(iliterals,k,formula);
	if(!status) return;

	status=totalizer_encodingt::atmostk(k,iliterals,oliterals,formula);
	//assert(oliterals.size()==iliterals.size());
	assert(oliterals.size()==k);
	if(!status) return;
	add_to_prop(formula);
}

/*****************************************************************************
 *
 * Function : totalizer_encoding_iwt::atmostk
 *
 * Input : k
 *
 * Output : assumptions, true/false
 *
 * Purpose : Takes a value k and returns the set of assumptions that the
 * comparator (in the totalizer encoding) needs to enforce to achieve
 * atmostk constraints. The totalizer-sum encoding must have been
 * done by the constructor by the constructor.
 *
 * The assumptions must be added before the call to the solver by the
 * caller.
 *
 * If the status is false, it means there was an error in the constructor
 * and return false
 *
 * Return true if everything is fine.
 *
 ****************************************************************************/
bool totalizer_encoding_iwt::atmostk(unsigned int k, bvt& assumptions)
{
	if(k==0 || !status) return false;
	unsigned int size= oliterals.size();
	if(k>=iliterals.size()) return true;
	if(size!=iliterals.size() && k>=size) return false;

	for(unsigned int i=k;i<size;i++)
	{
		assumptions.push_back(!oliterals[i]);
	}

	return true;


}

totalizer_encoding_iet::totalizer_encoding_iet(propt& _prop,
		 const bvt& literals,unsigned int k):totalizer_encodingt(_prop),isize(literals.size())
{

	formulat formula;
	status=sanity_check(literals,k,formula);
	if(!status) return;
	if(k>=isize)
	{
		current_sum=isize;
		return;
	}
	root_node=new tot_tree_nodet;
	status=create_atmostk(k+1,literals,root_node,formula); //only create the running sum
	if(root_node->oliterals.size()!=k+1) status=false;
	if(status){ current_sum=k+1; add_to_prop(formula); }


}

bool totalizer_encoding_iet::atmostk(unsigned int k,bvt& assumptions)
{
	if(k==0||!status) return false;
    //unsigned int size=root_node->oliterals.size();
    if(k>=isize) return true;
    if(k >= current_sum)//need current_sum 1 higher than k
    {
    	formulat formula;
    	status=delta_atmostk(k+1,root_node,formula);

    			if(!status) return false;

    	current_sum=k+1;
    	add_to_prop(formula);

    }
    bvt::iterator it = root_node->oliterals.begin()+k;
    bvt::iterator it_end=root_node->oliterals.end();
    for(;it!=it_end;it++)
    {
    	assumptions.push_back(!(*it));
    	//prop.set_frozen((*it));
    }
    return true;

}
bool totalizer_encoding_iet::delta_atmostk(unsigned int k,childrent node,formulat& formula)
{
	//k here indicates the running sum required
	if(k==0 || !status) return false;

	if(k>isize) return false;
    if(node->left==NULL || node->right==NULL) return true; //we have reached a leaf

    //if the required encoding has already been done then return
    if(current_sum>=node->num_inputs) return true;


    tot_tree_nodet& lnode=(*node->left);
    tot_tree_nodet& rnode=(*node->right);
    unsigned int lk = (k>=lnode.num_inputs)?lnode.num_inputs:k;
    unsigned int rk=(k>=rnode.num_inputs)?rnode.num_inputs:k;
    formulat lformula,rformula;

    bool result = delta_atmostk(lk,node->left,lformula);
    if(!result) return false;
    result= result && delta_atmostk(rk, node->right,rformula);
    if(!result) return false;

    //add required extra oliterals
    for(unsigned int i=current_sum;i<k;i++)
    {
    	literalt l = prop.new_variable();
    	node->oliterals.push_back(l);
    	prop.set_frozen(l);
    }




    	for(unsigned int i=0;i<lk;i++)
        	{
        		for(unsigned int j=0;j<rk;j++)
        		{
        			if(((i+j+2)<=k) && (i+j+2)>current_sum)
        			{
        				bvt clause;
        				clause.push_back(!node->left->oliterals[i]);
        				clause.push_back(!node->right->oliterals[j]);
        				clause.push_back(node->oliterals[i+j+1]);
        				formula.push_back(clause);
        			}
        		}
        	}

        	for(unsigned int i=current_sum;i<lk;i++)
        	{
        		bvt clause;
        		clause.push_back(!node->left->oliterals[i]);
        		clause.push_back(node->oliterals[i]);
        		formula.push_back(clause);
        	}

        	for(unsigned int i=current_sum;i<rk;i++)
        	{
        			bvt clause;
        			clause.push_back(!node->right->oliterals[i]);
        			clause.push_back(node->oliterals[i]);
        			formula.push_back(clause);
        	}
        	if(lformula.size()>0)
        	formula.splice(formula.begin(),lformula);
        	if(rformula.size()>0)
        	formula.splice(formula.begin(),rformula);
    return true;
}
bool totalizer_encoding_iet::create_atmostk(unsigned int k,const bvt& iliterals, childrent node,formulat& formula)
{

  if(iliterals.size()==0 || k==0) return false;

	if(iliterals.size()==1)
  {

	  node->oliterals.push_back(iliterals.front());
	  node->num_inputs=1;
	  return true;
  }

	unsigned int size=iliterals.size();

	formulat lformula,rformula;
	bvt linputs, rinputs;
	bvt loutputs,routputs;

	unsigned int lsize=size>>1;
	unsigned int rsize=size-lsize;
	bvt::const_iterator myit = iliterals.begin();
	bvt::const_iterator myit1=myit+lsize;
	bvt::const_iterator myit2=iliterals.end();

	linputs.insert(linputs.begin(),myit,myit1);
	rinputs.insert(rinputs.begin(),myit1,myit2);

	//since the totalizer sum is always upto k+1,
	//if lsize many input literals are passed, value of
	// k should be lsize-1
	unsigned int lk=k>=lsize?lsize:k;
	unsigned int rk=k>=rsize?rsize:k;

	node->left=new tot_tree_nodet;
	node->right=new tot_tree_nodet;
	bool result=create_atmostk(lk,linputs,node->left,lformula);
	if(!result) return result;
	result = result && create_atmostk(rk,rinputs,node->right,rformula);
	if(!result) return result;

	// running sum has to be done for k (k+1 with respect to original call)
	for(unsigned int i=0;i<k;i++)
	{
		literalt l=prop.new_variable();
		node->oliterals.push_back(l);
		prop.set_frozen(l);
	}


	for(unsigned int i=0;i<lk;i++)
	{
		for(unsigned int j=0;j<rk;j++)
		{
			if((i+j+2)<=k)
			{
				bvt clause;
				clause.push_back(!node->left->oliterals[i]);
				clause.push_back(!node->right->oliterals[j]);
				clause.push_back(node->oliterals[i+j+1]);
				formula.push_back(clause);
			}
		}
	}

	for(unsigned int i=0;i<lk;i++)
	{
		bvt clause;
		clause.push_back(!node->left->oliterals[i]);
		clause.push_back(node->oliterals[i]);
		formula.push_back(clause);
	}

	for(unsigned int i=0;i<rk;i++)
	{
			bvt clause;
			clause.push_back(!node->right->oliterals[i]);
			clause.push_back(node->oliterals[i]);
			formula.push_back(clause);
	}
// #ifdef DEBUG
// 	print_formula(std::cout,formula);
// #endif
#if 0
	//for cardinality-sum 1 to k+1
	for(unsigned int l=1;l<=k+1;l++)
	{
		for(unsigned int i=0;i<loutputs.size();i++)
		{

			if((l > (i+1)) && (routputs.size()>=(l-(i+1))))
			{
				bvt clause;
				clause.push_back(!loutputs[i]);

				clause.push_back(!routputs[l-(i+1)-1]);
				clause.push_back(oliterals[l-1]);
				formula.push_back(clause);
			}
			else if(l==(i+1))
			{
				bvt clause;
				clause.push_back(!loutputs[i]);
				clause.push_back(oliterals[i]);
				formula.push_back(clause);
			}
		}
	}


	//for cardinality-sum 1

	bvt clause;
	clause.push_back(!loutputs[0]);
	clause.push_back(oliterals[0]);
	formula.push_back(clause);

	clause.clear();
	clause.push_back(!routputs[0]);
	clause.push_back(oliterals[0]);
	formula.push_back(clause);

#endif
	if(lformula.size()>0)
	formula.splice(formula.begin(),lformula);
	if(rformula.size()>0)
	formula.splice(formula.begin(),rformula);
// #ifdef DEBUG
// 	print_formula(std::cout,formula);
// #endif
	node->num_inputs = node->left->num_inputs + node->right->num_inputs;
	return true;

}

#endif
