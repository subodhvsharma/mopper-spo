#include "cardinality.h"
#include <cmath>
#include<algorithm>
#include <iterator>
#ifdef DEBUG
#include <iostream>
#endif

typedef std::list<literalt> literalst;
#ifdef DEBUG
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
/***************************************************************************\
 * Function : encodingt::get_lit_for_formula
 *
 * Input : formula
 *
 * Output : literal
 *
 * Purpose : given a list of clause/bvt/vector of literals add it to the
 * solver prop and return an equisatisfiable literal
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
  return prop.land(tmp_formula);

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
 * use !l in set_assumptions when the formula need not be satisfiable.
 *
 * NOTE : l is not equisatisfiable to the formula
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
  literalt R[n-1][k];

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

  return true;

}
