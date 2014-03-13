
/*****************************************************************************\
 * Encodings presented here is from the paper
 * "SAT Encodings of the At-Most-k Constraint" by Alan M Frisch and
 * Paul A Giannaros
 */
#ifndef CPROVER_PROP_CARDINALITY_H
#define CPROVER_PROP_CARDINALITY_H


#include <prop.h>
#include <literal.h>
#include <vector>
#include <list>
#include<algorithm>


typedef std::list<bvt> formulat;
class  encodingt
{
	protected :
		//reference to prop must be passed so that valid auxiliary variables
		// can be created
		 propt& prop;
public :
		 encodingt(propt& _prop):prop(_prop){}

  /***************************************************************************\
   * Function : add_to_prop
   *
   * Input : prop, formula
   *
   * Output : prop
   *
   * Purpose : given a list of clause/bvt/vector of literals add it to the
   * solver prop
   *
   * This separate method is provided so that it does not force people to add
   * cardinality constraint/formula in the solver if they do not wish. All
   * other encoding methods just returns the formula without adding to a solver
   */
  virtual void add_to_prop(formulat& formula)
  {
    for(formulat::iterator it=formula.begin();
        it!=formula.end();it++)
    {
      prop.lcnf((*it));
    }
  }

  virtual void print_formula(std::ostream& out,formulat& formula)
  {
	  for(formulat::iterator it=formula.begin();
			  it!=formula.end();it++)
	  {
		  for(bvt::iterator bit=it->begin();
				  bit!=it->end();bit++)
		  {
			out << bit->dimacs() << " ";
		  }
		  out << std::endl;
	  }
  }

  virtual ~encodingt() {}
  /***************************************************************************\
   * Function : atmostk
   *
   * Input : literals, k
   *
   * Output : formula, true/false
   *
   * Purpose : encode the constraint <=k(literals) in formula
   *
   * Note that the input is a vector of literals (not variables). This means
   * for a vector (\neg a b \neg c) and k=1 the formula returned enforces that
   * at most one of the following is true (a==false,b==true,c==false) for a
   * satisfying assignment of the formula
   *
   * formulat is a cnf formula (list of vector of literals = conjunction of
   * disjunction of literals = conjunction of clauses)
   *
   * return valus is FALSE if improper input is given such as empty
   * set of literals
   */
  virtual bool atmostk(const bvt& literals,unsigned int k,formulat& formula)=0;


  virtual bool atmostone(const bvt& literals,formulat& formula)
  {
    if(literals.empty()) return false;
    return atmostk(literals,1,formula);
  }

  virtual bool atleastk(const bvt& literals,const unsigned int k,formulat& formula)
  {
    if(literals.empty()) return false;
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



  virtual bool atleastone(const bvt& literals,formulat&formula)
  {
    if(literals.empty()) return false;
    formula.clear();
    bvt clause;
    for(bvt::const_iterator it=literals.begin();it!=literals.end();it++)
    {
      clause.push_back(*it);
    }
     formula.push_back(clause);
     return true;

  }

  virtual bool exactlyk(const bvt& literals,const unsigned int k,formulat& formula)
  {
    if(literals.empty() || k==0) return false;

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

};



class commander_encodingt : public encodingt
{
public:
	commander_encodingt(propt& _prop):encodingt(_prop){}
  virtual bool atmostk(const bvt& literals,unsigned int k,
      formulat& formula);
protected:
  virtual bool atmostk(const bvt& literals,
      unsigned int k, formulat& formula, unsigned int gsize);

};

class binomial_encodingt : public encodingt
{
public:
binomial_encodingt(propt& _prop):encodingt(_prop){}
  virtual bool atmostk(const bvt& literals,unsigned int k,formulat& formula);
  virtual bool atmostone(const bvt& literals,formulat& formula);

};

template <class T>
void subsets_k(const std::vector<T>& v, const unsigned int k,
    std::list<std::list<T> >& subsets, std::list<T>& curr_set,
    const unsigned int index)
{
  if(k==0)
  {
    subsets.push_back(curr_set);
  }
  else
  {
    for(unsigned int i=index;i<=v.size()-k;i++)
    {
      curr_set.push_back(v[i]);
      subsets_k(v,k-1,subsets,curr_set,i+1);
      curr_set.pop_back();
    }
  }
}


/*****************************************************************************\
 * Function : subsets_k
 *
 * Input : v, k
 *
 * Output : subsets
 *
 * Purpose : given a set v and size k, in subsets return all subsets of v
 * of size k
 */
template <class T>
void subsets_k(const std::vector<T>& v,const unsigned int k,
    std::list<std::list<T> >& subsets)
{
  if(k==0)
  {
    subsets.clear();
    return;
  }
  else if(k>v.size())
  {
    subsets.clear();
    return;
  }
   std::list<T> curr_set;
   subsets_k(v,k,subsets,curr_set,0);
}

#endif
