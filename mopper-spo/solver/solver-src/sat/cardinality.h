
/*****************************************************************************\
 * Encodings presented here is from the paper
 * "SAT Encodings of the At-Most-k Constraint" by Alan M Frisch and
 * Paul A Giannaros
 */
#ifndef CPROVER_PROP_CARDINALITY_H
#define CPROVER_PROP_CARDINALITY_H


#include "prop.h"
#include "literal.h"
#include <vector>
#include <list>
#include<algorithm>
#include <set>
#include <iterator>
#ifdef DEBUG
#include<iostream>
#endif

typedef std::list<bvt> formulat;
class  encodingt
{
  protected :
    //reference to prop must be passed so that valid auxiliary variables
    // can be created
    propt& prop;
  public :
    encodingt(propt& _prop):prop(_prop){}

    virtual void add_to_prop(formulat& formula);
    virtual literalt get_lit_for_formula(formulat& formula);
    virtual literalt get_enabling_lit_for_formula(formulat& formula);
    /*****************************************************************************\
     * Function : encodingt::sanity_check
     *
     * Input : literals, k, formula
     *
     * OUtput : true/false
     *
     * Purpose : Ensure that set os literals are not empty or k!=0
     * Also the literals provided should all come from different variables
     * ***************************************************************************/
    virtual bool sanity_check(const bvt& literals,const unsigned int k,formulat& formula)
    {
      unsigned int size=literals.size();
      formula.clear();
      if(size==0 || k==0) return false;

      std::set<unsigned int> tmpset;

      for(bvt::const_iterator it=literals.begin();it!=literals.end();it++)
      {
        //given set of literals should all belong to different variables
        //if a variable repeats then return false  
        if(!tmpset.insert(it->var_no()).second) return false;
      }  
      return true;
    }
#ifdef DEBUG
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
#endif

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
    virtual bool atmostk(const bvt& literals,
        unsigned int k,formulat& formula)=0;


    virtual bool atmostone(const bvt& literals,formulat& formula)
    {
      if(!sanity_check(literals,1,formula)) return false;
      return atmostk(literals,1,formula);
    }
    virtual bool atleastk(const bvt& literals,
        const unsigned int k,formulat& formula);

    virtual bool atleastone(const bvt& literals,formulat&formula);

    virtual bool exactlyk(const bvt& literals,const unsigned int k,formulat& formula);

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
    virtual bool atmostk(const bvt& literals,unsigned int k,
        formulat& formula);
    virtual bool atmostone(const bvt& literals,formulat& formula);

};


class sequential_encodingt : public encodingt
{
  public:
    sequential_encodingt(propt& _prop):encodingt(_prop){}
    virtual bool atmostk(const bvt& literals,unsigned int k,
        formulat& formula);
};

/*****************************************************************************\
 * Function : subsets_k
 *
 * Input : v,k,curr_set
 *
 * OUtput : subsets
 *
 * Purpose : Given the universe v, size k and curr_set
 * add to subsets if we have constructed a subset of v of size k
 *
 * otherwise use recursive back-tracking to construct curr_set with
 * different elements of v one-by-one
 * ***************************************************************************/
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
