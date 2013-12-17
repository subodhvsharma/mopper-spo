#ifndef __ENCODING_HPP__
#define __ENCODING_HPP__

#include "Mo.hpp"
#include "InterleavingTree.hpp"
#include <map>
#include "utility.hpp"
#include "solver-src/flattening/bv_utils.h"
#include <solver-src/sat/satcheck_minisat2.h>

typedef std::list<CB> * MatchPtr; 
typedef std::list<CB>  Match; 

typedef std::pair<std::string, int> StrIntPair;

typedef std::vector<MatchPtr>::iterator MIter;
typedef Match::iterator LIter;

typedef std::vector<TransitionList *>::iterator TLIter;
typedef std::vector<Transition>::iterator TIter;

typedef satcheck_minisat_no_simplifiert satcheckt;
typedef satcheck_minisat_simplifiert satcheck_simplifiert;

#define forall_matchSet(it, MT) \
  for (MIter it = MT.begin(), it_end = MT.end(); \
       it != it_end; it++)

#define forall_match(it, M)			 \
  for (LIter it = M.begin(), it_end = M.end(); \
       it != it_end; it++)


#define forall_transitionLists(it, TL) \
  for (TLIter it = TL.begin(), it_end = TL.end(); \
       it != it_end; it++) 

#define forall_transitions(it, T) \
  for (TIter it = T.begin(), it_end = T.end(); \
       it != it_end; it++)

class Encoding{
public:
  //  Encoding();
  Encoding(ITree *it, M *m); 
  ~Encoding(){}

  virtual std::string getLitName(literalt a);
  void createMatchSet();  
  void printMatchSet();
  
  Node* last_node; 
  int traceSize;
  M* _m;
  ITree *_it; 
  literalt one, zero;  
  //satcheckt slv;
  satcheck_simplifiert  slv;
  bv_utilst bvUtils;  
  std::vector<MatchPtr> matchSet;
  std::map<StrIntPair, literalt> sym2lit; 
  std::map<literalt, StrIntPair > lit2sym; 
  bool _deadlock_found;
  struct timeval constGenStart, constGenEnd, solverStart, solverEnd;
};

class Encoding0 : public Encoding{
public: 
  Encoding0(ITree *it, M *m): Encoding(it, m) {} 
  
  //main encoding function
  void Encoding_Matches();
  
  // helper functions for Encoding_Matches
  literalt uniqueAtPosition();
  literalt noRepetition ();
  literalt partialOrder();
  literalt extensionNextPos();
  literalt noMatchAtNextPos();
  

  literalt uniqueEvents();
  literalt noRepetitionEvents();
  literalt partialOrderEvents();
  literalt extentionEvents();
  literalt noMatchEvents();
  
  //helper functions
  void createMatchLiterals(); 
  literalt getLiteralFromMatches(MatchPtr, int);

  //  IntPair getMatchNumeralPositionFromMatches(MatchPtr, int);

  void publish();

protected: 
  std::multimap<MatchPtr, StrIntPair > match2sym; // symbol:= (match, pos)
};

class Encoding1 : public Encoding{

public:
  Encoding1(ITree *it, M *m): Encoding(it, m) {} 

  
  //main encoding function
  void Encoding_Events();
  
  // helper functions for Encoding_Matches
  void stutteringAtPosition();
  void uniqueAtPosition();
  void noRepetition ();
  void partialOrder();
  void extensionNextPos();
  void noMatchAtNextPos();

  // general helper functions
  void createEventLiterals();
  literalt getLiteralFromEvents(TIter, int);
  literalt getLiteralFromCB(CB, int);
  void publish();
};

class Encoding2 : public Encoding {
public:
  Encoding2(ITree *it, M *m): Encoding(it, m) {} 

  
  //main encoding function
  void Encoding_Mixed();
  
  // helper functions for Encoding_Matches
  void stutteringAtPosition();
  void uniqueAtPosition();
  void noRepetition ();
  void partialOrder();
  void extensionNextPos();
  void noMatchAtNextPos();

  void createMatchLiterals(); 
  void createEventLiterals();
  void createBVEventLiterals();

  literalt getLiteralFromEvents(TIter, int);
  literalt getLiteralFromMatches(MatchPtr, int);
  literalt getLiteralFromCB(CB, int);
  MatchPtr getMatchPtrFromEvent(CB a);
  void publish();
protected: 
  std::multimap<MatchPtr, StrIntPair > match2sym; // symbol:= (match, pos)
  };

class poEncoding: public Encoding {
public:
  poEncoding(ITree *it, M *m): Encoding(it, m), width(0), eventSize(0) {} 

  // bitvector related functions
  void set_width();
  unsigned get_width();
  unsigned address_bits();

  void createPossibleMatches();
  void createMatchLiterals();
  literalt getMatchLiteral(MatchPtr mptr);
  void createFinalizeWaitLiterals();
  literalt getFinalizeWaitLiterals(CB f);
  void createBVLiterals();
  bvt getBVLiterals(CB A); 
  MatchPtr getMPtr(CB a);
    
  // helper functions for Encoding_Matches
  void init();
  void ext();
  void dlock();
  void m2Clk();
  void processPO();
  literalt predsMatched(CB q);
  literalt exclusive(CB q, MatchPtr m);

  std::string getLitName(literalt lt, int type);
  void publish();
  //main encoding function
  void poEnc();
  

protected: 
  unsigned width; 
  unsigned eventSize; 
  std::map<std::string, literalt> matchMap;
  std::map<literalt, std::string> revMatchMap;
  std::map<MatchPtr, std::string> match2symMap;

  std::map<literalt, CB> revEventMap;
  std::map<CB, literalt> eventMap;

  std::map<CB, bvt> bvEventMap;
  std::map<bvt, CB> revBVEventMap;
  std::map<MatchPtr, bvt> collBVMap;
  std::map<bvt, MatchPtr> revCollBVMap;
  
};


class Encoding3 : public Encoding {
  
public:
  Encoding3(ITree *it, M *m): Encoding(it, m), width(0), eventSize(0) {} 
  
  //creation of literals m_a, i_a,
  // and bitvectors for maintaining clocks
  void createEventLiterals();
  void createMatchLiterals();
  void createBVEventLiterals();

  literalt getClkLiteral(CB, CB);
  std::pair<literalt, literalt> getMILiteral(CB);
  literalt getMatchLiteral(MatchPtr);
  std::string getLitName(literalt, int);
  std::string getClkLitName(literalt, CB, CB);
  bvt getEventBV(CB);
  MatchPtr getMPtr(CB);
  
  void insertClockEntriesInMap(CB, CB, literalt);

  //constraint generation functions
  void createClkLiterals();
  void createRFConstraint();
  void createSerializationConstraint();
  void createRFSomeConstraint();
  void createMatchConstraint();
  void createFrConstraint();
  void createUniqueMatchConstraint();
  void alternativeUniqueMatchConstraint();
  void uniqueMatchSend();
  void uniqueMatchRecv();
  void allFstIssued();
  void noMoreMatchesPossible();
  void transitiveConstraint();
  void allAncestorsMatched();
  void alternateAllAncestorsMatched();
  void totalOrderOnSends();
  void totalOrderOnRacingSends();
  void matchImpliesIssued();
  void waitMatch();
  void nonOverTakingMatch();
  void notAllMatched();
  void encodingPartialOrders();
  void makingMatchesHappenSooner();
  //printing
  void printEventMap();
  void publish();
  

  // bitvector related functions
  void set_width();
  unsigned get_width();
  void create_bv(bvt &);
  unsigned address_bits();
  
public:


  std::map<literalt, CB> revEventMap;
  std::map<CB, std::pair<literalt, literalt> > eventMap;

  std::map<literalt, MatchPtr> revCollMap;
  std::map<MatchPtr,std::pair<literalt, literalt> > collEventMap;

  std::map<std::string, literalt> matchMap;
  std::map<literalt, std::string> revMatchMap;
  std::map<MatchPtr, std::string> match2symMap;

  std::map<literalt, std::pair<CB, CB> > revClkMap;
  std::map<std::pair<CB, CB>, literalt > clkMap; 

  std::map<literalt, std::pair<MatchPtr, CB> > revClkMapCollEvent;
  std::map<std::pair<MatchPtr, CB>, literalt > clkMapCollEvent; 
  
  std::map<literalt, std::pair<CB, MatchPtr> > revClkMapEventColl;
  std::map<std::pair<CB, MatchPtr>, literalt > clkMapEventColl; 
  
  std::map<literalt, std::pair<MatchPtr, MatchPtr> > revClkMapCollColl;
  std::map<std::pair<MatchPtr, MatchPtr>, literalt > clkMapCollColl; 

  std::map<CB, bvt> bvEventMap;
  std::map<bvt, CB> revBVEventMap;
  
  std::map<MatchPtr, bvt> collBVMap;
  std::map<bvt, MatchPtr> revCollBVMap;
  
  unsigned width; 
  unsigned eventSize; 
 };


#endif
