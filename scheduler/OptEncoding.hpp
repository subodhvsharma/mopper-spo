#ifndef __OptENCODING_HPP__
#define __OptENCODING_HPP__

#include "Encoding.hpp"
#include "MultiReceive.hpp"
class OptEncoding : public Encoding {
  
public:
  OptEncoding(ITree *it, M *m, propt *_slv): Encoding(it, m, _slv), width(0), eventSize(0) {} 
 
  void discoverMultiReceives();
  void construct_multirecv_match(bvt &rhs, Envelope *env); 
  void construct_nonmultirecv_match(bvt &rhs, Envelope *env); 
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
  void isLitCreatedForCollEvent(CB, literalt &);

  void encodingPartialOrders();
  void generateConstraints();

  void insertClockEntriesInMap(CB, CB, literalt);

  //constraint generation functions
  void createClkLiterals();  // partial order constraint + clock differenc
  void createRFSomeConstraint(); // Match correct
  void createMatchConstraint();//Matched Only
  void uniqueMatchSend();// unique match for send constraint
  void uniqueMatchRecv(); // unique match for recv constraint
  void noMoreMatchesPossible(); // No more matches possible
  void alternateAllAncestorsMatched(); // All ancestors matched  
  void notAllMatched(); // not all matched
  void matchImpliesIssued();// match only  issued
  void createRFConstraint(); // clock equality
  void waitMatch(); // matches when waits have 

#if 0  
  void createSerializationConstraint();
  void createFrConstraint();
  void createUniqueMatchConstraint();
  void alternativeUniqueMatchConstraint();
  void allFstIssued();
  void transitiveConstraint();
  void allAncestorsMatched();
  void totalOrderOnSends();
  void totalOrderOnRacingSends();
  void nonOverTakingMatch();
  void makingMatchesHappenSooner();
#endif

  //printing
  void printEventMap();
  void publish();
  

  // bitvector related functions
  void set_width();
  unsigned get_width();
  void create_bv(bvt &);
  unsigned address_bits();
  
public:
  multiReceive multiRs;

  std::map<literalt, CB> revEventMap;
  std::map<CB, std::pair<literalt, literalt> > eventMap;

  std::map<literalt, MatchPtr> revCollMap;
  std::map<MatchPtr,std::pair<literalt, literalt> > collEventMap;

  std::map<std::string, literalt> matchMap;
  std::map<literalt, std::string> revMatchMap;
  std::map<MatchPtr, std::string> match2symMap;

  std::map<std::string, literalt> matchMap_MultiRecv;
  std::map<literalt, std::string> revMatchMap_MultiRecv;
  std::map<CB, std::set<literalt> > match2symMap_MultiRecv;

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
