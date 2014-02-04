#ifndef __SPOENCODING_HPP__
#define __SPOENCODING_HPP__

#include "Encoding.hpp"

class SPOEncoding: public Encoding {
public:
  SPOEncoding(ITree *it, M *m, propt *_slv): Encoding(it, m, _slv), width(0), eventSize(0) {} 

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
  void generateConstraints();
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



#endif 
