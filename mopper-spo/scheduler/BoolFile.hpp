#ifndef __BOOL_FILE__
#define __BOOL_FILE__

class BStructure{
public:
  BStructure();
  ~BStructure();
  
  int  getTracePosition();
  int getmatchList();
  int getFpi();
  int getSpi();
  void setMatchList(int); 
 void setFpi(int);
  void setSpi(int);
  void setTracePosition(int);
  friend bool  operator==(BStructure b1, BStructure b2);
public:
  /*
    for finalize op == tracePosition is a fixed constant 
    for all other ops .. tracePosition is a range from 0 to tracePosition
   */
  int tracePosition;
  int matchList; // sequence of X_p1i1p2i1 .... where pjij is pid and index id
  int fpi, spi;
};

#endif
