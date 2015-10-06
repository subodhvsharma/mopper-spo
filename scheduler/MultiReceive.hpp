#ifndef __MULTIRECEIVE_HPP__
#define __MULTIRECEIVE_HPP__

#include "InterleavingTree.hpp"

class multiReceive {

public: 
  multiReceive(){}
  ~multiReceive(){}
  bool isPresent(CB a);
  bool isPresent(Envelope * env);
  void print();
  
public:
  std::list < std::pair < CB, CB> >receives;
};

#endif
