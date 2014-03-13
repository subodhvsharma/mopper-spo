#include "BoolFile.hpp"

BStructure::BStructure()
{
  tracePosition = -1;
  matchList = -1;
  fpi = -1;
  spi = -1;
}

int BStructure::getTracePosition()
{
  return tracePosition;
}

int BStructure::getMatchList()
{
  return matchList;
}

int BStructure::getFpi()
{
  return fpi;
}

int BStructure::getSpi()
{
  return Spi;
}

void BStructure::setMatchList(int p)
{
  matchList = p;
}

void BStructure::setFpi(int p)
{
  fpi = p;
}

void BStructure::setSpi(int p)
{
  spi = p;
}

void BStructure::setTracePosition(int p)
{
  tracePosition = p;
}


bool operator==(BStructure b1, BStructure b2)
{
  return((b1.matchList == b2.matchList)
	 && (b1.tracePosition == b2.tracePostion));
}

