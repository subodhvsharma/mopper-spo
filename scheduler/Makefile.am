CC = @CXX@
AM_LDFLAGS = -pthread  $(LIBOPTS_LDADD)
if COND_STATIC_LINK
  AM_LDFLAGS += -static ../solver/solver-src/solvers.a ../solver/big-int/big-int.a 
endif
AM_CXXFLAGS =  -DHAVE_STDINT_H -Wall $(LIBOPTS_CFLAGS) -O2
AM_CFLAGS = -DHAVE_STDINT_H -Wall $(LIBOPTS_CFLAGS) -O2 
#//-O2
INCLUDES = -I ../solver
bin_PROGRAMS = isp.exe
isp_exe_SOURCES = Socket.cpp ServerSocket.cpp MpiProc.cpp Envelope.cpp \
                  name2id.cpp  Scheduler.cpp  Counter.cpp Transition.cpp TransitionList.cpp \
                  InterleavingTree.cpp utility.cpp Mo.cpp Wu.cpp Encoding.cpp sched-opt.c main.cpp












