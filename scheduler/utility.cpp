#include<utility.hpp>

std::set<int> getImmediateAncestorList (Node *ncurr, int _pid, std::vector<int> &_list) 
{
  std::set<int>  _ancestor;
  //std::vector<int>& _tancestor;
  std::vector<int>::iterator _lit, _litend;
  _litend = _list.end();
  
  for(_lit = _list.begin(); _lit != _litend; _lit++) {
    Transition *_t = ncurr->GetTransition(_pid, *_lit);
    std::vector<int>::iterator it, itend;
    it = _t->get_ancestors().begin();   
    itend =_t->get_ancestors().end();
    for(; it != itend; it++) {
      int i = *it;
      _ancestor.insert(i);
    }
  }

  //std::cout << "Printing Ancestor List : [";
  //std::vector<int>::iterator sit, sit_end;
  //for(sit = _tancestor.begin(); sit != _tancestor.end(); sit++) {
  //  std::cout << *sit << ",";   
  //}
  //std::cout << "]\n";
  
  return _ancestor;
}

std::set<int> getAllAncestorList(Node *ncurr, CB c) 
{
  std::set<int> _allancestors, _iancestors;
  std::vector<int> _ilist;
  _ilist.push_back(c._index);
  unsigned int size;
    
  while(1){
    std::set<int>::iterator it, it_end;
    
    _iancestors = getImmediateAncestorList(ncurr, c._pid, _ilist);
    
    if(_iancestors.empty())
      break;
    
    it_end = _iancestors.end();
    _ilist.clear();
    
    for(it = _iancestors.begin(); it != it_end; it++) {
      _allancestors.insert(*it);
      _ilist.push_back(*it);
    }

  }

  // debug print
  //
  //std::set<int>::iterator it, itE;
  //itE = _allancestors.end();
  //std::cout << "All Ancestors of " << c << ": [ ";
  //for(it = _allancestors.begin(); it != itE; it++) {
  //  std::cout << *it << " " ;
  //}

  //std::cout << "]\n";
  
  return _allancestors;
}

std::set<int> getImmediateDescendantList (Node *ncurr, int _pid, std::vector<int> &_list)
{
  std::set<int> _descendant;
  
  std::vector<int>::iterator _it, _itend;
  _itend = _list.end();
  
  //std::cout << "In ImmediateDesc\n"<<"pid:" <<_pid <<std::endl ;
  
  for(_it = _list.begin(); _it != _itend; _it++) {
    Transition *_t = ncurr->GetTransition(_pid, *_it);
    std::vector<CB> _tdesc = _t->get_intra_cb();
    for(std::vector<CB>::iterator it = _tdesc.begin();
	it != _tdesc.end(); it++){
      _descendant.insert((*it)._index);	  
    }    
  }  
  return _descendant;
}

std::set<int> getAllDescendantList (Node *ncurr, CB c)
{
  std::set<int> _alldescendants, _idescendants;
  std::vector<int> _ilist;
  _ilist.push_back(c._index);
  unsigned int size;

  while(1) {
    std::set<int>::iterator it, it_end;
    
    _idescendants = getImmediateDescendantList(ncurr, c._pid, _ilist);
    
    if(_idescendants.empty())
      break;
    
    it_end = _idescendants.end();
    _ilist.clear();
    
    for(it = _idescendants.begin(); it != it_end; it++) {
      _alldescendants.insert(*it);
      _ilist.push_back(*it);
    }
  }

  // debug print
  //
  //std::set<int>::iterator it, itE;
  //itE = _alldescendants.end();
  //std::cout << "All Descendants of " << c << ": [ ";
  //for(it = _alldescendants.begin(); it != itE; it++) {
  //  std::cout << *it << " " ;
  //}

  //std::cout << "]\n";
   
  return _alldescendants;
}


void PrintStats (unsigned long total_time) {
  
  std::cout << "Total time = " << 
    (1.0* total_time)/1000000 << "sec \n";
	

}

unsigned long long getTimeElapsed (struct timeval first, 
				   struct timeval second) {
  unsigned long long secs;
  unsigned long long usecs = 0;

  if (first.tv_usec > second.tv_usec) {
    usecs = 1000000 - first.tv_usec + second.tv_usec;
    second.tv_sec--;
  } else {
    usecs = second.tv_usec - first.tv_usec;
  }
  secs = (second.tv_sec - first.tv_sec);
  secs *= 1000000;
  return (secs + usecs);
}


//////////////////////////////////////////////////////////////////////////////
//
// process_mem_usage(double &, double &) - takes two doubles by reference,
// attempts to read the system-dependent data for a process' virtual memory
// size and resident set size, and return the results in KB.
//
// On failure, returns 0.0, 0.0

void process_mem_usage(double& vm_usage, double& resident_set)
{
   using std::ios_base;
   using std::ifstream;
   using std::string;

   vm_usage     = 0.0;
   resident_set = 0.0;

   // 'file' stat seems to give the most reliable results
   //
   ifstream stat_stream("/proc/self/stat",ios_base::in);

   // dummy vars for leading entries in stat that we don't care about
   //
   string pid, comm, state, ppid, pgrp, session, tty_nr;
   string tpgid, flags, minflt, cminflt, majflt, cmajflt;
   string utime, stime, cutime, cstime, priority, nice;
   string O, itrealvalue, starttime;

   // the two fields we want
   //
   unsigned long vsize;
   long rss;

   stat_stream >> pid >> comm >> state >> ppid >> pgrp >> session >> tty_nr
               >> tpgid >> flags >> minflt >> cminflt >> majflt >> cmajflt
               >> utime >> stime >> cutime >> cstime >> priority >> nice
               >> O >> itrealvalue >> starttime >> vsize >> rss; // don't care about the rest

   stat_stream.close();

   long page_size_kb = sysconf(_SC_PAGE_SIZE) / 1024; // in case x86-64 is configured to use 2MB pages
   vm_usage     = vsize / 1024.0;
   resident_set = rss * page_size_kb;
}

//    double vm, rss;
//    process_mem_usage(vm, rss);
//    cout << "VM: " << vm << "; RSS: " << rss << endl;

/*
 * Author:  David Robert Nadeau
 * Site:    http://NadeauSoftware.com/
 * License: Creative Commons Attribution 3.0 Unported License
 *          http://creativecommons.org/licenses/by/3.0/deed.en_US
 */

#if defined(_WIN32)
#include <windows.h>
#include <psapi.h>

#elif defined(__unix__) || defined(__unix) || defined(unix) || (defined(__APPLE__) && defined(__MACH__))
#include <unistd.h>
#include <sys/resource.h>

#if defined(__APPLE__) && defined(__MACH__)
#include <mach/mach.h>

#elif (defined(_AIX) || defined(__TOS__AIX__)) || (defined(__sun__) || defined(__sun) || defined(sun) && (defined(__SVR4) || defined(__svr4__)))
#include <fcntl.h>
#include <procfs.h>

#elif defined(__linux__) || defined(__linux) || defined(linux) || defined(__gnu_linux__)
#include <stdio.h>

#endif

#else
#error "Cannot define getPeakRSS( ) or getCurrentRSS( ) for an unknown OS."
#endif


/**
 * Returns the peak (maximum so far) resident set size (physical
 * memory use) measured in bytes, or zero if the value cannot be
 * determined on this OS.
 */
size_t getPeakRSS( )
{
#if defined(_WIN32)
    /* Windows -------------------------------------------------- */
    PROCESS_MEMORY_COUNTERS info;
    GetProcessMemoryInfo( GetCurrentProcess( ), &info, sizeof(info) );
    return (size_t)info.PeakWorkingSetSize;

#elif (defined(_AIX) || defined(__TOS__AIX__)) || (defined(__sun__) || defined(__sun) || defined(sun) && (defined(__SVR4) || defined(__svr4__)))
    /* AIX and Solaris ------------------------------------------ */
    struct psinfo psinfo;
    int fd = -1;
    if ( (fd = open( "/proc/self/psinfo", O_RDONLY )) == -1 )
        return (size_t)0L;      /* Can't open? */
    if ( read( fd, &psinfo, sizeof(psinfo) ) != sizeof(psinfo) )
    {
        close( fd );
        return (size_t)0L;      /* Can't read? */
    }
    close( fd );
    return (size_t)(psinfo.pr_rssize * 1024L);

#elif defined(__unix__) || defined(__unix) || defined(unix) || (defined(__APPLE__) && defined(__MACH__))
    /* BSD, Linux, and OSX -------------------------------------- */
    struct rusage rusage;
    getrusage( RUSAGE_SELF, &rusage );
#if defined(__APPLE__) && defined(__MACH__)
    return (size_t)rusage.ru_maxrss;
#else
    return (size_t)(rusage.ru_maxrss * 1024L);
#endif

#else
    /* Unknown OS ----------------------------------------------- */
    return (size_t)0L;          /* Unsupported. */
#endif
}

/**
 * Returns the current resident set size (physical memory use) measured
 * in bytes, or zero if the value cannot be determined on this OS.
 */
size_t getCurrentRSS( )
{
#if defined(_WIN32)
    /* Windows -------------------------------------------------- */
    PROCESS_MEMORY_COUNTERS info;
    GetProcessMemoryInfo( GetCurrentProcess( ), &info, sizeof(info) );
    return (size_t)info.WorkingSetSize;

#elif defined(__APPLE__) && defined(__MACH__)
    /* OSX ------------------------------------------------------ */
    struct mach_task_basic_info info;
    mach_msg_type_number_t infoCount = MACH_TASK_BASIC_INFO_COUNT;
    if ( task_info( mach_task_self( ), MACH_TASK_BASIC_INFO,
        (task_info_t)&info, &infoCount ) != KERN_SUCCESS )
        return (size_t)0L;      /* Can't access? */
    return (size_t)info.resident_size;

#elif defined(__linux__) || defined(__linux) || defined(linux) || defined(__gnu_linux__)
    /* Linux ---------------------------------------------------- */
    long rss = 0L;
    FILE* fp = NULL;
    if ( (fp = fopen( "/proc/self/statm", "r" )) == NULL )
        return (size_t)0L;      /* Can't open? */
    if ( fscanf( fp, "%*s%ld", &rss ) != 1 )
    {
        fclose( fp );
        return (size_t)0L;      /* Can't read? */
    }
    fclose( fp );
    return (size_t)rss * (size_t)sysconf( _SC_PAGESIZE);

#else
    /* AIX, BSD, Solaris, and Unknown OS ------------------------ */
    return (size_t)0L;          /* Unsupported. */
#endif
}
