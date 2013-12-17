/*   -*- buffer-read-only: t -*- vi: set ro:
 *  
 *  DO NOT EDIT THIS FILE   (sched-opt.c)
 *  
 *  It has been AutoGen-ed  August 13, 2013 at 04:32:40 PM by AutoGen 5.11.1
 *  From the definitions    sched-opt.def
 *  and the template file   options
 *
 * Generated from AutoOpts 33:2:8 templates.
 *
 *  AutoOpts is a copyrighted work.  This source file is not encumbered
 *  by AutoOpts licensing, but is provided under the licensing terms chosen
 *  by the isp author or copyright holder.  AutoOpts is
 *  licensed under the terms of the LGPL.  The redistributable library
 *  (``libopts'') is licensed under the terms of either the LGPL or, at the
 *  users discretion, the BSD license.  See the AutoOpts and/or libopts sources
 *  for details.
 *
 * This source file is copyrighted and licensed under the following terms:
 *
 * isp copyright (c) 1-27-2009 University of Utah - all rights reserved
 *
 * Copyright (C) 2009 -- please see LICENSE for details.
 */

#include <sys/types.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
extern FILE * option_usage_fp;
#define OPTION_CODE_COMPILE 1
#include "sched-opt.h"

#ifdef  __cplusplus
extern "C" {
#endif

/* TRANSLATORS: choose the translation for option names wisely because you
                cannot ever change your mind. */
tSCC zCopyright[] =
       "isp copyright (c) 1-27-2009 University of Utah, all rights reserved"
/* extracted from sched-opt.def near line 10 */
;
tSCC zCopyrightNotice[54] =
"Copyright (C) 2009 -- please see LICENSE for details.";

extern tUsageProc optionUsage;

#ifndef NULL
#  define NULL 0
#endif
#ifndef EXIT_SUCCESS
#  define  EXIT_SUCCESS 0
#endif
#ifndef EXIT_FAILURE
#  define  EXIT_FAILURE 1
#endif

/*
 *  Numprocs option description:
 */
static char const zNumprocsText[] =
        "Number of processes";
static char const zNumprocs_NAME[]           = "NUMPROCS";
static char const zNumprocs_Name[]           = "numprocs";
#define zNumprocsDefaultArg          ((char const*)2)
#define NUMPROCS_FLAGS       (OPTST_DISABLED \
        | OPTST_SET_ARGTYPE(OPARG_TYPE_NUMERIC))

/*
 *  Encoding option description:
 */
static char const zEncodingText[] =
        "SAT encoding type";
static char const zEncoding_NAME[]           = "ENCODING";
static char const zEncoding_Name[]           = "encoding";
#define zEncodingDefaultArg          ((char const*)0)
#define ENCODING_FLAGS       (OPTST_DISABLED \
        | OPTST_SET_ARGTYPE(OPARG_TYPE_NUMERIC))

/*
 *  Port option description:
 */
static char const zPortText[] =
        "Listening port";
static char const zPort_NAME[]               = "PORT";
static char const zPort_Name[]               = "port";
#define zPortDefaultArg              ((char const*)9999)
#define PORT_FLAGS       (OPTST_DISABLED \
        | OPTST_SET_ARGTYPE(OPARG_TYPE_NUMERIC))

/*
 *  Host option description:
 */
static char const zHostText[] =
        "Hostname where ISP resides";
static char const zHost_NAME[]               = "HOST";
static char const zHost_Name[]               = "host";
static char const zHostDefaultArg[]            = "localhost";
#define HOST_FLAGS       (OPTST_DISABLED \
        | OPTST_SET_ARGTYPE(OPARG_TYPE_STRING))

/*
 *  Us option description:
 */
#ifndef WIN_32
static char const zUsText[] =
        "Use unix sockets";
static char const zUs_NAME[]                 = "US";
static char const zUs_Name[]                 = "us";
#define US_FLAGS       (OPTST_DISABLED)

#else   /* disable Us */
#define US_FLAGS       (OPTST_OMITTED | OPTST_NO_INIT)
#define zUs_NAME      NULL
#define zUsText       NULL
#define zUs_Name      NULL
#endif  /* WIN_32 */

/*
 *  Block option description with
 *  "Must also have options" and "Incompatible options":
 */
static char const zBlockText[] =
        "Treat sends as blocking w/o buffering";
static char const zBlock_NAME[]              = "BLOCK";
static char const zBlock_Name[]              = "block";
static const int
    aBlockCantList[] = {
    INDEX_OPT_NOBLOCK, NO_EQUIVALENT };
#define BLOCK_FLAGS       (OPTST_DISABLED)

/*
 *  Noblock option description with
 *  "Must also have options" and "Incompatible options":
 */
static char const zNoblockText[] =
        "Sends use buffering of MPI subsystem (default)";
static char const zNoblock_NAME[]            = "NOBLOCK";
static char const zNoblock_Name[]            = "noblock";
static const int
    aNoblockCantList[] = {
    INDEX_OPT_BLOCK, NO_EQUIVALENT };
#define NOBLOCK_FLAGS       (OPTST_DISABLED)

/*
 *  Logfile option description:
 */
static char const zLogfileText[] =
        "Location of interleaving log for UI";
static char const zLogfile_NAME[]            = "LOGFILE";
static char const zLogfile_Name[]            = "logfile";
#define LOGFILE_FLAGS       (OPTST_DISABLED \
        | OPTST_SET_ARGTYPE(OPARG_TYPE_STRING))

/*
 *  Mpicalls option description:
 */
static char const zMpicallsText[] =
        "Output # mpi calls trapped per rank";
static char const zMpicalls_NAME[]           = "MPICALLS";
static char const zMpicalls_Name[]           = "mpicalls";
#define MPICALLS_FLAGS       (OPTST_DISABLED)

/*
 *  Verbose option description:
 */
static char const zVerboseText[] =
        "Always output all transition lists";
static char const zVerbose_NAME[]            = "VERBOSE";
static char const zVerbose_Name[]            = "verbose";
#define VERBOSE_FLAGS       (OPTST_DISABLED)

/*
 *  Quiet option description with
 *  "Must also have options" and "Incompatible options":
 */
static char const zQuietText[] =
        "Output no information save return code";
static char const zQuiet_NAME[]              = "QUIET";
static char const zQuiet_Name[]              = "quiet";
static const int
    aQuietCantList[] = {
    INDEX_OPT_VERBOSE, NO_EQUIVALENT };
#define QUIET_FLAGS       (OPTST_DISABLED)

/*
 *  Rpt_Progress option description:
 */
static char const zRpt_ProgressText[] =
        "Output progress every n MPI calls";
static char const zRpt_Progress_NAME[]       = "RPT_PROGRESS";
static char const zRpt_Progress_Name[]       = "rpt-progress";
#define RPT_PROGRESS_FLAGS       (OPTST_DISABLED \
        | OPTST_SET_ARGTYPE(OPARG_TYPE_NUMERIC))

/*
 *  Distributed option description:
 */
static char const zDistributedText[] =
        "Use to launch profiled proc manually";
static char const zDistributed_NAME[]        = "DISTRIBUTED";
static char const zDistributed_Name[]        = "distributed";
#define DISTRIBUTED_FLAGS       (OPTST_DISABLED)

/*
 *  Fibopt option description:
 */
#ifdef FIB
static char const zFiboptText[] =
        "Enables irrelevant barrier detection";
static char const zFibopt_NAME[]             = "FIBOPT";
static char const zFibopt_Name[]             = "fibopt";
#define FIBOPT_FLAGS       (OPTST_DISABLED)

#else   /* disable Fibopt */
#define FIBOPT_FLAGS       (OPTST_OMITTED | OPTST_NO_INIT)
#define zFibopt_NAME      NULL
#define zFiboptText       NULL
#define zFibopt_Name      NULL
#endif  /* FIB */

/*
 *  View_Prog_Out_Only option description:
 */
static char const zView_Prog_Out_OnlyText[] =
        "ISP generates no output, but the code being analyzed does";
static char const zView_Prog_Out_Only_NAME[] = "VIEW_PROG_OUT_ONLY";
static char const zView_Prog_Out_Only_Name[] = "view-prog-out-only";
#define VIEW_PROG_OUT_ONLY_FLAGS       (OPTST_DISABLED)

/*
 *  Disable_Omp option description:
 */
#ifdef USE_OPENMP
static char const zDisable_OmpText[] =
        "Disables OpenMP.  No effect unless ./configure --enable-openmp";
static char const zDisable_Omp_NAME[]        = "DISABLE_OMP";
static char const zDisable_Omp_Name[]        = "disable-omp";
#define DISABLE_OMP_FLAGS       (OPTST_DISABLED)

#else   /* disable Disable_Omp */
#define DISABLE_OMP_FLAGS       (OPTST_OMITTED | OPTST_NO_INIT)
#define zDisable_Omp_NAME      NULL
#define zDisable_OmpText       NULL
#define zDisable_Omp_Name      NULL
#endif  /* USE_OPENMP */

/*
 *  Exp_Mode option description:
 */
static char const zExp_ModeText[] =
        "Choose which interleavings to explore [all, random, left_most]";
static char const zExp_Mode_NAME[]           = "EXP_MODE";
static char const zExp_Mode_Name[]           = "exp-mode";
#define zExp_ModeDefaultArg          ((char const*)EXP_MODE_ALL)
#define EXP_MODE_FLAGS       (OPTST_DISABLED \
        | OPTST_SET_ARGTYPE(OPARG_TYPE_ENUMERATION))

/*
 *  Env option description:
 */
static char const zEnvText[] =
        "Use environment to set client options (Windows)";
static char const zEnv_NAME[]                = "ENV";
static char const zEnv_Name[]                = "env";
#define ENV_FLAGS       (OPTST_DISABLED)

/*
 *  Exp_Some option description:
 */
static char const zExp_SomeText[] =
        "Explore random K choices at non-determ. points";
static char const zExp_Some_NAME[]           = "EXP_SOME";
static char const zExp_Some_Name[]           = "exp-some";
#define EXP_SOME_FLAGS       (OPTST_DISABLED \
        | OPTST_SET_ARGTYPE(OPARG_TYPE_NUMERIC))

/*
 *  Stop_At_Deadlock option description:
 */
static char const zStop_At_DeadlockText[] =
        "When enabled, ISP will stop at deadlock";
static char const zStop_At_Deadlock_NAME[]   = "STOP_AT_DEADLOCK";
static char const zStop_At_Deadlock_Name[]   = "stop-at-deadlock";
#define zStop_At_DeadlockDefaultArg  ((char const*)AG_FALSE)
#define STOP_AT_DEADLOCK_FLAGS       (OPTST_DISABLED \
        | OPTST_SET_ARGTYPE(OPARG_TYPE_BOOLEAN))

/*
 *  Debug_Sched option description:
 */
#ifdef CONFIG_DEBUG_SCHED
static char const zDebug_SchedText[] =
        "Enable scheduler debug messages";
static char const zDebug_Sched_NAME[]        = "DEBUG_SCHED";
static char const zDebug_Sched_Name[]        = "debug-sched";
#define DEBUG_SCHED_FLAGS       (OPTST_DISABLED)

#else   /* disable Debug_Sched */
#define DEBUG_SCHED_FLAGS       (OPTST_OMITTED | OPTST_NO_INIT)
#define zDebug_Sched_NAME      NULL
#define zDebug_SchedText       NULL
#define zDebug_Sched_Name      NULL
#endif  /* CONFIG_DEBUG_SCHED */

/*
 *  No_Ample_Set_Fix option description:
 */
#ifdef CONFIG_OPTIONAL_AMPLE_SET_FIX
static char const zNo_Ample_Set_FixText[] =
        "Disable the ample set fix";
static char const zNo_Ample_Set_Fix_NAME[]   = "NO_AMPLE_SET_FIX";
static char const zNo_Ample_Set_Fix_Name[]   = "no-ample-set-fix";
#define NO_AMPLE_SET_FIX_FLAGS       (OPTST_DISABLED)

#else   /* disable No_Ample_Set_Fix */
#define NO_AMPLE_SET_FIX_FLAGS       (OPTST_OMITTED | OPTST_NO_INIT)
#define zNo_Ample_Set_Fix_NAME      NULL
#define zNo_Ample_Set_FixText       NULL
#define zNo_Ample_Set_Fix_Name      NULL
#endif  /* CONFIG_OPTIONAL_AMPLE_SET_FIX */

/*
 *  Bound option description:
 */
static char const zBoundText[] =
        "Enable bounded mixing";
static char const zBound_NAME[]              = "BOUND";
static char const zBound_Name[]              = "bound";
#define BOUND_FLAGS       (OPTST_DISABLED \
        | OPTST_SET_ARGTYPE(OPARG_TYPE_NUMERIC))

/*
 *  Fprs option description:
 */
static char const zFprsText[] =
        "Focus Plus Random Sampling";
static char const zFprs_NAME[]               = "FPRS";
static char const zFprs_Name[]               = "fprs";
#define FPRS_FLAGS       (OPTST_DISABLED)

/*
 *  Help/More_Help/Version option descriptions:
 */
static char const zHelpText[]          = "Display extended usage information and exit";
static char const zHelp_Name[]         = "help";
#ifdef HAVE_WORKING_FORK
#define OPTST_MORE_HELP_FLAGS   (OPTST_IMM | OPTST_NO_INIT)
static char const zMore_Help_Name[]    = "more-help";
static char const zMore_HelpText[]     = "Extended usage information passed thru pager";
#else
#define OPTST_MORE_HELP_FLAGS   (OPTST_OMITTED | OPTST_NO_INIT)
#define zMore_Help_Name   NULL
#define zMore_HelpText    NULL
#endif
#ifdef NO_OPTIONAL_OPT_ARGS
#  define OPTST_VERSION_FLAGS   OPTST_IMM | OPTST_NO_INIT
#else
#  define OPTST_VERSION_FLAGS   OPTST_SET_ARGTYPE(OPARG_TYPE_STRING) | \
                                OPTST_ARG_OPTIONAL | OPTST_IMM | OPTST_NO_INIT
#endif

static char const zVersionText[]       = "Output version information and exit";
static char const zVersion_Name[]      = "version";
/*
 *  Declare option callback procedures
 */
extern tOptProc
    optionBooleanVal,    optionNestedVal,     optionNumericVal,
    optionPagedUsage,    optionPrintVersion,  optionResetOpt,
    optionStackArg,      optionTimeVal,       optionUnstackArg,
    optionVersionStderr;
static tOptProc
    doOptEncoding, doOptExp_Mode, doOptNumprocs, doOptPort, doUsageOpt;

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *
 *  Define the Isp Option Descriptions.
 */
static tOptDesc optDesc[ OPTION_CT ] = {
  {  /* entry idx, value */ 0, VALUE_OPT_NUMPROCS,
     /* equiv idx, value */ 0, VALUE_OPT_NUMPROCS,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ NUMPROCS_FLAGS, 0,
     /* last opt argumnt */ { zNumprocsDefaultArg },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ doOptNumprocs,
     /* desc, NAME, name */ zNumprocsText, zNumprocs_NAME, zNumprocs_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 1, VALUE_OPT_ENCODING,
     /* equiv idx, value */ 1, VALUE_OPT_ENCODING,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ ENCODING_FLAGS, 0,
     /* last opt argumnt */ { zEncodingDefaultArg },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ doOptEncoding,
     /* desc, NAME, name */ zEncodingText, zEncoding_NAME, zEncoding_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 2, VALUE_OPT_PORT,
     /* equiv idx, value */ 2, VALUE_OPT_PORT,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ PORT_FLAGS, 0,
     /* last opt argumnt */ { zPortDefaultArg },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ doOptPort,
     /* desc, NAME, name */ zPortText, zPort_NAME, zPort_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 3, VALUE_OPT_HOST,
     /* equiv idx, value */ 3, VALUE_OPT_HOST,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ HOST_FLAGS, 0,
     /* last opt argumnt */ { zHostDefaultArg },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zHostText, zHost_NAME, zHost_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 4, VALUE_OPT_US,
     /* equiv idx, value */ 4, VALUE_OPT_US,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ US_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zUsText, zUs_NAME, zUs_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 5, VALUE_OPT_BLOCK,
     /* equiv idx, value */ 5, VALUE_OPT_BLOCK,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ BLOCK_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, aBlockCantList,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zBlockText, zBlock_NAME, zBlock_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 6, VALUE_OPT_NOBLOCK,
     /* equiv idx, value */ 6, VALUE_OPT_NOBLOCK,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ NOBLOCK_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, aNoblockCantList,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zNoblockText, zNoblock_NAME, zNoblock_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 7, VALUE_OPT_LOGFILE,
     /* equiv idx, value */ 7, VALUE_OPT_LOGFILE,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ LOGFILE_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zLogfileText, zLogfile_NAME, zLogfile_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 8, VALUE_OPT_MPICALLS,
     /* equiv idx, value */ 8, VALUE_OPT_MPICALLS,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ MPICALLS_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zMpicallsText, zMpicalls_NAME, zMpicalls_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 9, VALUE_OPT_VERBOSE,
     /* equiv idx, value */ 9, VALUE_OPT_VERBOSE,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ VERBOSE_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zVerboseText, zVerbose_NAME, zVerbose_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 10, VALUE_OPT_QUIET,
     /* equiv idx, value */ 10, VALUE_OPT_QUIET,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ QUIET_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, aQuietCantList,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zQuietText, zQuiet_NAME, zQuiet_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 11, VALUE_OPT_RPT_PROGRESS,
     /* equiv idx, value */ 11, VALUE_OPT_RPT_PROGRESS,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ RPT_PROGRESS_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ optionNumericVal,
     /* desc, NAME, name */ zRpt_ProgressText, zRpt_Progress_NAME, zRpt_Progress_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 12, VALUE_OPT_DISTRIBUTED,
     /* equiv idx, value */ 12, VALUE_OPT_DISTRIBUTED,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ DISTRIBUTED_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zDistributedText, zDistributed_NAME, zDistributed_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 13, VALUE_OPT_FIBOPT,
     /* equiv idx, value */ 13, VALUE_OPT_FIBOPT,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ FIBOPT_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zFiboptText, zFibopt_NAME, zFibopt_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 14, VALUE_OPT_VIEW_PROG_OUT_ONLY,
     /* equiv idx, value */ 14, VALUE_OPT_VIEW_PROG_OUT_ONLY,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ VIEW_PROG_OUT_ONLY_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zView_Prog_Out_OnlyText, zView_Prog_Out_Only_NAME, zView_Prog_Out_Only_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 15, VALUE_OPT_DISABLE_OMP,
     /* equiv idx, value */ 15, VALUE_OPT_DISABLE_OMP,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ DISABLE_OMP_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zDisable_OmpText, zDisable_Omp_NAME, zDisable_Omp_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 16, VALUE_OPT_EXP_MODE,
     /* equiv idx, value */ 16, VALUE_OPT_EXP_MODE,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ EXP_MODE_FLAGS, 0,
     /* last opt argumnt */ { zExp_ModeDefaultArg },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ doOptExp_Mode,
     /* desc, NAME, name */ zExp_ModeText, zExp_Mode_NAME, zExp_Mode_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 17, VALUE_OPT_ENV,
     /* equiv idx, value */ 17, VALUE_OPT_ENV,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ ENV_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zEnvText, zEnv_NAME, zEnv_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 18, VALUE_OPT_EXP_SOME,
     /* equiv idx, value */ 18, VALUE_OPT_EXP_SOME,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ EXP_SOME_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ optionNumericVal,
     /* desc, NAME, name */ zExp_SomeText, zExp_Some_NAME, zExp_Some_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 19, VALUE_OPT_STOP_AT_DEADLOCK,
     /* equiv idx, value */ 19, VALUE_OPT_STOP_AT_DEADLOCK,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ STOP_AT_DEADLOCK_FLAGS, 0,
     /* last opt argumnt */ { zStop_At_DeadlockDefaultArg },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ optionBooleanVal,
     /* desc, NAME, name */ zStop_At_DeadlockText, zStop_At_Deadlock_NAME, zStop_At_Deadlock_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 20, VALUE_OPT_DEBUG_SCHED,
     /* equiv idx, value */ 20, VALUE_OPT_DEBUG_SCHED,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ DEBUG_SCHED_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zDebug_SchedText, zDebug_Sched_NAME, zDebug_Sched_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 21, VALUE_OPT_NO_AMPLE_SET_FIX,
     /* equiv idx, value */ 21, VALUE_OPT_NO_AMPLE_SET_FIX,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ NO_AMPLE_SET_FIX_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zNo_Ample_Set_FixText, zNo_Ample_Set_Fix_NAME, zNo_Ample_Set_Fix_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 22, VALUE_OPT_BOUND,
     /* equiv idx, value */ 22, VALUE_OPT_BOUND,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ BOUND_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ optionNumericVal,
     /* desc, NAME, name */ zBoundText, zBound_NAME, zBound_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ 23, VALUE_OPT_FPRS,
     /* equiv idx, value */ 23, VALUE_OPT_FPRS,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ FPRS_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ NULL,
     /* desc, NAME, name */ zFprsText, zFprs_NAME, zFprs_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ INDEX_OPT_VERSION, VALUE_OPT_VERSION,
     /* equiv idx value  */ NO_EQUIVALENT, 0,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ OPTST_VERSION_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ optionPrintVersion,
     /* desc, NAME, name */ zVersionText, NULL, zVersion_Name,
     /* disablement strs */ NULL, NULL },



  {  /* entry idx, value */ INDEX_OPT_HELP, VALUE_OPT_HELP,
     /* equiv idx value  */ NO_EQUIVALENT, 0,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ OPTST_IMM | OPTST_NO_INIT, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL, NULL,
     /* option proc      */ doUsageOpt,
     /* desc, NAME, name */ zHelpText, NULL, zHelp_Name,
     /* disablement strs */ NULL, NULL },

  {  /* entry idx, value */ INDEX_OPT_MORE_HELP, VALUE_OPT_MORE_HELP,
     /* equiv idx value  */ NO_EQUIVALENT, 0,
     /* equivalenced to  */ NO_EQUIVALENT,
     /* min, max, act ct */ 0, 1, 0,
     /* opt state flags  */ OPTST_MORE_HELP_FLAGS, 0,
     /* last opt argumnt */ { NULL },
     /* arg list/cookie  */ NULL,
     /* must/cannot opts */ NULL,  NULL,
     /* option proc      */ optionPagedUsage,
     /* desc, NAME, name */ zMore_HelpText, NULL, zMore_Help_Name,
     /* disablement strs */ NULL, NULL }
};

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *
 *  Define the Isp Option Environment
 */
tSCC   zPROGNAME[]   = "ISP";
tSCC   zUsageTitle[] =
"isp - isp: In-Situ Partial Order - Ver. 0.2.0\n\
USAGE:  %s [ -<flag> [<val>] | --<name>[{=| }<val>] ]... \\\n\
\t\tprofiled_executable [executable args]\n";
#define zRcName     NULL
#define apzHomeList NULL

tSCC   zBugsAddr[]    = "isp-dev@cs.utah.edu";
tSCC   zExplain[]     = "\n\
exit codes:\n\
 \t\t    0    Model checking complete with no errors detected.\n\
\t\t    1    Model checking complete with deadlock detected.\n\
\t\t    2    ISP help displayed.\n\
\t\t    3    A process failed an assertion.\n\
\t\t    4    A process exited with MPI_Abort.\n\
\t\t    5    A process called an MPI function with an invalid rank.\n\
\t\t    11   Unable to start profiled MPI program with mpiexec.\n\
\t\t    12   Unable to use WINSOCK.\n\
\t\t    13   Unable to open socket.\n\
\t\t    14   Unable to bind to socket.\n\
\t\t    15   Unable to listen on socket.\n\
\t\t    16   Unable to accept connections on socket.\n\
\t\t    17   Error reading from socket.\n\
\t\t    20   Unable to open specified log file.\n\
\t\t    21   Transitions different between interleavings.\n\
\t\t    22   Received an empty buffer. (Profiled code might have crashed.)\n";
#define zDetail         NULL
tSCC    zFullVersion[] = ISP_FULL_VERSION;
/* extracted from /home/ssharma/Downloads/autogen-5.11.1/autogen-install/share/autogen/optcode.tpl near line 493 */

#if defined(ENABLE_NLS)
# define OPTPROC_BASE OPTPROC_TRANSLATE
  static tOptionXlateProc translate_option_strings;
#else
# define OPTPROC_BASE OPTPROC_NONE
# define translate_option_strings NULL
#endif /* ENABLE_NLS */


#define isp_full_usage NULL
#define isp_short_usage NULL
tOptions ispOptions = {
    OPTIONS_STRUCT_VERSION,
    0, NULL,                    /* original argc + argv    */
    ( OPTPROC_BASE
    + OPTPROC_ERRSTOP
    + OPTPROC_SHORTOPT
    + OPTPROC_LONGOPT
    + OPTPROC_NO_REQ_OPT
    + OPTPROC_ARGS_REQ ),
    0, NULL,                    /* current option index, current option */
    NULL,         NULL,         zPROGNAME,
    zRcName,      zCopyright,   zCopyrightNotice,
    zFullVersion, apzHomeList,  zUsageTitle,
    zExplain,     zDetail,      optDesc,
    zBugsAddr,                  /* address to send bugs to */
    NULL, NULL,                 /* extensions/saved state  */
    optionUsage,       /* usage procedure */
    translate_option_strings,   /* translation procedure */
    /*
     *  Indexes to special options
     */
    { INDEX_OPT_MORE_HELP, /* more-help option index */
      NO_EQUIVALENT, /* save option index */
      NO_EQUIVALENT, /* '-#' option index */
      NO_EQUIVALENT /* index of default opt */
    },
    27 /* full option count */, 24 /* user option count */,
    isp_full_usage, isp_short_usage,
    NULL, NULL
};

/*
 *  Create the static procedure(s) declared above.
 */
static void
doUsageOpt(
    tOptions*   pOptions,
    tOptDesc*   pOptDesc )
{
    (void)pOptions;
    USAGE(EXIT_SUCCESS);
}

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *
 *   For the numProcs option.
 */
static void
doOptNumprocs(tOptions* pOptions, tOptDesc* pOptDesc)
{
    static const struct {long const rmin, rmax;} rng[1] = {
        { 1, LONG_MAX } };
    long val;
    int  ix;
    char * pzEnd;

    if (pOptions <= OPTPROC_EMIT_LIMIT)
        goto emit_ranges;

    errno = 0;
    val = strtol(pOptDesc->optArg.argString, &pzEnd, 0);
    if ((pOptDesc->optArg.argString == pzEnd) || (errno != 0))
        goto bad_value;

    if (*pzEnd != '\0')
        goto bad_value;
    for (ix = 0; ix < 1; ix++) {
        if (val < rng[ix].rmin)
            continue;  /* ranges need not be ordered. */
        if (val == rng[ix].rmin)
            goto valid_return;
        if (rng[ix].rmax == LONG_MIN)
            continue;
        if (val <= rng[ix].rmax)
            goto valid_return;
    }

  bad_value:

    option_usage_fp = stderr;

  emit_ranges:
    optionShowRange(pOptions, pOptDesc, (void *)rng, 1);
    return;

  valid_return:
    if ((pOptDesc->fOptState & OPTST_ALLOC_ARG) != 0) {
        free((void *)pOptDesc->optArg.argString);
        pOptDesc->fOptState &= ~OPTST_ALLOC_ARG;
    }
    pOptDesc->optArg.argInt = val;
}

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *
 *   For the encoding option.
 */
static void
doOptEncoding(tOptions* pOptions, tOptDesc* pOptDesc)
{
    static const struct {long const rmin, rmax;} rng[1] = {
        { 0, 2 } };
    long val;
    int  ix;
    char * pzEnd;

    if (pOptions <= OPTPROC_EMIT_LIMIT)
        goto emit_ranges;

    errno = 0;
    val = strtol(pOptDesc->optArg.argString, &pzEnd, 0);
    if ((pOptDesc->optArg.argString == pzEnd) || (errno != 0))
        goto bad_value;

    if (*pzEnd != '\0')
        goto bad_value;
    for (ix = 0; ix < 1; ix++) {
        if (val < rng[ix].rmin)
            continue;  /* ranges need not be ordered. */
        if (val == rng[ix].rmin)
            goto valid_return;
        if (rng[ix].rmax == LONG_MIN)
            continue;
        if (val <= rng[ix].rmax)
            goto valid_return;
    }

  bad_value:

    option_usage_fp = stderr;

  emit_ranges:
    optionShowRange(pOptions, pOptDesc, (void *)rng, 1);
    return;

  valid_return:
    if ((pOptDesc->fOptState & OPTST_ALLOC_ARG) != 0) {
        free((void *)pOptDesc->optArg.argString);
        pOptDesc->fOptState &= ~OPTST_ALLOC_ARG;
    }
    pOptDesc->optArg.argInt = val;
}

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *
 *   For the port option.
 */
static void
doOptPort(tOptions* pOptions, tOptDesc* pOptDesc)
{
    static const struct {long const rmin, rmax;} rng[1] = {
        { 1, 99999 } };
    long val;
    int  ix;
    char * pzEnd;

    if (pOptions <= OPTPROC_EMIT_LIMIT)
        goto emit_ranges;

    errno = 0;
    val = strtol(pOptDesc->optArg.argString, &pzEnd, 0);
    if ((pOptDesc->optArg.argString == pzEnd) || (errno != 0))
        goto bad_value;

    if (*pzEnd != '\0')
        goto bad_value;
    for (ix = 0; ix < 1; ix++) {
        if (val < rng[ix].rmin)
            continue;  /* ranges need not be ordered. */
        if (val == rng[ix].rmin)
            goto valid_return;
        if (rng[ix].rmax == LONG_MIN)
            continue;
        if (val <= rng[ix].rmax)
            goto valid_return;
    }

  bad_value:

    option_usage_fp = stderr;

  emit_ranges:
    optionShowRange(pOptions, pOptDesc, (void *)rng, 1);
    return;

  valid_return:
    if ((pOptDesc->fOptState & OPTST_ALLOC_ARG) != 0) {
        free((void *)pOptDesc->optArg.argString);
        pOptDesc->fOptState &= ~OPTST_ALLOC_ARG;
    }
    pOptDesc->optArg.argInt = val;
}

/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *
 *   For the exp-mode option.
 */
static void
doOptExp_Mode(tOptions* pOptions, tOptDesc* pOptDesc)
{

/* extracted from /home/ssharma/Downloads/autogen-5.11.1/autogen-install/share/autogen/optmain.tpl near line 890 */
    static char const * const azNames[3] = {
        "all",        "random",     "left_most"
    };

    if (pOptions <= OPTPROC_EMIT_LIMIT) {
        (void) optionEnumerationVal(pOptions, pOptDesc, azNames, 3);
        return; /* protect AutoOpts client code from internal callbacks */
    }

    pOptDesc->optArg.argEnum =
        optionEnumerationVal(pOptions, pOptDesc, azNames, 3);

}
/* extracted from /home/ssharma/Downloads/autogen-5.11.1/autogen-install/share/autogen/optcode.tpl near line 625 */

#if ENABLE_NLS
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <autoopts/usage-txt.h>

static char* AO_gettext(char const* pz);
static void  coerce_it(void** s);

static char*
AO_gettext(char const* pz)
{
    char* pzRes;
    if (pz == NULL)
        return NULL;
    pzRes = _(pz);
    if (pzRes == pz)
        return pzRes;
    pzRes = strdup(pzRes);
    if (pzRes == NULL) {
        fputs(_("No memory for duping translated strings\n"), stderr);
        exit(EXIT_FAILURE);
    }
    return pzRes;
}

static void coerce_it(void** s) { *s = AO_gettext(*s); }
#define COERSION(_f) \
  coerce_it((void*)&(ispOptions._f))

/*
 *  This invokes the translation code (e.g. gettext(3)).
 */
static void
translate_option_strings(void)
{
    /*
     *  Guard against re-translation.  It won't work.  The strings will have
     *  been changed by the first pass through this code.  One shot only.
     */
    if (option_usage_text.field_ct != 0) {

        /*
         *  Do the translations.  The first pointer follows the field count
         *  field.  The field count field is the size of a pointer.
         */
        tOptDesc* pOD = ispOptions.pOptDesc;
        char**    ppz = (char**)(void*)&(option_usage_text);
        int       ix  = option_usage_text.field_ct;

        do {
            ppz++;
            *ppz = AO_gettext(*ppz);
        } while (--ix > 0);

        COERSION(pzCopyright);
        COERSION(pzCopyNotice);
        COERSION(pzFullVersion);
        COERSION(pzUsageTitle);
        COERSION(pzExplain);
        COERSION(pzDetail);
        option_usage_text.field_ct = 0;

        for (ix = ispOptions.optCt; ix > 0; ix--, pOD++)
            coerce_it((void*)&(pOD->pzText));
    }

    if ((ispOptions.fOptSet & OPTPROC_NXLAT_OPT_CFG) == 0) {
        tOptDesc* pOD = ispOptions.pOptDesc;
        int       ix;

        for (ix = ispOptions.optCt; ix > 0; ix--, pOD++) {
            coerce_it((void*)&(pOD->pz_Name));
            coerce_it((void*)&(pOD->pz_DisableName));
            coerce_it((void*)&(pOD->pz_DisablePfx));
        }
        /* prevent re-translation */
        ispOptions.fOptSet |= OPTPROC_NXLAT_OPT_CFG | OPTPROC_NXLAT_OPT;
    }
}

#endif /* ENABLE_NLS */

#ifdef  __cplusplus
}
#endif
/* sched-opt.c ends here */
