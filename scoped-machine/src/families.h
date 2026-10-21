/* families.h — the one name of every operation family: its id. A module
 * defines its families at these ids; every module refers to a family by this
 * name. Families defined at run time (tests) follow F_FIXED. */
#ifndef CUBICAL_FAMILIES_H
#define CUBICAL_FAMILIES_H

enum {
    F_WHNF = 1, Fz_ADD, Fz_NEG, F_REFVAR, F_DIMS, F_FIELD, F_BINDER, F_CONSTRUCT, F_HEAD, F_PHI, F_UNFOLD,
    F_GLOBALS, F_JOIN, F_IVMEET, F_FCMEET, F_IVNEG, F_FCEND, F_FCENT, F_FCFORALL,
    F_FCPROJ, F_SUNION, F_SREMOVE, F_SCONTAINS,
    F_INTERN, F_FLATTEN, F_HOST, F_OBS, F_CREQ, F_CBRANCH, F_DIST, F_EQUIV,
    F_COMPCLAUSE, F_TIMGT, F_TIMGD, F_TREF, F_TIV, F_TFC, F_TSCOPE,
    F_SCOPESIDE, F_SETFREE, F_CAPTURE, F_LOOKUP, F_SET, F_COMPOSE, F_ENVREBUILD, F_INTERP,
    F_TVMAKE, F_ISCOPE, F_LSUCC, F_LMAX, F_CODE,
    F_FIXED
};

#endif
