#ifndef _KACONFIG_H
#define _KACONFIG_H


#include "llvm/Support/FileSystem.h"
#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <fstream>
#include <map> 
#include "Common.h"


using namespace std;
using namespace llvm;

//
// Configurations
//

//#define VERBOSE_SA 1
//#define DEBUG_SA 1

extern int ENABLE_MLTA;
extern int ENABLE_TYDM;
extern int MAX_PHASE_CG;

#define SOUND_MODE 1
#define UNROLL_LOOP_ONCE 1

///////////////////////////////////////////////////////////
// TyPM-related configurations
///////////////////////////////////////////////////////////
#define PARSE_VALUE_USES 1
#define TYPE_ELEVATION 1
#define FLOW_DIRECTION 1
#define FUNCTION_AS_TARGET_TYPE 1 // Target types: struct type or function type
#define MAP_DECLARATION_FUNCTION
#define PRINT_ICALL_TARGET
///////////////////////////////////////////////////////////

#define MAX_TYPE_LAYER 10
//#define MAP_CALLER_TO_CALLEE 1
//#define MLTA_FIELD_INSENSITIVE
#define PRINT_SOURCE_LINE
//#define DEBUG_MLTA

// Paths of sources
#define LINUX_SOURCE_KASE "/home/kjlu/projects/kernels/linux-5.18"




// 
// Load data from files
//

struct SrcLn {
	SrcLn() {};
	SrcLn(string s, int l) {
		Src = s;
		Ln = l;
	};
	string Src;
	int Ln;
};

static void LoadTraces(map<size_t, set<size_t>> &hashedTraces,
		map<size_t, SrcLn> &hashSrcMap) {

	string exepath = sys::fs::getMainExecutable(NULL, NULL);
	string exedir = exepath.substr(0, exepath.find_last_of('/'));
	string line;
#ifdef EVAL_FN_FIRFOX
	ifstream tracefile(exedir + "/../../data/traces-ff.list");
#else 
	ifstream tracefile(exedir + "/../../data/traces.list");
#endif

	SrcLn CallerSrcLn("", 0);
	SrcLn CalleeSrcLn("", 0);
	if (tracefile.is_open()) {
		while (!tracefile.eof()) {
			getline (tracefile, line);
			if (line.length() == 0)
				continue;
			size_t pos = line.find("CALLER:");
			if (pos != string::npos) {
				line = line.substr(pos + 8);
				pos = line.rfind(":");
				if (pos == string::npos) {
					CallerSrcLn.Ln = -1;
					continue;
				}
				CallerSrcLn.Ln = stoi(line.substr(pos + 1));
				CallerSrcLn.Src = line.substr(0, pos);
#ifdef EVAL_FN_FIRFOX
				pos = CallerSrcLn.Src.find("gecko-dev");
				if (pos != string::npos)
					CallerSrcLn.Src = CallerSrcLn.Src.substr(pos + 10);
#endif
				hashSrcMap[strIntHash(CallerSrcLn.Src, CallerSrcLn.Ln)] = CallerSrcLn;

				continue;
			}
			pos = line.find("CALLEE:");
			if (pos != string::npos) {
				if (CallerSrcLn.Ln == -1)
					continue;

				line = line.substr(pos + 8);
				pos = line.rfind(":");
				if (pos == string::npos)
					continue;
				CalleeSrcLn.Ln = stoi(line.substr(pos + 1));
				CalleeSrcLn.Src = line.substr(0, pos);
#ifdef EVAL_FN_FIRFOX
				pos = CalleeSrcLn.Src.find("gecko-dev");
				if (pos != string::npos) {
					CalleeSrcLn.Src = CalleeSrcLn.Src.substr(pos + 10);
				}
#endif
				// Assume every callee is preceded with a caller
				size_t callerhash = strIntHash(CallerSrcLn.Src, CallerSrcLn.Ln);
				size_t calleehash = strIntHash(CalleeSrcLn.Src, CalleeSrcLn.Ln);
				hashedTraces[callerhash].insert(calleehash);
				hashSrcMap[calleehash] = CalleeSrcLn;

				continue;
			}
		}
		tracefile.close();
	}
}


//////////////////////////////////////////////////////////
//
// Define target types
//
//////////////////////////////////////////////////////////

static void LoadTargetTypes(set<size_t> &TTySet) {

	hash<string> str_hash;
	string exepath = sys::fs::getMainExecutable(NULL, NULL);
	string exedir = exepath.substr(0, exepath.find_last_of('/'));
	string line;
	ifstream structfile(exedir + "/configs/critical-structs");
	if (structfile.is_open()) {
		while (!structfile.eof()) {
			getline (structfile, line);
			if (line.length() > 1) {
				TTySet.insert(str_hash("struct." + line));
			}
		}
		structfile.close();
	}
	string TTyName[] = {
		"struct.kernfs_node",
		"struct.ksm_scan",
	};
	for (auto name : TTyName) {
		TTySet.insert(str_hash(name));
	}
}

// 
// Functions that are out of the analysis scope: definition, data
// flows, etc. Common causes include linktime behaviors and assembly
//

static void LoadOutScopeFuncs(set<string> &FuncSet) {
	string exepath = sys::fs::getMainExecutable(NULL, NULL);
	string exedir = exepath.substr(0, exepath.find_last_of('/'));
	string line;
	ifstream structfile(exedir + "/configs/out-scope-funcs");
	if (structfile.is_open()) {
		while (!structfile.eof()) {
			getline (structfile, line);
			if (line.length() > 1) {
				FuncSet.insert(line);
			}
		}
		structfile.close();
	}
}

#endif
