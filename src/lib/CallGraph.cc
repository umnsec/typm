//===-- CallGraph.cc - Build global call-graph------------------===//
// 
// This pass builds a global call-graph. The targets of an indirect
// call are identified based on type analysis. This is scope-aware
// and multi-layer type analysis. 
//
//===-----------------------------------------------------------===//

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h" 
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/raw_ostream.h"  
#include "llvm/IR/InstrTypes.h" 
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h" 
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/CFG.h" 

#include <map> 
#include <vector> 
#include <pthread.h>


#include "Common.h"
#include "Config.h"
#include "CallGraph.h"



using namespace llvm;

//
// Static variables
//
int CallGraphPass::AnalysisPhase = 1;

//
// Implementation
//

void CallGraphPass::PhaseMLTA(Function *F) {

	// Unroll loops
#ifdef UNROLL_LOOP_ONCE
	unrollLoops(F);
#endif

	// Collect callers and callees
	for (inst_iterator i = inst_begin(F), e = inst_end(F); 
			i != e; ++i) {
		// Map callsite to possible callees.
		if (CallInst *CI = dyn_cast<CallInst>(&*i)) {

			CallSet.insert(CI);

			FuncSet *FS = &Ctx->Callees[CI];
			Value *CV = CI->getCalledOperand();
			Function *CF = dyn_cast<Function>(CV);

			// Indirect call
			if (CI->isIndirectCall()) {

				// Multi-layer type matching
				if (ENABLE_MLTA > 1) {
					findCalleesWithMLTA(CI, *FS);
				}
				// Fuzzy type matching
				else if (ENABLE_MLTA == 0) {
					size_t CIH = callHash(CI);
					if (MatchedICallTypeMap.find(CIH) 
							!= MatchedICallTypeMap.end())
						*FS = MatchedICallTypeMap[CIH];
					else {
						findCalleesWithType(CI, *FS);
						MatchedICallTypeMap[CIH] = *FS;
					}
				}
				// One-layer type matching
				else {
					*FS = Ctx->sigFuncsMap[callHash(CI)];
				}

#ifdef MAP_CALLER_TO_CALLEE
				for (Function *Callee : *FS) {
					Ctx->Callers[Callee].insert(CI);
				}
#endif

				// Save called values for future uses.
				Ctx->IndirectCallInsts.push_back(CI);

				ICallSet.insert(CI);
				if (!FS->empty()) {
					MatchedICallSet.insert(CI);
					Ctx->NumIndirectCallTargets += FS->size();
					Ctx->NumValidIndirectCalls++;
				}
			}
			// Direct call
			else {
				// not InlineAsm
				if (CF) {
					// Call external functions
					if (CF->isDeclaration()) {
						//StringRef FName = CF->getName();
						//if (FName.startswith("SyS_"))
						//	FName = StringRef("sys_" + FName.str().substr(4));
						if (Function *GF = Ctx->GlobalFuncMap[CF->getGUID()])
							CF = GF;
					}

					FS->insert(CF);

#ifdef MAP_CALLER_TO_CALLEE
					Ctx->Callers[CF].insert(CI);
#endif
				}
				// InlineAsm
				else {
					// TODO: handle InlineAsm functions
				}
			}
#if 0
			if (ENABLE_MLTA > 1) {
				if (CI->isIndirectCall()) {

#ifdef PRINT_ICALL_TARGET
					printSourceCodeInfo(CI, "RESOLVING");
#endif

					//FuncSet FSBase = Ctx->sigFuncsMap[callHash(CI)];
					//saveCalleesInfo(CI, FSBase, false);
					//if (LayerNo > 0) {
					//	saveCalleesInfo(CI, FS, true);
					for (auto F : Ctx->sigFuncsMap[callHash(CI)]) {
						if (FS->find(F) == FS->end()) {
#ifdef PRINT_ICALL_TARGET
							if ((OutScopeFuncs.find(F) == OutScopeFuncs.end())
									&& (StoredFuncs.find(F) != StoredFuncs.end())) {
								printSourceCodeInfo(F, "REMOVED");
							}
							else {
								// TODO: may need to add it back, as the function is
								// out of the analysis scope
							}
#endif
						}
					}
#ifdef PRINT_ICALL_TARGET
					printTargets(*FS, CI);
#endif
				}
				}
#endif
			}
		}
	}

	void CallGraphPass::PhaseTyPM(Function *F) {
		for (inst_iterator i = inst_begin(F), e = inst_end(F); 
				i != e; ++i) {

			//
			// Step 1: Collect data flows among modules
			// 

			// Note: the following impl is not type-aware yet
			// Collect data flows through functions calls
			CallInst *CI = dyn_cast<CallInst>(&*i);
			if (!CI)
				continue;

			if (CI->arg_empty())
				continue;

			// Indirect call
			if (CI->isIndirectCall()) {

				for (auto CF : Ctx->Callees[CI]) {
					// Need to use the actual function with body here
					if (CF->isDeclaration())
						CF = Ctx->GlobalFuncMap[CF->getGUID()];
					if (!CF) {
						continue;
					}
					if (CF->doesNotAccessMemory())
						continue;

					parseTargetTypesInCalls(CI, CF);
				}
			}

			// Direct call, no need to repeat for following iterations
			else if (AnalysisPhase == 2) {
				// NOTE: Do not use getCalledFunction as it can only return
				// function within the module
				Value *CO = CI->getCalledOperand();
				if (!CO) {
					continue;
				}

				Function *CF = dyn_cast<Function>(CO);
				if (!CF || CF->isIntrinsic()) {
					// Likely it is ASM code
					continue;
				}
				// Need to use the actual function with body here
				if (CF->isDeclaration()) {
					CF = Ctx->GlobalFuncMap[CF->getGUID()];
					if (!CF) {
						// Have to skip it as the function body is not in
						// the analysis scope
						continue;
					}
				}
				if (CF->doesNotAccessMemory())
					continue;

				parseTargetTypesInCalls(CI, CF);
			}
		}
	}

	bool CallGraphPass::doInitialization(Module *M) {

		OP<<"#"<<MIdx<<" Initializing: "<<M->getName()<<"\n";

		++ MIdx;

		DLMap[M] = &(M->getDataLayout());
		Int8PtrTy[M] = Type::getInt8PtrTy(M->getContext());
		assert(Int8PtrTy[M]);
		IntPtrTy[M] = DLMap[M]->getIntPtrType(M->getContext());

		set<User *>CastSet;

		//
		// Do something at the begining 
		//
		if (1 == MIdx) {
			for (auto MN : Ctx->Modules) {
				Module *M = MN.first;
				for (Module::global_iterator gi = M->global_begin(); 
						gi != M->global_end(); ++gi) {

					GlobalVariable* GV = &*gi;
					if (GV->hasInitializer()) {
						Ctx->Globals[GV->getGUID()] = GV;
					}
				}

			}

		}



		//
		// Iterate and process globals
		//
		for (Module::global_iterator gi = M->global_begin(); 
				gi != M->global_end(); ++gi) {

			GlobalVariable* GV = &*gi;
			if (GV->hasInitializer()) {

				Type *ITy = GV->getInitializer()->getType();
				if (!ITy->isPointerTy() && !isContainerTy(ITy))
					continue;

				//Ctx->Globals[GV->getGUID()] = GV;

				// Parse the initializer
				set<Type *>TySet;
				findTargetTypesInInitializer(GV, M, TySet);

				typeConfineInInitializer(GV);

				// Collect all casts in the global variable
				findCastsInGV(GV, CastSet);
			}
		}

		// Iterate functions and instructions
		for (Function &F : *M) { 

			// Do not include LLVM intrinsic functions?
			if (F.isIntrinsic()) {
				continue;
			}

			// Collect address-taken functions.
			// NOTE: declaration functions can also have address taken 
			if (F.hasAddressTaken()) {
				Ctx->AddressTakenFuncs.insert(&F);
				size_t FuncHash = funcHash(&F, false);
				Ctx->sigFuncsMap[FuncHash].insert(&F);
				StringRef FName = F.getName();
				// The following functions are not in the analysis scope
				if (FName.startswith("__x64") ||
						FName.startswith("__ia32") ||
						FName.startswith("__do_sys")) {
					OutScopeFuncNames.insert(F.getName().str());
				}
			}

			// The following only considers actual functions with body
			if (F.isDeclaration()) {
				continue;
			}
			++Ctx->NumFunctions;

			// Collect global function definitions.
			if (F.hasExternalLinkage()) {
				Ctx->GlobalFuncMap[F.getGUID()] = &F;
			}


			//
			// MLTA and TyPM
			//
			if (ENABLE_MLTA > 1) {
				typePropInFunction(&F);
			}

			collectAliasStructPtr(&F);
			typeConfineInFunction(&F);

			// Collect all casts in the function
			findCastsInFunction(&F, CastSet);

			// Handle casts
			processCasts(CastSet, M);

			// Collect all stores against fields of composite types in the
			// function
			findStoredTypeIdxInFunction(&F);

			// Collection allocations of critical data structures
			findTargetAllocInFunction(&F);
		}



		//
		// Do something at the end of last module
		//
		if (Ctx->Modules.size() == MIdx) {

			if (ENABLE_MLTA > 1) {
				// Map the declaration functions to actual ones
				// NOTE: to delete an item, must iterate by reference
				for (auto &SF : Ctx->sigFuncsMap) {
					for (auto F : SF.second) {
						if (!F)
							continue;
						if (F->isDeclaration()) {
							SF.second.erase(F);
							if (Function *AF = Ctx->GlobalFuncMap[F->getGUID()]) {
								SF.second.insert(AF);
							}
						}
					}
				}

				for (auto &TF : typeIdxFuncsMap) {
					for (auto &IF : TF.second) {
						for (auto F : IF.second) {
							if (F->isDeclaration()) {
								IF.second.erase(F);
								if (Function *AF = Ctx->GlobalFuncMap[F->getGUID()]) {
									IF.second.insert(AF);
								}
							}
						}
					}
				}
			}

			MIdx = 0;
		}

		return false;
	}

	bool CallGraphPass::doFinalization(Module *M) {

		++ MIdx;
		if (Ctx->Modules.size() == MIdx) {
			// Finally map declaration functions to actual functions
			OP<<"Mapping declaration functions to actual ones...\n";
			Ctx->NumIndirectCallTargets = 0;
			for (auto CI : CallSet) {
				mapDeclToActualFuncs(Ctx->Callees[CI]);

				if (CI->isIndirectCall()) {
					Ctx->NumIndirectCallTargets += Ctx->Callees[CI].size();
					printTargets(Ctx->Callees[CI], CI);
				}
			}


#if 0
			for (auto Prop : moPropMap) {
				for (auto Mo : Prop.second)
					OP<<"\t"<<Mo->getName()<<"\n\n";
			}
#endif

		}
		return false;
	}

	bool CallGraphPass::doModulePass(Module *M) {

		++ MIdx;

		//
		// Iterate and process globals
		//
		for (Module::global_iterator gi = M->global_begin(); 
				gi != M->global_end(); ++gi) {

			GlobalVariable* GV = &*gi;

			Type *GTy = GV->getType();
			assert(GTy->isPointerTy());

			if (AnalysisPhase == 1) {

#ifdef PARSE_VALUE_USES
				// Parse its uses
				set<Value *>Visited;
				parseUsesOfGV(GV, GV, M, Visited);

#else

				if (!GV->hasInitializer()) {
					GV = Ctx->Globals[GV->getGUID()];
					if (!GV) {
						continue;
					}
				}

				set<Type *>TySet;
				findTargetTypesInValue(GV->getInitializer(), TySet, M);
				for (auto Ty : TySet) {

					// TODO: can be optimized for better precision: either from
					// or to
					size_t TyH;
					TypesFromModuleGVMap[make_pair(GV->getGUID(), TyH)].insert(M);
					TypesToModuleGVMap[make_pair(GV->getGUID(), TyH)].insert(M);
				}

#endif

			}
		}
		if (MIdx == Ctx->Modules.size()) {
			// Use globals to connect modules
			for (auto GMM : TypesToModuleGVMap) {
				for (auto DstM : GMM.second) {
					size_t TyH = GMM.first.second;
					moPropMap[make_pair(DstM, TyH)].insert(
							TypesFromModuleGVMap[GMM.first].begin(),
							TypesFromModuleGVMap[GMM.first].end());
				}
			}
#if 0
			for (auto m : moPropMap)
				for (auto m1 : m.second)
					OP<<"@@ dependence "<<m1->getName()
						<<" ==> "<<m.first.first->getName()
						<<" HASH: "<<m.first.second<<"\n";
#endif
		}

		//
		// Process functions
		//
		for (Module::iterator f = M->begin(), fe = M->end(); 
				f != fe; ++f) {

			Function *F = &*f;

			if (F->isDeclaration() || F->isIntrinsic())
				continue;

			// Phase 1: Multi-layer type analysis
			if (AnalysisPhase == 1) {
				PhaseMLTA(F);
			} else {
				// Phase 2-to-n: Modular type analysis
				// TODO: only iterate over indirect calls
				PhaseTyPM(F);
			}
		}

		// Analysis phase control
		if (Ctx->Modules.size() == MIdx) {

			if (AnalysisPhase == 2) {
				//
				// Clear no longer useful structures
				//
				GVFuncTypesMap.clear();
				TypesFromModuleGVMap.clear();
				TypesToModuleGVMap.clear();
			}

			if (AnalysisPhase >= 2) {

				ResolvedDepModulesMap.clear();
				bool Iter = true;
				// Merge the propagation maps
				moPropMapAll.insert(moPropMap.begin(), moPropMap.end());
				// Add map one by one to avoid overwritting
				for (auto m : moPropMapV) {
					moPropMapAll[m.first].insert(m.second.begin(), m.second.end());
				}

				// TODO: multi-threading for better performance

				// 
				// Steps 2 and 3 of TyPM: Collecting depedent modules
				// and resolving targets within  on dependent modules
				//
#ifdef FUNCTION_AS_TARGET_TYPE
				bool NextIter = resolveFunctionTargets();
#else // struct as target type
				bool NextIter = resolveStructTargets();
#endif

				if (!NextIter) {
					// Done with the iteration
					MIdx = 0;
					return false;
				}

				// Reset the map when phase >= 2
				moPropMapV.clear();
				moPropMapAll.clear();
				ParsedModuleTypeICallMap.clear();
				ParsedModuleTypeDCallMap.clear();
			}

			++AnalysisPhase;
			MIdx = 0;
			if (AnalysisPhase <= MAX_PHASE_CG) {
				OP<<"\n\n=== Move to phase "<<AnalysisPhase<<" ===\n\n";
				return true;
			}
		}

		return false;
	}

	void CallGraphPass::processResults() {

		// Load traces for evaluation
		// Key: hash of SrcLn for caller
		map<size_t, set<size_t>> hashedTraces;
		map<size_t, SrcLn> hashSrcMap;
		LoadTraces(hashedTraces, hashSrcMap);
		size_t TraceCount = 0;
		for (auto T : hashedTraces) {
			TraceCount += T.second.size();
		}
		OP<<"@@ Trace size: "<<TraceCount<<"\n";


		for (auto T : hashedTraces) {
			if (calleesSrcMap.find(T.first) == calleesSrcMap.end())
				continue;
			for (auto calleehash : T.second) {
				if (srcLnHashSet.find(calleehash) == srcLnHashSet.end())
					continue;
				if (addrTakenFuncHashSet.find(calleehash) == 
						addrTakenFuncHashSet.end())
					continue;
				if (calleesSrcMap[T.first].count(calleehash)) {
					// the callee is in the target set
					SrcLn Caller = hashSrcMap[T.first];
					OP<<"@ Found callee for: "<<Caller.Src<<" +"<<Caller.Ln<<"\n";
				}
				else if (L1CalleesSrcMap[T.first].count(calleehash)){
					// false negative
					OP<<"!! Cannot find callee\n";
					SrcLn Caller = hashSrcMap[T.first];
					SrcLn Callee = hashSrcMap[calleehash];
					OP<<"@ Caller: "<<Caller.Src<<" +"<<Caller.Ln<<"\n";
					OP<<"\t@ Callee: "<<Callee.Src<<" +"<<Callee.Ln<<"\n";
				}
			}
		}
	}
