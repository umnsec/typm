#ifndef _TYPE_BASED_DEPENDENCE_MODULARIZATION_H
#define _TYPE_BASED_DEPENDENCE_MODULARIZATION_H

#include "Analyzer.h"
#include "MLTA.h"
#include "Config.h"


class TyPM : public MLTA {

	protected:

		//
		// Variables
		// 

		//GlobalContext *Ctx;
		set<CallInst *>CallSet;
		set<CallInst *>ICallSet;
		set<CallInst *>MatchedICallSet;
		set<StoreInst *>StoreInstSet;


		//
		// Structures for type-based dependece analysis
		// 

		// Set of target types
		set<size_t>TTySet;
		DenseMap<size_t, set<Module *>> TargetDataAllocModules;

		set<string> OutScopeFuncNames;

		// Propagation maps
		DenseMap<Module*, set<map<Module*, set<size_t>>>>moTyPropMap;
		DenseMap<pair<Module*, size_t>, set<Module*>>moPropMap;
		// Versatile map for refined indirect calls
		DenseMap<pair<Module*, size_t>, set<Module*>>moPropMapV;

		// Which fields of a type have been stored to
		DenseMap<Module *, map<Type *, set<int>>> storedTypeIdxMap;

		// All casts in a module
		DenseMap<Module *, map<Type *, set<Type *>>> CastFromMap;
		DenseMap<Module *, map<Type *, set<Type *>>> CastToMap;

		// Function types that can be held by the GV
		DenseMap<GlobalVariable *, set<Type *>>GVFuncTypesMap;
		// Modules that store function pointers of the type to the global
		DenseMap<pair<uint64_t, size_t>, set<Module *>>TypesFromModuleGVMap;
		// Modules that load function pointers of the type from the global
		DenseMap<pair<uint64_t, size_t>, set<Module *>>TypesToModuleGVMap;

		// For caching
		DenseMap<size_t, FuncSet> MatchedICallTypeMap;
		DenseMap<pair<Module *, size_t>, set<Module *>> ResolvedDepModulesMap;
		DenseMap<pair<Module *, Type *>, set<Type *>>ParsedTypeMap;
		DenseMap<GlobalVariable *, set<Type *>>ParsedGlobalTypesMap;
		DenseMap<pair<Module *, Module *>, set<Type *>>ParsedModuleTypeICallMap;
		DenseMap<pair<Module *, Module *>, set<Type *>>ParsedModuleTypeDCallMap;



		//
		// Methods
		//

		// Custom isTargetTy to decide if it is interested type
		bool isTargetTy(Type *);
		// A type such as struct that can contain the target type
		bool isContainerTy(Type *);


		// API for getting dependent modules based on the target type
		bool resolveFunctionTargets();
		bool resolveStructTargets();
		void getDependentModulesTy(size_t TyH, Module *M, set<Module *>&MSet);
		// API for getting dependent modules based on the target value
		void getDependentModulesV(Value *TV,	Module *M, set<Module *>&MSet);


		// Typecasting analysis
		void findCastsInGV(GlobalVariable *,
				set<User *> &CastSet);
		void findCastsInFunction(Function *, set<User *> &CastSet);
		void processCasts(set<User *> &CastSet, Module *M);
		
		
		// Analyze globals and function calls for potential types of
		// data flows
		void findTargetTypesInInitializer(GlobalVariable *, Module *, 
				set<Type *> &TargetTypes);
		void parseUsesOfGV(GlobalVariable *GV, Value *, 
				Module *, set<Value *> &Visited);
		bool parseUsesOfValue(Value *V, set<Type *> &ReadTypes, 
				set<Type *> &WrittenTypes, Module *M);
		void findTargetTypesInValue(Value *V, 
				set<Type *> &TargetTypes, Module *M);
		void parseTargetTypesInCalls(CallInst *CI, Function *CF);


		// Maintain the maps
		// mapping between modules, through calls
		void addPropagation(Module *ToM, Module *FromM, Type *Ty, 
				bool isICall = false);
		// mapping between module and global, through globals
		void addModuleToGVType(Type *Ty, Module *M, GlobalVariable *GV);
		void addGVToModuleType(Type *Ty, GlobalVariable *GV, Module *M);



		// Parse functions for various semantic information
		void findStoredTypeIdxInFunction(Function * F);
		void findTargetAllocInFunction(Function * F);
		void mapDeclToActualFuncs(FuncSet &FS);

	public:

		// Merged map
		static DenseMap<pair<Module*, size_t>, set<Module*>>moPropMapAll;

		TyPM(GlobalContext *Ctx_) : MLTA(Ctx_) {
			LoadTargetTypes(TTySet);
			LoadOutScopeFuncs(OutScopeFuncNames);
		}

};

#endif
