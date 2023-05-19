#ifndef _CALL_GRAPH_H
#define _CALL_GRAPH_H

#include "Analyzer.h"
#include "MLTA.h"
#include "TyPM.h"
#include "Config.h"
#include <time.h>

class CallGraphPass : 
	public virtual IterativeModulePass, public virtual TyPM {

	private:

		//
		// Variables
		//

		// Index of the module
		int MIdx;


		//
		// Methods
		//

		// Phases
		void PhaseMLTA(Function *F);
		void PhaseTyPM(Function *F);


	public:
		static int AnalysisPhase;

		CallGraphPass(GlobalContext *Ctx_)
			: IterativeModulePass(Ctx_, "CallGraph"), 
			TyPM(Ctx_) {

				LoadElementsStructNameMap(Ctx->Modules);
				MIdx = 0;

				time_t my_time = time(NULL);
				OP<<"# TIME: "<<ctime(&my_time)<<"\n";
			}

		virtual bool doInitialization(llvm::Module *);
		virtual bool doFinalization(llvm::Module *);
		virtual bool doModulePass(llvm::Module *);

		void processResults();

};

#endif
