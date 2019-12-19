package il.ac.bgu.cs.fvm.examples;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;


// Figure 2.12 in the book
public class MutualExclusionUsingArbiter {
    public enum TsState { NonCrit, Crit }
    public enum ArState { Unlock, Lock }
    public enum MuAction{ Request, Release }
    
	static final FvmFacade fvmFacadeImpl = FvmFacade.get();
	
	static public TransitionSystem<TsState, MuAction, String> buildP() {
		TransitionSystem<TsState, MuAction, String> ts = new TransitionSystem<>();

		ts.addAllStates(TsState.values());
        ts.addAllActions(MuAction.values());
		ts.addInitialState(TsState.NonCrit);

		ts.addTransitionFrom(TsState.NonCrit).action(MuAction.Request).to(TsState.Crit);
        ts.addTransitionFrom(TsState.Crit).action(MuAction.Release).to(TsState.NonCrit);
        return ts;
    }

 
	static public TransitionSystem<ArState, MuAction, String> buildArbiter() {
		TransitionSystem<ArState, MuAction, String> ts = new TransitionSystem<>();

		ts.addAllStates(ArState.values());
        ts.addAllActions(MuAction.values());
		ts.addInitialState(ArState.Unlock);

		ts.addTransition(new TSTransition<>(ArState.Unlock, MuAction.Request, ArState.Lock));
		ts.addTransition(new TSTransition<>(ArState.Lock, MuAction.Release, ArState.Unlock));

        return ts;
    }

}
