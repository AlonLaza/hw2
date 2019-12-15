package il.ac.bgu.cs.formalmethodsintro.base;

import java.io.InputStream;
import java.util.List;
import java.util.Map;
import java.util.Set;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ActionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ConditionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationResult;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

/**
 * Interface for the entry point class to the HW in this class. Our
 * client/testing code interfaces with the student solutions through this
 * interface only. <br>
 * More about facade: {@linkplain http://www.vincehuston.org/dp/facade.html}.
 */
public class FvmFacade {

	private static FvmFacade INSTANCE = null;

	/**
	 *
	 * @return an instance of this class.
	 */
	public static FvmFacade get() {
		if (INSTANCE == null) {
			INSTANCE = new FvmFacade();
		}
		return INSTANCE;
	}

	/**
	 * Checks whether a transition system is action deterministic. I.e., if for any
	 * given p and α there exists only a single tuple (p,α,q) in →. Note that this
	 * must be true even for non-reachable states.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param <P> Type of atomic propositions.
	 * @param ts  The transition system being tested.
	 * @return {@code true} iff the action is deterministic.
	 */
	public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
		for (TSTransition transition : ts.getTransitions()) {
			for (TSTransition transition_compared : ts.getTransitions()) {
				if ((!transition.equals(transition_compared))
						&& transition.getFrom().equals(transition_compared.getFrom())
						&& transition.getAction().equals(transition_compared.getAction())) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Checks whether an action is ap-deterministic (as defined in class), in the
	 * context of a given {@link TransitionSystem}.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param <P> Type of atomic propositions.
	 * @param ts  The transition system being tested.
	 * @return {@code true} iff the action is ap-deterministic.
	 */
	public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
		if (ts.getInitialStates().size() > 1) {
			return false;
		}

		for (S state : ts.getStates()) {
			for (S state_of_post_s : this.post(ts, state)) {
				for (S another_state_of_post_s : this.post(ts, state)) {
					if ((!state_of_post_s.equals(another_state_of_post_s))
							&& ts.getLabel(state_of_post_s).equals(ts.getLabel(another_state_of_post_s))) {
						return false;
					}
				}
			}
		}
		return true;
	}

	/**
	 * Checks whether an alternating sequence is an execution of a
	 * {@link TransitionSystem}, as defined in class.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param <P> Type of atomic propositions.
	 * @param ts  The transition system being tested.
	 * @param e   The sequence that may or may not be an execution of {@code ts}.
	 * @return {@code true} iff {@code e} is an execution of {@code ts}.
	 */
	public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
		if (!(ts.getInitialStates().contains(e.head()))) {
			return false;
		}
		if (!(isStateTerminal(ts, e.last()))) {
			return false;
		}
		return e.isExecutionFragment(ts);
	}

	/**
	 * Checks whether an alternating sequence is an execution fragment of a
	 * {@link TransitionSystem}, as defined in class.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param <P> Type of atomic propositions.
	 * @param ts  The transition system being tested.
	 * @param e   The sequence that may or may not be an execution fragment of
	 *            {@code ts}.
	 * @return {@code true} iff {@code e} is an execution fragment of {@code ts}.
	 */
	public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
		// check if the first state is reachable
		if (!(reach(ts).contains(e.head()))) {
			return false;
		}
		return e.isExecutionFragment(ts);
	}

	/**
	 * Checks whether an alternating sequence is an initial execution fragment of a
	 * {@link TransitionSystem}, as defined in class.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param <P> Type of atomic propositions.
	 * @param ts  The transition system being tested.
	 * @param e   The sequence that may or may not be an initial execution fragment
	 *            of {@code ts}.
	 * @return {@code true} iff {@code e} is an execution fragment of {@code ts}.
	 */
	public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
		if (!(ts.getInitialStates().contains(e.head()))) {
			return false;
		}
		return e.isExecutionFragment(ts);
	}

	/**
	 * Checks whether an alternating sequence is a maximal execution fragment of a
	 * {@link TransitionSystem}, as defined in class.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param <P> Type of atomic propositions.
	 * @param ts  The transition system being tested.
	 * @param e   The sequence that may or may not be a maximal execution fragment
	 *            of {@code ts}.
	 * @return {@code true} iff {@code e} is a maximal fragment of {@code ts}.
	 */
	public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
		// check if the first state is reachable
		if (!(reach(ts).contains(e.head()))) {
			return false;
		}
		if (!(isStateTerminal(ts, e.last()))) {
			return false;
		}
		return e.isExecutionFragment(ts);
	}

	/**
	 * Checks whether a state in {@code ts} is terminal.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param ts  Transition system of {@code s}.
	 * @param s   The state being tested for terminality.
	 * @return {@code true} iff state {@code s} is terminal in {@code ts}.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
		if (!ts.getStates().contains(s)) {
			throw new StateNotFoundException("State " + s + " not found");
		}
		return post(ts, s).isEmpty();
	}

	/**
	 * @param <S> Type of states.
	 * @param ts  Transition system of {@code s}.
	 * @param s   A state in {@code ts}.
	 * @return All the states in {@code Post(s)}, in the context of {@code ts}.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
		if (!ts.getStates().contains(s)) {
			throw new StateNotFoundException("State " + s + " not found");
		}
		Set<S> post_s = new HashSet<>();
		for (TSTransition transition : ts.getTransitions()) {
			if (transition.getFrom().equals(s)) {
				post_s.add((S) transition.getTo());
			}
		}
		return post_s;
	}

	/**
	 * @param <S> Type of states.
	 * @param ts  Transition system of {@code s}.
	 * @param c   States in {@code ts}.
	 * @return All the states in {@code Post(s)} where {@code s} is a member of
	 *         {@code c}, in the context of {@code ts}.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
		Set<S> post_c = new HashSet<>();
		for (S state : c) {
			post_c.addAll(post(ts, state));
		}
		return post_c;
	}

	/**
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param ts  Transition system of {@code s}.
	 * @param s   A state in {@code ts}.
	 * @param a   An action.
	 * @return All the states that {@code ts} might transition to from {@code s},
	 *         when action {@code a} is selected.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
		if (!ts.getStates().contains(s)) {
			throw new StateNotFoundException("State " + s + " not found");
		}
		Set<S> post_s_a = new HashSet<>();
		for (TSTransition transition : ts.getTransitions()) {
			if (transition.getFrom().equals(s) && transition.getAction().equals(a)) {
				post_s_a.add((S) transition.getTo());
			}
		}
		return post_s_a;
	}

	/**
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param ts  Transition system of {@code s}.
	 * @param c   Set of states in {@code ts}.
	 * @param a   An action.
	 * @return All the states that {@code ts} might transition to from any state in
	 *         {@code c}, when action {@code a} is selected.
	 */
	public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
		Set<S> post_c_a = new HashSet<>();
		for (S state : c) {
			post_c_a.addAll(post(ts, state, a));
		}
		return post_c_a;
	}

	/**
	 * @param <S> Type of states.
	 * @param ts  Transition system of {@code s}.
	 * @param s   A state in {@code ts}.
	 * @return All the states in {@code Pre(s)}, in the context of {@code ts}.
	 */
	public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
		if (!ts.getStates().contains(s)) {
			throw new StateNotFoundException("State " + s + " not found");
		}
		Set<S> pre_s = new HashSet<>();
		for (TSTransition transition : ts.getTransitions()) {
			if (transition.getTo().equals(s)) {
				pre_s.add((S) transition.getFrom());
			}
		}
		return pre_s;
	}

	/**
	 * @param <S> Type of states.
	 * @param ts  Transition system of {@code s}.
	 * @param c   States in {@code ts}.
	 * @return All the states in {@code Pre(s)} where {@code s} is a member of
	 *         {@code c}, in the context of {@code ts}.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
		Set<S> pre_c = new HashSet<>();
		for (S state : c) {
			pre_c.addAll(pre(ts, state));
		}
		return pre_c;
	}

	/**
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param ts  Transition system of {@code s}.
	 * @param s   A state in {@code ts}.
	 * @param a   An action.
	 * @return All the states that {@code ts} might transitioned from, when in
	 *         {@code s}, and the last action was {@code a}.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
		if (!ts.getStates().contains(s)) {
			throw new StateNotFoundException("State " + s + " not found");
		}
		Set<S> pre_s_a = new HashSet<>();
		for (TSTransition transition : ts.getTransitions()) {
			if (transition.getTo().equals(s) && transition.getAction().equals(a)) {
				pre_s_a.add((S) transition.getFrom());
			}
		}
		return pre_s_a;
	}

	/**
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param ts  Transition system of {@code s}.
	 * @param c   Set of states in {@code ts}.
	 * @param a   An action.
	 * @return All the states that {@code ts} might transitioned from, when in any
	 *         state in {@code c}, and the last action was {@code a}.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
		Set<S> pre_c_a = new HashSet<>();
		for (S state : c) {
			pre_c_a.addAll(pre(ts, state, a));
		}
		return pre_c_a;
	}

	/**
	 * Implements the {@code reach(TS)} function.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param ts  Transition system of {@code s}.
	 * @return All states reachable in {@code ts}.
	 */
	public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
		Set<S> reach_states = ts.getInitialStates();
		if (reach_states.isEmpty())
			return new HashSet<>();
		return reach(ts, new HashSet<>(reach_states), new HashSet<>(reach_states));
	}
	
	public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts, Set<S> reach_states, Set<S> states_to_explore) {
		if (states_to_explore.isEmpty())
			return reach_states;
		Set<S> explored_states = this.post(ts, states_to_explore);
		explored_states.removeAll(reach_states);
		reach_states.addAll(explored_states);
		return reach(ts, reach_states, explored_states);
	}

	/**
	 * Compute the synchronous product of two transition systems.
	 *
	 * @param <S1> Type of states in the first system.
	 * @param <S2> Type of states in the first system.
	 * @param <A>  Type of actions (in both systems).
	 * @param <P>  Type of atomic propositions (in both systems).
	 * @param ts1  The first transition system.
	 * @param ts2  The second transition system.
	 *
	 * @return A transition system that represents the product of the two.
	 */
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
			TransitionSystem<S2, A, P> ts2) {

		TransitionSystem<Pair<S1, S2>, A, P> interleave_transition_system = new TransitionSystem();

		// Creating the new states set
		CreatingInterleaveStates(interleave_transition_system, ts1, ts2);

		// Creating the action set
		CreatingInterleaveActions(interleave_transition_system, ts1, ts2);

		// Creating transitions
		CreatingInterleaveTransitions(interleave_transition_system, ts1, ts2);

		// Creating the initial states
		CreatingInterleaveInitialStates(interleave_transition_system, ts1, ts2);

		// Creating the atomic Propositions
		CreatingInterleavePropositions(interleave_transition_system, ts1, ts2);

		// Creating the new labeling function
		CreatingInterleaveLabeling(interleave_transition_system, ts1, ts2);

		return interleave_transition_system;
	}

	/**
	 * Compute the synchronous product of two transition systems.
	 *
	 * @param <S1>               Type of states in the first system.
	 * @param <S2>               Type of states in the first system.
	 * @param <A>                Type of actions (in both systems).
	 * @param <P>                Type of atomic propositions (in both systems).
	 * @param ts1                The first transition system.
	 * @param ts2                The second transition system.
	 * @param handShakingActions Set of actions both systems perform together.
	 *
	 * @return A transition system that represents the product of the two.
	 */
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
			TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {

		TransitionSystem<Pair<S1, S2>, A, P> interleave_transition_system = new TransitionSystem();

		// Creating the new states set
		CreatingInterleaveStates(interleave_transition_system, ts1, ts2);

		// Creating the action set
		CreatingInterleaveActions(interleave_transition_system, ts1, ts2);

		// Creating transitions
		CreatingInterleaveSynchronizeTransitions(interleave_transition_system, ts1, ts2, handShakingActions);

		// Creating the initial states
		CreatingInterleaveInitialStates(interleave_transition_system, ts1, ts2);

		// Creating the atomic Propositions
		CreatingInterleavePropositions(interleave_transition_system, ts1, ts2);

		// Creating the new labeling function
		CreatingInterleaveLabeling(interleave_transition_system, ts1, ts2);

		return interleave_transition_system;

	}

	/**
	 * Creates a new {@link ProgramGraph} object.
	 *
	 * @param <L> Type of locations in the graph.
	 * @param <A> Type of actions of the graph.
	 * @return A new program graph instance.
	 */
	public <L, A> ProgramGraph<L, A> createProgramGraph() {
		return new ProgramGraph<>();
	}

	/**
	 * Interleaves two program graphs.
	 *
	 * @param <L1> Type of locations in the first graph.
	 * @param <L2> Type of locations in the second graph.
	 * @param <A>  Type of actions in BOTH GRAPHS.
	 * @param pg1  The first program graph.
	 * @param pg2  The second program graph.
	 * @return Interleaved program graph.
	 */
	public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
		ProgramGraph<Pair<L1, L2>, A> interleavedPG = new ProgramGraph<>();
		
		// Set the initialConditions
		Set<List<String>> initialConditions = new HashSet<>(pg1.getInitalizations());
		initialConditions.retainAll(pg2.getInitalizations());
		interleavedPG.getInitalizations().addAll(initialConditions);
		
		// Set all the interleaved locations
		for(L1 loc1 : pg1.getLocations()) {
			for(L2 loc2 : pg2.getLocations()) {
				if (pg1.getInitialLocations().contains(loc1) && pg2.getInitialLocations().contains(loc2))
					interleavedPG.setInitial(new Pair(loc1, loc2), true);
				else
					interleavedPG.addLocation(new Pair(loc1, loc2));
			}
		}
		
		// Set all the transitions PGTransition
		for(PGTransition<L1, A> transition1 : pg1.getTransitions()) { 
			for(PGTransition<L2, A> transition2 : pg2.getTransitions()) {
				// Transition by pg1
				interleavedPG.addTransition(new PGTransition<Pair<L1, L2>, A>(
						new Pair(transition1.getFrom(), transition2.getFrom()),
						transition1.getCondition(),
						transition1.getAction(),
						new Pair(transition1.getTo(), transition2.getFrom())));
				// Transition by pg2
				interleavedPG.addTransition(new PGTransition<Pair<L1, L2>, A>(
						new Pair(transition1.getFrom(), transition2.getFrom()),
						transition2.getCondition(),
						transition2.getAction(),
						new Pair(transition1.getFrom(), transition2.getTo())));
			}
		}
		return interleavedPG;
	}

	/**
	 * Creates a {@link TransitionSystem} representing the passed circuit.
	 *
	 * @param c The circuit to translate into a {@link TransitionSystem}.
	 * @return A {@link TransitionSystem} representing {@code c}.
	 */
	public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(
			Circuit c) {
		throw new java.lang.UnsupportedOperationException();
	}

	/**
	 * Creates a {@link TransitionSystem} from a program graph.
	 *
	 * @param <L>           Type of program graph locations.
	 * @param <A>           Type of program graph actions.
	 * @param pg            The program graph to be translated into a transition
	 *                      system.
	 * @param actionDefs    Defines the effect of each action.
	 * @param conditionDefs Defines the conditions (guards) of the program graph.
	 * @return A transition system representing {@code pg}.
	 */
	public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(
			ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {

		TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts = new TransitionSystem();

		// Create Eval
		Set<Map<String, Object>> eval = new HashSet();
		for (List<String> initializtion : pg.getInitalizations()) {
			Map<String, Object> atomic_eval = new HashMap();
			for (String atomic_init : initializtion) {
				atomic_eval.putIfAbsent((atomic_init.substring(0, atomic_init.indexOf(':')).replaceAll("\\s+", "")),
						Integer.parseInt((atomic_init.substring(atomic_init.indexOf('=') + 1)).replaceAll("\\s+", "")));
			}
			eval.add(atomic_eval);
		}

		// Creating locations
		for (L loc : pg.getLocations()) {
			for (Map<String, Object> atomic_eval : eval) {
				ts.addState(new Pair(loc, atomic_eval));
			}
		}
		// Creating initial locations
		for (Pair<L, Map<String, Object>> state : ts.getStates()) {
			if (pg.getInitialLocations().contains(state.first)) {
				ts.addInitialState(state);
			}
		}

		// Creating actions
		for (PGTransition pg_transition : pg.getTransitions()) {
			ts.addAction((A) pg_transition.getAction());
		}

		// Creating list of all the conditions
		Set<String> conditions = new HashSet<String>();
		for (PGTransition transition : pg.getTransitions()) {
			conditions.add(transition.getCondition());
		}

		// Add propositions and Labeling
		for (Pair<L, Map<String, Object>> state : ts.getStates()) {
			labelNew_TS_stateFromGraph(ts, state, conditions, conditionDefs);
		}


		//Create the list state to explore
		List<Pair<L, Map<String, Object>>> states_to_explore = new LinkedList<>();
		states_to_explore.addAll(ts.getInitialStates());
		
		// Create transitions
		state_and_transition_exploration(states_to_explore, ts, pg, actionDefs, conditionDefs, conditions);
		
		return ts;
	}

	public <L, A> void state_and_transition_exploration(List<Pair<L, Map<String, Object>>> states_to_explore,
			TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts, ProgramGraph<L, A> pg,
			Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs, Set<String> conditions) {
		
		Pair<L, Map<String, Object>> state_to_explore = states_to_explore.remove(0);
		for (PGTransition transition : pg.getTransitions()) {
			if (transition.getFrom().equals(state_to_explore.first)
					&& ConditionDef.evaluate(conditionDefs, state_to_explore.second, transition.getCondition())) {
				Map<String, Object> newEval = ActionDef.effect(actionDefs, state_to_explore.second, transition.getAction());
				Pair<L, Map<String, Object>> newState = new Pair(transition.getTo(), newEval);
				ts.addState(newState);
				labelNew_TS_stateFromGraph(ts, newState, conditions, conditionDefs);
				ts.addTransition(new TSTransition(state_to_explore, (A) transition.getAction(), newState));
				states_to_explore.add(newState);
			}
		}
		if(states_to_explore.size()>0) {
			state_and_transition_exploration(states_to_explore, ts, pg, actionDefs, conditionDefs, conditions);
		}
	}

	/**
	 * Creates a transition system representing channel system {@code cs}.
	 *
	 * @param <L> Type of locations in the channel system.
	 * @param <A> Type of actions in the channel system.
	 * @param cs  The channel system to be translated into a transition system.
	 * @return A transition system representing {@code cs}.
	 */
	public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
			ChannelSystem<L, A> cs) {

		Set<ActionDef> actions = Collections.singleton(new ParserBasedActDef());
		Set<ConditionDef> conditions = Collections.singleton(new ParserBasedCondDef());
		return transitionSystemFromChannelSystem(cs, actions, conditions);
	}

	public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
			ChannelSystem<L, A> cs, Set<ActionDef> actions, Set<ConditionDef> conditions) {
		throw new java.lang.UnsupportedOperationException();
	}

	/**
	 * Construct a program graph from nanopromela code.
	 *
	 * @param filename The nanopromela code.
	 * @return A program graph for the given code.
	 * @throws Exception If the code is invalid.
	 */
	public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
		throw new java.lang.UnsupportedOperationException();
	}

	/**
	 * Construct a program graph from nanopromela code.
	 *
	 * @param nanopromela The nanopromela code.
	 * @return A program graph for the given code.
	 * @throws Exception If the code is invalid.
	 */
	public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
		throw new java.lang.UnsupportedOperationException();
	}

	/**
	 * Construct a program graph from nanopromela code.
	 *
	 * @param inputStream The nanopromela code.
	 * @return A program graph for the given code.
	 * @throws Exception If the code is invalid.
	 */
	public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
		throw new java.lang.UnsupportedOperationException();
	}

	/**
	 * Creates a transition system from a transition system and an automaton.
	 *
	 * @param <Sts>  Type of states in the transition system.
	 * @param <Saut> Type of states in the automaton.
	 * @param <A>    Type of actions in the transition system.
	 * @param <P>    Type of atomic propositions in the transition system, which is
	 *               also the type of the automaton alphabet.
	 * @param ts     The transition system.
	 * @param aut    The automaton.
	 * @return The product of {@code ts} with {@code aut}.
	 */
	public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts,
			Automaton<Saut, P> aut) {
		throw new java.lang.UnsupportedOperationException();
	}

	/**
	 * Verify that a system satisfies an omega regular property.
	 *
	 * @param <S>    Type of states in the transition system.
	 * @param <Saut> Type of states in the automaton.
	 * @param <A>    Type of actions in the transition system.
	 * @param <P>    Type of atomic propositions in the transition system, which is
	 *               also the type of the automaton alphabet.
	 * @param ts     The transition system.
	 * @param aut    A Büchi automaton for the words that do not satisfy the
	 *               property.
	 * @return A VerificationSucceeded object or a VerificationFailed object with a
	 *         counterexample.
	 */
	public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts,
			Automaton<Saut, P> aut) {
		throw new java.lang.UnsupportedOperationException();
	}

	/**
	 * Translation of Linear Temporal Logic (LTL) formula to a Nondeterministic
	 * Büchi Automaton (NBA).
	 *
	 * @param <L> Type of resultant automaton transition alphabet
	 * @param ltl The LTL formula represented as a parse-tree.
	 * @return An automaton A such that L_\omega(A)=Words(ltl)
	 */
	public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
		throw new java.lang.UnsupportedOperationException();
	}

	/**
	 * A translation of a Generalized Büchi Automaton (GNBA) to a Nondeterministic
	 * Büchi Automaton (NBA).
	 *
	 * @param <L>    Type of resultant automaton transition alphabet
	 * @param mulAut An automaton with a set of accepting states (colors).
	 * @return An equivalent automaton with a single set of accepting states.
	 */
	public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
		throw new java.lang.UnsupportedOperationException();
	}

	public <S1, S2, A, P> void CreatingInterleaveStates(
			TransitionSystem<Pair<S1, S2>, A, P> interleave_transition_system, TransitionSystem<S1, A, P> ts1,
			TransitionSystem<S2, A, P> ts2) {
		for (S1 state_s1 : ts1.getStates()) {
			for (S2 state_s2 : ts2.getStates()) {
				interleave_transition_system.addState(new Pair(state_s1, state_s2));
			}
		}
	}

	public <S1, S2, A, P> void CreatingInterleaveActions(
			TransitionSystem<Pair<S1, S2>, A, P> interleave_transition_system, TransitionSystem<S1, A, P> ts1,
			TransitionSystem<S2, A, P> ts2) {
		interleave_transition_system.addAllActions(ts1.getActions());
		interleave_transition_system.addAllActions(ts2.getActions());
	}

	public <S1, S2, A, P> void CreatingInterleaveTransitions(
			TransitionSystem<Pair<S1, S2>, A, P> interleave_transition_system, TransitionSystem<S1, A, P> ts1,
			TransitionSystem<S2, A, P> ts2) {

		// Adding the transitions from ts1
		for (TSTransition transition_ts1 : ts1.getTransitions()) {
			for (Pair<S1, S2> state : interleave_transition_system.getStates()) {
				if (state.first.equals(transition_ts1.getFrom())) {
					interleave_transition_system.addTransition(new TSTransition(state, transition_ts1.getAction(),
							new Pair(transition_ts1.getTo(), state.second)));
				}
			}
		}
		// Adding the transitions from ts2
		for (TSTransition transition_ts2 : ts2.getTransitions()) {
			for (Pair<S1, S2> state : interleave_transition_system.getStates()) {
				if (state.second.equals(transition_ts2.getFrom())) {
					interleave_transition_system.addTransition(new TSTransition(state, transition_ts2.getAction(),
							new Pair(state.first, transition_ts2.getTo())));
				}
			}
		}
	}

	public <S1, S2, A, P> void CreatingInterleaveInitialStates(
			TransitionSystem<Pair<S1, S2>, A, P> interleave_transition_system, TransitionSystem<S1, A, P> ts1,
			TransitionSystem<S2, A, P> ts2) {
		for (Pair<S1, S2> state : interleave_transition_system.getStates()) {
			if ((ts1.getInitialStates().contains(state.first)) && (ts2.getInitialStates().contains(state.second))) {
				interleave_transition_system.addInitialState(state);
			}
		}
	}

	public <S1, S2, A, P> void CreatingInterleavePropositions(
			TransitionSystem<Pair<S1, S2>, A, P> interleave_transition_system, TransitionSystem<S1, A, P> ts1,
			TransitionSystem<S2, A, P> ts2) {
		interleave_transition_system.addAllAtomicPropositions(ts1.getAtomicPropositions());
		interleave_transition_system.addAllAtomicPropositions(ts2.getAtomicPropositions());
	}

	public <S1, S2, A, P> void CreatingInterleaveLabeling(
			TransitionSystem<Pair<S1, S2>, A, P> interleave_transition_system, TransitionSystem<S1, A, P> ts1,
			TransitionSystem<S2, A, P> ts2) {
		for (Pair<S1, S2> interleave_state : interleave_transition_system.getStates()) {
			for (P atomic_pro : ts1.getLabel(interleave_state.first)) {
				interleave_transition_system.addToLabel(interleave_state, atomic_pro);
			}
			for (P atomic_pro : ts2.getLabel(interleave_state.second)) {
				interleave_transition_system.addToLabel(interleave_state, atomic_pro);
			}
		}
	}

	public <S1, S2, A, P> void CreatingInterleaveSynchronizeTransitions(
			TransitionSystem<Pair<S1, S2>, A, P> interleave_transition_system, TransitionSystem<S1, A, P> ts1,
			TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {

		// Adding the transitions from ts1
		for (TSTransition transition_ts1 : ts1.getTransitions()) {
			if (!(handShakingActions.contains(transition_ts1.getAction()))) {
				for (Pair<S1, S2> state : interleave_transition_system.getStates()) {
					if (state.first.equals(transition_ts1.getFrom())) {
						interleave_transition_system.addTransition(new TSTransition(state, transition_ts1.getAction(),
								new Pair(transition_ts1.getTo(), state.second)));
					}
				}
			}
		}
		// Adding the transitions from ts2
		for (TSTransition transition_ts2 : ts2.getTransitions()) {
			if (!(handShakingActions.contains(transition_ts2.getAction()))) {
				for (Pair<S1, S2> state : interleave_transition_system.getStates()) {
					if (state.second.equals(transition_ts2.getFrom())) {
						interleave_transition_system.addTransition(new TSTransition(state, transition_ts2.getAction(),
								new Pair(state.first, transition_ts2.getTo())));
					}
				}
			}
		}
		for (A synch_action : handShakingActions) {
			for (TSTransition transition_ts1 : ts1.getTransitions()) {
				for (TSTransition transition_ts2 : ts2.getTransitions()) {
					if (transition_ts1.getAction().equals(synch_action)
							&& transition_ts2.getAction().equals(synch_action)) {
						interleave_transition_system.addTransition(
								new TSTransition(new Pair(transition_ts1.getFrom(), transition_ts2.getFrom()),
										synch_action, new Pair(transition_ts1.getTo(), transition_ts2.getTo())));
					}
				}
			}

		}
	}

	public <L, A> void labelNew_TS_stateFromGraph(TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts,
			Pair<L, Map<String, Object>> state, Set<String> conditions, Set<ConditionDef> conditionDefs) {
		ts.addToLabel(state, (String) state.first);
		for (String condition : conditions) {
			if (ConditionDef.evaluate(conditionDefs, state.second, condition)) {
				ts.addToLabel(state, condition);
			}
		}
	}

}