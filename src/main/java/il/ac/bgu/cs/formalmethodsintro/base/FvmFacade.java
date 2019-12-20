package il.ac.bgu.cs.formalmethodsintro.base;

import java.io.InputStream;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.ArrayList;
import java.util.Vector;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser;
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
import org.antlr.v4.runtime.ParserRuleContext;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

/**
 * Interface for the entry point class to the HW in this class. Our
 * client/testing code interfaces with the student solutions through this
 * interface only. <br>
 * More about facade: {@linkplain ://www.vincehuston.org/dp/facade.html}.
 */
public class FvmFacade {

	private static FvmFacade INSTANCE = null;

	/**
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
	 * @return A transition system that represents the product of the two.
	 */
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
			TransitionSystem<S2, A, P> ts2) {

		TransitionSystem<Pair<S1, S2>, A, P> interleave_transition_system = new TransitionSystem();

		// Creating the new states set
		CreatingInterleaveStates(interleave_transition_system, ts1, ts2);

		// Creating the action set
		CreatingInterleaveActions(interleave_transition_system, ts1, ts2);

		// Creating the initial states
		CreatingInterleaveInitialStates(interleave_transition_system, ts1, ts2);

		// Creating transitions
		CreatingInterleaveTransitions(interleave_transition_system, ts1, ts2);

		Set<Pair<S1, S2>> reaches = reach(interleave_transition_system);
		Set<Pair<S1, S2>> unreachable = new HashSet<>();

		for (Pair<S1, S2> state : interleave_transition_system.getStates()) {
			if (!reaches.contains(state)) {
				unreachable.add(state);
			}
		}
		for (Pair<S1, S2> state : unreachable) {
			interleave_transition_system.removeState(state);
		}

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
	 * @return A transition system that represents the product of the two.
	 */
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
			TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {

		TransitionSystem<Pair<S1, S2>, A, P> interleave_transition_system = new TransitionSystem();

		// Creating the new states set
		CreatingInterleaveStates(interleave_transition_system, ts1, ts2);

		// Creating the action set
		CreatingInterleaveActions(interleave_transition_system, ts1, ts2);

		// Creating the initial states
		CreatingInterleaveInitialStates(interleave_transition_system, ts1, ts2);
		
		// Creating transitions
		CreatingInterleaveSynchronizeTransitions(interleave_transition_system, ts1, ts2, handShakingActions);

		Set<Pair<S1, S2>> reaches = reach(interleave_transition_system);
		Set<Pair<S1, S2>> unreachable = new HashSet<>();

		for (Pair<S1, S2> state : interleave_transition_system.getStates()) {
			if (!reaches.contains(state)) {
				unreachable.add(state);
			}
		}
		for (Pair<S1, S2> state : unreachable) {
			interleave_transition_system.removeState(state);
		}
		
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
		for (L1 loc1 : pg1.getLocations()) {
			for (L2 loc2 : pg2.getLocations()) {
				if (pg1.getInitialLocations().contains(loc1) && pg2.getInitialLocations().contains(loc2))
					interleavedPG.setInitial(new Pair(loc1, loc2), true);
				else
					interleavedPG.addLocation(new Pair(loc1, loc2));
			}
		}

		// Set all the transitions PGTransition
		for (PGTransition<L1, A> transition1 : pg1.getTransitions()) {
			for (Pair<L1, L2> state : interleavedPG.getLocations()) {
				if (transition1.getFrom().equals(state.first)) {
					interleavedPG.addTransition(new PGTransition<Pair<L1, L2>, A>(
							new Pair(transition1.getFrom(), state.second), transition1.getCondition(),
							transition1.getAction(), new Pair(transition1.getTo(), state.second)));
				}
			}
		}

		for (PGTransition<L2, A> transition2 : pg2.getTransitions()) {
			for (Pair<L1, L2> state : interleavedPG.getLocations()) {
				if (transition2.getFrom().equals(state.second)) {
					interleavedPG.addTransition(new PGTransition<Pair<L1, L2>, A>(
							new Pair(state.first, transition2.getFrom()), transition2.getCondition(),
							transition2.getAction(), new Pair(state.first, transition2.getTo())));
				}
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
		TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> tsFromCircuit = new TransitionSystem<>();
		List<Map<String, Boolean>> inputsCombinations = getAllCombinations(c.getInputPortNames());
		List<Map<String, Boolean>> registersCombinations = getAllCombinations(c.getRegisterNames());
		for (Map<String, Boolean> inps_comb : inputsCombinations) {
			for (Map<String, Boolean> regs_comb : registersCombinations) {
				Pair<Map<String, Boolean>, Map<String, Boolean>> newState = new Pair(inps_comb, regs_comb);
				tsFromCircuit.addState(newState);

				// Set the AP - inputs
				for (Map.Entry<String, Boolean> entry : inps_comb.entrySet()) {
					if (entry.getValue())
						tsFromCircuit.addToLabel(newState, entry.getKey());
				}

				// Set the AP - registers
				for (Map.Entry<String, Boolean> entry : regs_comb.entrySet()) {
					if (entry.getValue())
						tsFromCircuit.addToLabel(newState, entry.getKey());
				}

				// Set the AP - outputs
				Map<String, Boolean> outputs = c.computeOutputs(inps_comb, regs_comb);
				for (Map.Entry<String, Boolean> entry : outputs.entrySet()) {
					if (entry.getValue())
						tsFromCircuit.addToLabel(newState, entry.getKey());
				}

				// Set initialized states
				Boolean initialRegs = true;
				for (Map.Entry<String, Boolean> entry : regs_comb.entrySet()) {
					if (entry.getValue()) {
						initialRegs = false;
						break;
					}
				}

				if (initialRegs)
					tsFromCircuit.addInitialState(newState);

				// Set the transitions and actions
				Map<String, Boolean> newRegistersValues = c.updateRegisters(inps_comb, regs_comb);
				for (Map<String, Boolean> comb : inputsCombinations) {
					tsFromCircuit.addTransition(new TSTransition<>(newState, comb, new Pair(comb, newRegistersValues)));
				}
			}
		}
		return tsFromCircuit;
	}

	public List<Map<String, Boolean>> getAllCombinations(Set<String> setToIterate) {
		List<Map<String, Boolean>> combinations = new ArrayList<>();
		int numOfIterationsForInputs = (int) Math.pow(2, setToIterate.size());
		for (int i = 0; i < numOfIterationsForInputs; i++) {
			Map<String, Boolean> inputsMap = new HashMap<>();
			String binaryNum = Integer.toString(i, 2);
			List<String> inputs = new ArrayList<>();
			for (String input : setToIterate) {
				inputs.add(input);
			}
			for (int j = 0; j < binaryNum.length(); j++) {
				inputsMap.put(inputs.get(j), (binaryNum.charAt(j) == '0') ? false : true);
			}
			for (int j = inputs.size() - binaryNum.length(); j > 0; j--) {
				inputsMap.put(inputs.get(j), false);
			}
			combinations.add(inputsMap);
		}
		return combinations;
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

		// Create Eval and initial states
		for (L loc : pg.getInitialLocations()) {
			Map<String, Object> eval = new HashMap<String, Object>();

			if (pg.getInitalizations().size() == 0) {
				ts.addInitialState(new Pair(loc, eval));

			} else {
				for (List<String> init : pg.getInitalizations()) {
					for (String s : init) {
						eval = ActionDef.effect(actionDefs, eval, s);
					}
					ts.addInitialState(new Pair(loc, eval));
				}
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

		// Create the list state to explore
		List<Pair<L, Map<String, Object>>> states_to_explore = new LinkedList<>(ts.getInitialStates());

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
				Map<String, Object> newEval = ActionDef.effect(actionDefs, state_to_explore.second,
						transition.getAction());
				Pair<L, Map<String, Object>> newState = new Pair(transition.getTo(), newEval);
				ts.addState(newState);
				labelNew_TS_stateFromGraph(ts, newState, conditions, conditionDefs);
				ts.addTransition(new TSTransition(state_to_explore, (A) transition.getAction(), newState));
				states_to_explore.add(newState);
			}
		}
		if (states_to_explore.size() > 0) {
			state_and_transition_exploration(states_to_explore, ts, pg, actionDefs, conditionDefs, conditions);
		}
	}

	public <L> Set<List<L>> cartesianProduct(Set<L>... sets) {
		if (sets.length < 2)
			throw new IllegalArgumentException("Can't have a product of fewer than two sets (got " + sets.length + ")");

		return _cartesianProduct(0, sets);
	}

	private <L> Set<List<L>> _cartesianProduct(int index, Set<L>... sets) {
		Set<List<L>> ret = new HashSet<List<L>>();
		if (index == sets.length) {
			ret.add(new LinkedList<L>());
		} else {
			for (L obj : sets[index]) {
				for (List<L> list : _cartesianProduct(index + 1, sets)) {
					list.add(obj);
					ret.add(list);
				}
			}
		}
		return ret;
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

		TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts = new TransitionSystem();

		List<ProgramGraph<L, A>> pgs = cs.getProgramGraphs();
		int number_of_pgs = cs.getProgramGraphs().size();
		// just to sent to the cartesianProduct function to get all the possible initial
		// states list
		Set<L>[] array_of_sets = (Set<L>[]) new Object[number_of_pgs];

		for (int i = 0; i < number_of_pgs; i++) {
			array_of_sets[i] = pgs.get(i).getInitialLocations();
		}

		Set<List<L>> cartesian_initial_states = cartesianProduct(array_of_sets);

		// doing the cut between all the initializations
		Set<List<String>> initialConditions = new HashSet<>(pgs.get(0).getInitalizations());
		for (int i = 1; i < number_of_pgs; i++) {
			initialConditions.retainAll(pgs.get(i).getInitalizations());
		}

		// Create Eval
		Map<String, Object> eval = new HashMap<String, Object>();

		for (List<String> init : initialConditions) {
			for (String s : init) {
				eval = ActionDef.effect(actions, eval, s);
			}
		}
		// creating the initial states
		for (List<L> initial_state_list : cartesian_initial_states) {
			ts.addInitialState(new Pair(initial_state_list, eval));
		}

		// Create string list of all conditions
		Set<String> conditions_string = new HashSet<>();
		for (ProgramGraph<L, A> pg : pgs) {
			for (PGTransition trans : pg.getTransitions()) {
				conditions_string.add(trans.getCondition());
			}
		}
		// create labels of the initial states
		for (Pair<List<L>, Map<String, Object>> initial_state : ts.getInitialStates()) {
			labelNew_TS_stateFromChannel(ts, initial_state, conditions, conditions_string);
		}
		// Create the list state to explore
		List<Pair<List<L>, Map<String, Object>>> states_to_explore = new LinkedList<>(ts.getInitialStates());

		// Create transitions
		channel_state_and_transition_exploration(states_to_explore, ts, pgs, actions, conditions, conditions_string);
		return ts;

	}

	public <L, A> void channel_state_and_transition_exploration(
			List<Pair<List<L>, Map<String, Object>>> states_to_explore,
			TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts, List<ProgramGraph<L, A>> pgs,
			Set<ActionDef> actions, Set<ConditionDef> conditionDefs, Set<String> conditions_string) {

		Pair<List<L>, Map<String, Object>> state_to_explore = states_to_explore.remove(0);
		ParserBasedInterleavingActDef parserBasedInterleavingActDef = new ParserBasedInterleavingActDef();
		Set<PGTransition<L, A>> all_transitions_from_state = new HashSet<>();
		for (ProgramGraph<L, A> pg : pgs) {
			for (PGTransition<L, A> transition : pg.getTransitions()) {
				if (state_to_explore.first.contains(transition.getFrom())
						&& ConditionDef.evaluate(conditionDefs, state_to_explore.second, transition.getCondition())) {
					all_transitions_from_state.add(transition);
				}
			}
		}
		for (PGTransition transition : all_transitions_from_state) {
			if (!parserBasedInterleavingActDef.isOneSidedAction((String) transition.getAction())) {
				if (try_to_read_from_empty_queue(state_to_explore, transition)) {
					continue;
				}
				List<L> new_state_list = new LinkedList<>(state_to_explore.first);
				int index_of_old = new_state_list.indexOf(transition.getFrom());

				new_state_list.set(index_of_old, (L) transition.getTo());
				Map<String, Object> new_eval = ActionDef.effect(actions, state_to_explore.second,
						transition.getAction());

				Pair<List<L>, Map<String, Object>> newState = new Pair(new_state_list, state_to_explore.second);
				ts.addState(newState);
				states_to_explore.add(newState);
				// add label
				labelNew_TS_stateFromChannel(ts, newState, conditionDefs, conditions_string);
				// add transition
				ts.addTransition(new TSTransition(state_to_explore, (A) transition.getAction(), newState));
			}
			// scanning just the _C! and not the _C? to avoid duplicates
			else if (((String) transition.getAction()).contains("!")) {
				for (PGTransition transition_interleavead : all_transitions_from_state) {
					if (parserBasedInterleavingActDef.isOneSidedAction((String) transition_interleavead.getAction())
							&& isOppositeActionInSameChannel((String) transition.getAction(),
									(String) transition_interleavead.getAction())) {
						List<L> new_state_name = channel_create_new_state_name(state_to_explore.first, transition,
								transition_interleavead);
						String interleaved_action = build_channel_interleave_action((String) transition.getAction(),
								(String) transition_interleavead.getAction());
						Map<String, Object> new_eval = parserBasedInterleavingActDef.effect(state_to_explore.second,
								interleaved_action);
						Pair<List<L>, Map<String, Object>> new_state = new Pair(new_state_name, new_eval);
						ts.addState(new_state);
						states_to_explore.add(new_state);
						// add transition
						ts.addTransition(new TSTransition(state_to_explore, interleaved_action, new_state));
						// add label
						labelNew_TS_stateFromChannel(ts, state_to_explore, conditionDefs, conditions_string);
					}
				}
			}
		}
		if (states_to_explore.size() > 0) {
			channel_state_and_transition_exploration(states_to_explore, ts, pgs, actions, conditionDefs,
					conditions_string);
		}
	}

	/**
	 * Construct a program graph from nanopromela code.
	 *
	 * @param filename The nanopromela code.
	 * @return A program graph for the given code.
	 * @throws Exception If the code is invalid.
	 */
	public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
		NanoPromelaParser.StmtContext stmt = NanoPromelaFileReader.pareseNanoPromelaFile(filename);
		ProgramGraph<String, String> pgGraph = createProgramGraph();
		List<PGTransition<String, String>> transitions = generatePGTransitions(stmt, false);
		pgGraph.setInitial(stmt.getText().toString(), true);
		for (PGTransition<String, String> transition : transitions) {
			if (!transition.getFrom().equals(TRUE_COND))
				pgGraph.addTransition(transition);
			else
				pgGraph.addTransition(transition);
		}
		return pgGraph;
	}

	/**
	 * Construct a program graph from nanopromela code.
	 *
	 * @param nanopromela The nanopromela code.
	 * @return A program graph for the given code.
	 * @throws Exception If the code is invalid.
	 */
	public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
		NanoPromelaParser.StmtContext stmt = NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);
		ProgramGraph<String, String> pgGraph = createProgramGraph();
		List<PGTransition<String, String>> transitions = generatePGTransitions(stmt, false);
		pgGraph.setInitial(stmt.getText().toString(), true);
		for (PGTransition<String, String> transition : transitions) {
			if (!transition.getFrom().equals(TRUE_COND))
				pgGraph.addTransition(transition);
			else
				pgGraph.addTransition(transition);
		}
		return pgGraph;
	}

	/**
	 * Construct a program graph from nanopromela code.
	 *
	 * @param inputStream The nanopromela code.
	 * @return A program graph for the given code.
	 * @throws Exception If the code is invalid.
	 */
	public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
		NanoPromelaParser.StmtContext stmt = NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
		ProgramGraph<String, String> pgGraph = createProgramGraph();
		List<PGTransition<String, String>> transitions = generatePGTransitions(stmt, false);
		pgGraph.setInitial(stmt.getText().toString(), true);
		for (PGTransition<String, String> transition : transitions) {
			if (!transition.getFrom().equals(TRUE_COND))
				pgGraph.addTransition(transition);
			else
				pgGraph.addTransition(transition);
		}
		return pgGraph;
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

		Set<TSTransition> unreachable_transitions = new HashSet<>();
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
		Set<Pair<S1, S2>> reaches = reach(interleave_transition_system);

		for (TSTransition trans : interleave_transition_system.getTransitions()) {
			if (!reaches.contains(trans.getFrom())) {
				unreachable_transitions.add(trans);
			}
		}
		for (TSTransition trans : unreachable_transitions) {
			interleave_transition_system.removeTransition(trans);
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

	private boolean isSimpleStatement(NanoPromelaParser.StmtContext sc) {
		return ((sc.assstmt() != null) || (sc.skipstmt() != null) || (sc.atomicstmt() != null)
				|| (sc.chanreadstmt() != null) || (sc.chanwritestmt() != null));
	}

	private final String TRUE_COND = "true";

	public List<PGTransition<String, String>> generatePGTransitionsFromSimpleStmnt(NanoPromelaParser.StmtContext sc,
			boolean cameFromIf, List<PGTransition<String, String>> allTransitions) {
		if (isSimpleStatement(sc) && !cameFromIf) {
			PGTransition<String, String> transition = new PGTransition<>(sc.getText().toString(), TRUE_COND,
					sc.getText().toString(), TRUE_COND);
			allTransitions.add(transition);
		} else if (isSimpleStatement(sc) && cameFromIf) {
			PGTransition<String, String> transition = new PGTransition<>(TRUE_COND, TRUE_COND, sc.getText().toString(),
					TRUE_COND);
			allTransitions.add(transition);
		}
		return allTransitions;
	}

	public void execSingleIfElseCommand(boolean ifCond, String type, String Succ, String fail,
			PGTransition<String, String> transition) {
		if (ifCond) {
			switch (type) {
			case "from": {
				transition.setFrom(Succ);
				break;
			}
			case "condition": {
				transition.setCondition(Succ);
				break;
			}
			case "to": {
				transition.setTo(Succ);
				break;
			}
			default:
				break;
			}
		} else {
			switch (type) {
			case "from": {
				transition.setFrom(fail);
				break;
			}
			case "condition": {
				transition.setCondition(fail);
				break;
			}
			case "to": {
				transition.setTo(fail);
				break;
			}
			default:
				break;
			}
		}
	}

	public void addingTransitionsByTypeOfStmt(List<PGTransition<String, String>> allTransitions, ParserRuleContext stmt,
			String type, boolean CameFromIf) {
		switch (type) {
		case "if": {
			NanoPromelaParser.IfstmtContext ifSStatement = (NanoPromelaParser.IfstmtContext) stmt;
			for (NanoPromelaParser.OptionContext oc : ifSStatement.option()) {
				List<PGTransition<String, String>> nestedTransitions = generatePGTransitions(oc.stmt(), true);
				for (PGTransition<String, String> transition : nestedTransitions) {
					boolean isStmtDirectlyAfterIf = !CameFromIf && transition.getFrom().equals(TRUE_COND);
					if (isStmtDirectlyAfterIf)
						transition.setFrom(ifSStatement.getText().toString());
					boolean toPutIfCondBefore = transition.getFrom().equals(ifSStatement.getText().toString())
							|| transition.getFrom().equals(TRUE_COND);
					if (toPutIfCondBefore) {
						if (transition.getCondition().equals(TRUE_COND))
							transition.setCondition("(" + oc.boolexpr().getText().toString() + ")");
						else
							transition.setCondition("(" + oc.boolexpr().getText().toString() + ") && ("
									+ transition.getCondition() + ")");
					}
					allTransitions.add(transition);
				}
			}
			break;
		}
		case "do": {
			NanoPromelaParser.DostmtContext doStatement = (NanoPromelaParser.DostmtContext) stmt;
			String loopTag = doStatement.getText().toString();
			PGTransition<String, String> condcondIfExit = new PGTransition<>(TRUE_COND, TRUE_COND, TRUE_COND,
					TRUE_COND);
			PGTransition<String, String> condExit = new PGTransition<>(TRUE_COND, TRUE_COND, TRUE_COND, TRUE_COND);
			for (NanoPromelaParser.OptionContext oc : doStatement.option()) {
				List<PGTransition<String, String>> nestedTransitions = generatePGTransitions(oc.stmt(), true);
				String cond = oc.boolexpr().getText().toString();
				for (PGTransition<String, String> transition : nestedTransitions) {
					String transFrom = transition.getFrom();
					if (CameFromIf)
						if (!transition.getFrom().equals(TRUE_COND))
							transition.setFrom(transFrom + ";" + loopTag);
						else
							execSingleIfElseCommand(transition.getFrom().equals(TRUE_COND), "from", loopTag,
									transFrom + ";" + loopTag, transition);

					if (transition.getFrom().equals(loopTag) || transition.getFrom().equals(TRUE_COND)) {
						String transCondition = transition.getCondition();
						if (transCondition.equals(TRUE_COND))
							transition.setCondition("(" + cond + ")");
						else
							transition.setCondition("(" + cond + ") && (" + transCondition + ")");
					}
					execSingleIfElseCommand(transition.getTo().equals(TRUE_COND), "to", loopTag,
							transition.getTo() + ";" + loopTag, transition);
				}
				execSingleIfElseCommand(condcondIfExit.getCondition().equals(TRUE_COND), "condition", "(" + cond + ")",
						condcondIfExit.getCondition() + "||(" + cond + ")", condcondIfExit);
				allTransitions.addAll(nestedTransitions);
				for (PGTransition<String, String> nesTransition : nestedTransitions) {
					if (nesTransition.getFrom().equals(TRUE_COND)) {
						PGTransition<String, String> newTransition = new PGTransition<>(loopTag,
								nesTransition.getCondition(), nesTransition.getAction(), nesTransition.getTo());
						allTransitions.add(newTransition);

					}
				}
			}
			condcondIfExit.setCondition("!(" + condcondIfExit.getCondition() + ")");
			if (CameFromIf)
				allTransitions.add(condcondIfExit);
			condExit.setFrom(loopTag);
			condExit.setCondition(condcondIfExit.getCondition());
			allTransitions.add(condExit);
			break;
		}
		default:
			break;
		}
	}

	public List<PGTransition<String, String>> generatePGTransitionsFromIfStmnt(NanoPromelaParser.StmtContext sc,
			boolean CameFromIf, List<PGTransition<String, String>> allTransitions) {
		NanoPromelaParser.IfstmtContext ifSStatement;
		ifSStatement = sc.ifstmt();
		if (ifSStatement != null)
			addingTransitionsByTypeOfStmt(allTransitions, ifSStatement, "if", CameFromIf);
		return allTransitions;
	}

	public List<PGTransition<String, String>> generatePGTransitionsFromDoStmnt(NanoPromelaParser.StmtContext sc,
			boolean CameFromIf, List<PGTransition<String, String>> allTransitions) {
		NanoPromelaParser.DostmtContext doStatement;
		doStatement = sc.dostmt();
		if (doStatement != null)
			addingTransitionsByTypeOfStmt(allTransitions, doStatement, "if", CameFromIf);
		return allTransitions;
	}

	public List<PGTransition<String, String>> generatePGTransitionsFromCompoundStmnt(NanoPromelaParser.StmtContext sc,
			boolean CameFromIf, List<PGTransition<String, String>> allTransitions) {
		List<NanoPromelaParser.StmtContext> stmts;
		stmts = sc.stmt();
		if (stmts != null) {
			String nextStmt = stmts.get(1).getText().toString();
			List<PGTransition<String, String>> nestedTransitions = generatePGTransitions(stmts.get(0), CameFromIf);
			for (PGTransition<String, String> transition : nestedTransitions) {
				if (CameFromIf)
					if (!transition.getFrom().equals(TRUE_COND))
						transition.setFrom(transition.getFrom() + ";" + nextStmt);
					else
						transition.setFrom(transition.getFrom() + ";" + nextStmt);
				execSingleIfElseCommand(transition.getTo().equals(TRUE_COND), "to", nextStmt,
						transition.getTo() + ";" + nextStmt, transition);
			}
			allTransitions.addAll(nestedTransitions);
			nestedTransitions = generatePGTransitions(stmts.get(1), false);
			allTransitions.addAll(nestedTransitions);
		}
		return allTransitions;
	}

	public List<PGTransition<String, String>> generatePGTransitions(NanoPromelaParser.StmtContext sc,
			boolean cameFromIf) {
		List<PGTransition<String, String>> totalTransitions = new LinkedList<>();

		// Mabye We are in a simple statement; base case
		if ((!generatePGTransitionsFromSimpleStmnt(sc, cameFromIf, totalTransitions).isEmpty())
				|| (!generatePGTransitionsFromIfStmnt(sc, cameFromIf, totalTransitions).isEmpty())
				|| (!generatePGTransitionsFromDoStmnt(sc, cameFromIf, totalTransitions).isEmpty())
				|| (!generatePGTransitionsFromCompoundStmnt(sc, cameFromIf, totalTransitions).isEmpty()))
			return totalTransitions;
		return totalTransitions; // Will be empty
	}

	public <L, A> void labelNew_TS_stateFromChannel(TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts,
			Pair<List<L>, Map<String, Object>> state, Set<ConditionDef> conditionDefs, Set<String> conditions) {
		for (L state_name : state.first) {
			ts.addToLabel(state, (String) state_name);

		}
		for (String condition : conditions) {
			if (ConditionDef.evaluate(conditionDefs, state.second, condition)) {
				ts.addToLabel(state, condition);
			}
		}
	}

	public boolean isOppositeActionInSameChannel(String first_action, String second_action) {
		if (first_action.contains("?") && second_action.contains("!")) {
			String chanName1 = first_action.split("\\?")[0];
			String chanName2 = second_action.split("\\!")[0];
			return chanName1.equals(chanName2);
		}
		if (first_action.contains("!") && second_action.contains("?")) {
			String chanName1 = first_action.split("\\!")[0];
			String chanName2 = second_action.split("\\?")[0];
			return chanName1.equals(chanName2);
		}
		return false;
	}

	public <L> boolean try_to_read_from_empty_queue(Pair<List<L>, Map<String, Object>> state, PGTransition transition) {
		String action = (String) transition.getAction();
		if (!action.contains("?")) {
			return false;
		}
		String channelName = action.split("\\?")[0];
		return ((Vector) state.second.get(channelName)).size() <= 0;
	}

	public <L> List<L> channel_create_new_state_name(List<L> old_name, PGTransition first_trans,
			PGTransition second_trans) {
		List<L> new_state_name = new LinkedList<>(old_name);

		int index_of_old_1 = new_state_name.indexOf(first_trans.getFrom());
		int index_of_old_2 = new_state_name.indexOf(second_trans.getFrom());

		new_state_name.set(index_of_old_1, (L) first_trans.getTo());
		new_state_name.set(index_of_old_2, (L) second_trans.getTo());
		return new_state_name;
	}

	public String build_channel_interleave_action(String first_action, String second_action) {
		if (first_action.contains("!")) {
			return first_action + '|' + second_action;
		} else {
			return second_action + '|' + first_action;
		}
	}

//	public String build_channel_interleave_condition(String first_cond, String second_cond) {
//        String cond1 = first_cond.equals("") ? "true" : "(" + first_cond + ")";
//        String cond2 = second_cond.equals("") ? "true" : "(" + second_cond + ")";
//        String condition = cond1 + "&&" + cond2;
//        return condition;
//	}

}
