package il.ac.bgu.cs.formalmethodsintro.base;

import java.io.InputStream;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Vector;
import java.util.*;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.fairness.FairnessCondition;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.And;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.Next;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.Not;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.TRUE;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.Until;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.AP;
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
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationSucceeded;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationFailed;
import org.antlr.v4.runtime.ParserRuleContext;

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
     * given p and ־± there exists only a single tuple (p,־±,q) in ג†’. Note that this
     * must be true even for non-reachable states.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @return {@code true} iff the action is deterministic.
     */
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        if (ts.getInitialStates().size() > 1) {
            return false;
        }
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
     * {@code c}, in the context of {@code ts}.
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
     * when action {@code a} is selected.
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
     * {@code c}, when action {@code a} is selected.
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
     * {@code c}, in the context of {@code ts}.
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
     * {@code s}, and the last action was {@code a}.
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
     * state in {@code c}, and the last action was {@code a}.
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

        // Set<Pair<S1, S2>> reaches = reach(interleave_transition_system);
        // Set<Pair<S1, S2>> unreachable = new HashSet<>();
        //
        // for (Pair<S1, S2> state : interleave_transition_system.getStates()) {
        // if (!reaches.contains(state)) {
        // unreachable.add(state);
        // }
        // }
        // for (Pair<S1, S2> state : unreachable) {
        // interleave_transition_system.removeState(state);
        // }

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
        for (List<String> initialOfP1 : pg1.getInitalizations()) {
            for (List<String> initialOfP2 : pg2.getInitalizations()) {
                List<String> newInitialization = new ArrayList<>(initialOfP1);
                newInitialization.addAll(initialOfP2);
                interleavedPG.addInitalization(newInitialization);
            }
        }
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
            if ((setToIterate.size() - binaryNum.length()) > 0) {
                char[] charArray = new char[setToIterate.size() - binaryNum.length()];
                Arrays.fill(charArray, '0');
                binaryNum = new String(charArray) + binaryNum;
            }
            List<String> inputs = new ArrayList<>();
            for (String input : setToIterate) {
                inputs.add(input);
            }
            for (int j = 0; j < binaryNum.length(); j++) {
                inputsMap.put(inputs.get(j), !(binaryNum.charAt(j) == '0'));
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
            if (pg_transition.getAction().equals("")) {
                continue;
            }
            ts.addAction((A) pg_transition.getAction());
        }

        // Creating list of all the conditions
        Set<String> conditions = new HashSet<String>();
        for (PGTransition transition : pg.getTransitions()) {
            conditions.add(transition.getCondition());
        }

        // Add propositions and Labeling
        for (Pair<L, Map<String, Object>> state : ts.getStates()) {
            labelNew_TS_stateFromGraph(ts, state, conditionDefs);
        }

        // Create the list state to explore
        List<Pair<L, Map<String, Object>>> states_to_explore = new LinkedList<>(ts.getInitialStates());

        // Create transitions
        state_and_transition_exploration(states_to_explore, 0, ts, pg, actionDefs, conditionDefs, conditions);

        return ts;
    }

    public <L, A> void state_and_transition_exploration(List<Pair<L, Map<String, Object>>> states_to_explore, int index,
                                                        TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts, ProgramGraph<L, A> pg,
                                                        Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs, Set<String> conditions) {

        Pair<L, Map<String, Object>> state_to_explore = states_to_explore.get(index);
        for (PGTransition transition : pg.getTransitions()) {
            if (transition.getFrom().equals(state_to_explore.first)
                    && ConditionDef.evaluate(conditionDefs, state_to_explore.second, transition.getCondition())) {
                Map<String, Object> newEval = ActionDef.effect(actionDefs, state_to_explore.second,
                        transition.getAction());
                Pair<L, Map<String, Object>> newState = new Pair(transition.getTo(), newEval);
                ts.addTransition(new TSTransition(state_to_explore, (A) transition.getAction(), newState));
                ts.addState(newState);
                labelNew_TS_stateFromGraph(ts, newState, conditionDefs);
                if (!states_to_explore.contains(newState)) {
                    states_to_explore.add(newState);
                }
            }
        }

        if (index + 1 < states_to_explore.size()) {
            state_and_transition_exploration(states_to_explore, index + 1, ts, pg, actionDefs, conditionDefs,
                    conditions);
        }
    }

    public <L> Set<List<L>> cartesianProduct(List<Set<L>> array_of_sets) {
        if (array_of_sets.size() < 2)
            throw new IllegalArgumentException(
                    "Can't have a product of fewer than two sets (got " + array_of_sets.size() + ")");

        return _cartesianProduct(0, array_of_sets);
    }

    private <L> Set<List<L>> _cartesianProduct(int index, List<Set<L>> array_of_sets) {
        Set<List<L>> ret = new HashSet<List<L>>();
        if (index == array_of_sets.size()) {
            ret.add(new LinkedList<L>());
        } else {
            for (L obj : array_of_sets.get(index)) {
                for (List<L> list : _cartesianProduct(index + 1, array_of_sets)) {
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
        List<Set<L>> array_of_sets = new ArrayList<Set<L>>();

        for (int i = number_of_pgs - 1; i > -1; i--) {
            array_of_sets.add(pgs.get(i).getInitialLocations());
        }

        Set<List<L>> cartesian_initial_states = cartesianProduct(array_of_sets);

        // The initializetions
        Set<List<String>> initials = createListOfInitials(cs.getProgramGraphs());

        // initial states
        for (List<L> loc : cartesian_initial_states) {
            if (initials.size() > 0) {
                for (List<String> init : initials) {
                    Map<String, Object> eval = new HashMap<>();
                    for (String s : init) {
                        eval = ActionDef.effect(actions, eval, s);
                    }
                    Pair<List<L>, Map<String, Object>> state = new Pair<>(loc, eval);
                    ts.addInitialState(state);
                }
            } else {
                Map<String, Object> eval = new HashMap<>();
                Pair<List<L>, Map<String, Object>> state = new Pair<>(loc, eval);
                ts.addInitialState(state);
            }
        }

        // create labels of the initial states
        for (Pair<List<L>, Map<String, Object>> initial_state : ts.getInitialStates()) {
            labelNew_TS_stateFromChannel(ts, initial_state, conditions);
        }
        // Create the list state to explore
        List<Pair<List<L>, Map<String, Object>>> states_to_explore = new LinkedList<>(ts.getInitialStates());

        // Create transitions
        channel_state_and_transition_exploration(states_to_explore, 0, ts, pgs, actions, conditions);
        return ts;

    }

    public <L, A> void channel_state_and_transition_exploration(
            List<Pair<List<L>, Map<String, Object>>> states_to_explore, int index,
            TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts, List<ProgramGraph<L, A>> pgs,
            Set<ActionDef> actions, Set<ConditionDef> conditionDefs) {

        Pair<List<L>, Map<String, Object>> state_to_explore = states_to_explore.get(index);
        ParserBasedInterleavingActDef parserBasedInterleavingActDef = new ParserBasedInterleavingActDef();
        Set<PGTransition<L, A>> all_transitions_from_state = new HashSet<>();

        // for (PGTransition transition : all_transitions_from_state) {
        for (int i = 0; i < pgs.size(); i++) {
            for (PGTransition<L, A> transition : pgs.get(i).getTransitions()) {
                if (state_to_explore.first.get(i).equals(transition.getFrom())
                        && ConditionDef.evaluate(conditionDefs, state_to_explore.second, transition.getCondition())) {
                    if (!parserBasedInterleavingActDef.isOneSidedAction((String) transition.getAction())) {
                        if (try_to_read_from_empty_queue(state_to_explore, transition)) {
                            continue;
                        }
                        List<L> new_state_list = new LinkedList<>(state_to_explore.first);

                        new_state_list.set(i, (L) transition.getTo());
                        Map<String, Object> new_eval = ActionDef.effect(actions, state_to_explore.second,
                                transition.getAction());

                        Pair<List<L>, Map<String, Object>> newState = new Pair(new_state_list, new_eval);
                        ts.addState(newState);
                        // add label
                        labelNew_TS_stateFromChannel(ts, newState, conditionDefs);
                        // add transition
                        ts.addTransition(new TSTransition(state_to_explore, (A) transition.getAction(), newState));
                        if (!states_to_explore.contains(newState)) {
                            states_to_explore.add(newState);
                        }
                    } else /* if (((String) transition.getAction()).contains("!")) */ {
                        for (int j = 0; j < pgs.size(); j++) {
                            for (PGTransition<L, A> transition_interleavead : pgs.get(j).getTransitions()) {
                                if (state_to_explore.first.get(j).equals(transition_interleavead.getFrom())
                                        && parserBasedInterleavingActDef
                                        .isOneSidedAction((String) transition_interleavead.getAction())
                                        && isOppositeActionInSameChannel((String) transition.getAction(),
                                        (String) transition_interleavead.getAction())) {
                                    List<L> new_state_name = channel_create_new_state_name(state_to_explore.first,
                                            transition, transition_interleavead);
                                    String interleaved_action = build_channel_interleave_action(
                                            (String) transition.getAction(),
                                            (String) transition_interleavead.getAction());
                                    Map<String, Object> new_eval = parserBasedInterleavingActDef
                                            .effect(state_to_explore.second, interleaved_action);
                                    Pair<List<L>, Map<String, Object>> new_state = new Pair(new_state_name, new_eval);
                                    ts.addState(new_state);
                                    // add transition
                                    ts.addTransition(new TSTransition(state_to_explore, interleaved_action, new_state));
                                    // add label
                                    labelNew_TS_stateFromChannel(ts, state_to_explore, conditionDefs);
                                    if (!states_to_explore.contains(new_state)) {
                                        states_to_explore.add(new_state);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        if (index + 1 < states_to_explore.size()) {
            channel_state_and_transition_exploration(states_to_explore, index + 1, ts, pgs, actions, conditionDefs);
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
        TransitionSystem<Pair<Sts, Saut>, A, Saut> product_ts = new TransitionSystem<Pair<Sts, Saut>, A, Saut>();

        // Actions
        for (A act : ts.getActions()) {
            product_ts.addAction(act);
        }

        // Initial states
        for (Sts s : ts.getInitialStates()) {
            for (Saut q_initial : aut.getInitialStates()) {
                // What if there is no proposition?
                /*
                 * if(ts.getLabel(s).isEmpty()) { for(Saut q_dest:
                 * aut.getTransitions().get(q_initial).get(prop)) {
                 * product_ts.addInitialState(new Pair(s,q_dest)); } }
                 */
                for (Saut q_dest : aut.getTransitions().get(q_initial).get(ts.getLabel(s)/* prop */)) {
                    Pair<Sts, Saut> init_state = new Pair(s, q_dest);
                    product_ts.addInitialState(init_state);
                    product_ts.addToLabel(init_state, q_dest);
                }
            }

        }

        List<Pair<Sts, Saut>> states_to_explore = new LinkedList(product_ts.getInitialStates());
        // Transitions and states
        explore_transition_for_product_ts(product_ts, ts, aut, states_to_explore, 0);
        return product_ts;
    }

    private <Sts, Saut, A, P> void explore_transition_for_product_ts(
            TransitionSystem<Pair<Sts, Saut>, A, Saut> product_ts, TransitionSystem<Sts, A, P> ts,
            Automaton<Saut, P> aut, List<Pair<Sts, Saut>> states_to_explore, int index) {

        Pair<Sts, Saut> state_to_explore = states_to_explore.get(index);
        for (TSTransition<Sts, A> trans : ts.getTransitions()) {
            if (trans.getFrom().equals(state_to_explore.first)) {
                Sts state_dest = trans.getTo();
                if (aut.getTransitions().get(state_to_explore.second).get(ts.getLabel(state_dest)) != null) {
                    for (Saut q_dest : aut.getTransitions().get(state_to_explore.second).get(ts.getLabel(state_dest))) {
                        Pair<Sts, Saut> new_state = new Pair(state_dest, q_dest);
                        if (!states_to_explore.contains(new_state)) {
                            states_to_explore.add(new_state);
                        }
                        // We adding the state in the addTransition function
                        product_ts.addTransition(new TSTransition(state_to_explore, trans.getAction(), new_state));
                        product_ts.addToLabel(new_state, new_state.second);
                    }
                }
            }
        }
        if (index + 1 < states_to_explore.size()) {
            explore_transition_for_product_ts(product_ts, ts, aut, states_to_explore, index + 1);
        }
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
     * @param aut    A Bֳ¼chi automaton for the words that do not satisfy the
     *               property.
     * @return A VerificationSucceeded object or a VerificationFailed object with a
     * counterexample.
     */

    private <S, A, P, Saut> VerificationFailed<S> buildFailPathFromScratch(List<Pair<S, Saut>> cycle, List<Pair<S, Saut>> prefix) {
        VerificationFailed<S> result = new VerificationFailed<>();
        List<S> cycleStatesOfTs = new LinkedList<>();
        for (Pair<S, Saut> p : cycle)
            cycleStatesOfTs.add(p.first);
        result.setCycle(cycleStatesOfTs);

        if (!prefix.isEmpty()) prefix.remove(prefix.size() - 1);

        List<S> prefixStatesOfTs = new LinkedList<>();
        for (Pair<S, Saut> p : prefix)
            prefixStatesOfTs.add(p.first);
        result.setPrefix(prefixStatesOfTs);
        return result;
    }

    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts,
                                                                              Automaton<Saut, P> aut) {
        List<Pair<S, Saut>> prefix = new LinkedList<>();
        List<Pair<S, Saut>> cycle = new LinkedList<>();
        if (runDFS(product(ts, aut), aut, cycle, prefix)) return new VerificationSucceeded<>();
        // There is a fail path, We will build one
        return buildFailPathFromScratch(cycle, prefix);
    }

    private <S, A, Saut, P> boolean runDFS(TransitionSystem<Pair<S, Saut>, A, Saut> productTSA, Automaton<Saut, P> aut, List<Pair<S, Saut>> cycle, List<Pair<S, Saut>> prefix) {
        Set<Pair<S, Saut>> totalStates = new HashSet<>();
        Set<Pair<S, Saut>> satisfiedStates = new HashSet<>();
        Stack<Pair<S, Saut>> statesToExpose = new Stack<>();
        for (Pair<S, Saut> state : productTSA.getInitialStates()) {
            if (!totalStates.contains(state)) {
                // Starting exposing states in paths
                statesToExpose.push(state);
                totalStates.add(state);
                boolean itsFirst = true;
                while (!statesToExpose.isEmpty() || itsFirst) {
                    itsFirst = false;
                    Pair<S, Saut> tmp = statesToExpose.peek();
                    Set<Pair<S, Saut>> postTempState = post(productTSA, tmp);
                    if (totalStates.containsAll(postTempState)) {
                        statesToExpose.pop();
                        if (stateIsSatisfying(tmp, aut, productTSA)) satisfiedStates.add(tmp);
                    } else {
                        Pair<S, Saut> tempTempState = substract(postTempState, totalStates).get(0);
                        statesToExpose.push(tempTempState);
                        totalStates.add(tempTempState);
                    }
                }
            }
        }

        for (Pair<S, Saut> state : satisfiedStates) {
            if (runCycleTest(state, productTSA, cycle)) {
                if (prefix.isEmpty()) {
                    boolean hasPref = false;
                    Stack<Pair<S, Saut>> stack = new Stack<>();
                    for (Pair<S, Saut> initState : productTSA.getInitialStates()) {
                        if (isStateFound(productTSA, state, initState, stack)) {
                            hasPref = true;
                            prefix.addAll(new LinkedList<>(stack));
                            break;
                        }
                    }
                    if (!hasPref) prefix.addAll(new LinkedList<>());
                }
                return false;
            }
        }
        return true;
    }

    private <S, A, P, Saut> boolean runCycleTest(Pair<S, Saut> state, TransitionSystem<Pair<S, Saut>, A, Saut> ts, List<Pair<S, Saut>> cycle) {
        Set<Pair<S, Saut>> checked = new HashSet<>();
        Stack<Pair<S, Saut>> toExpose = new Stack<>();
        boolean cycleFound = false;
        toExpose.push(state);
        checked.add(state);
        do {
            Pair<S, Saut> tmp = toExpose.peek();
            Set<Pair<S, Saut>> postTempState = post(ts, tmp);
            if (postTempState.contains(state)) {
                cycleFound = true;
                if (cycle.isEmpty()) cycle.addAll(toExpose);
            } else {
                if (!substract(postTempState, checked).isEmpty()) {
                    Pair<S, Saut> tempTempState = substract(postTempState, checked).get(0);
                    toExpose.push(tempTempState);
                    checked.add(tempTempState);
                } else toExpose.pop();
            }
        } while (!toExpose.isEmpty() && !cycleFound);
        return cycleFound;
    }

    private <A, S, Saut> boolean isStateFound(TransitionSystem<Pair<S, Saut>, A, Saut> productTSA,
                                              Pair<S, Saut> stateToFind, Pair<S, Saut> initState, Stack<Pair<S, Saut>> stack) {
        stack.push(initState);
        Set<Pair<S, Saut>> statesToExplore = new HashSet<>();
        statesToExplore.add(initState);
        boolean itsFirst = true;
        while (!stack.isEmpty() || itsFirst) {
            itsFirst = false;
            Pair<S, Saut> tempState = stack.peek();
            if (tempState.equals(stateToFind)) return true;
            if (statesToExplore.containsAll(post(productTSA, tempState))) stack.pop();
            else {
                Set<Pair<S, Saut>> postTempState = post(productTSA, tempState);
                postTempState.removeAll(statesToExplore);
                Pair<S, Saut> tempTempState = new LinkedList<>(postTempState).get(0);
                stack.push(tempTempState);
                statesToExplore.add(tempTempState);
            }
        }
        return false;
    }

    private <Saut, P, A, S> boolean stateIsSatisfying(Pair<S, Saut> state, Automaton<Saut, P> aut, TransitionSystem<Pair<S, Saut>, A, Saut> productTSA) {
        Set<Saut> acceptingStates = aut.getAcceptingStates();
        for (Saut prop : productTSA.getLabel(state)) {
            for (Saut st : acceptingStates)
                if (st.equals(prop))
                    return true;
        }
        return false;
    }

    private <S> List<S> substract(Set<S> toSubtractFrom, Set<S> toSubstract) {
        List<S> res = new LinkedList<>(toSubtractFrom);
        res.removeAll(toSubstract);
        return res;
    }

    /**
     * A translation of a Generalized Bֳ¼chi Automaton (GNBA) to a Nondeterministic
     * Bֳ¼chi Automaton (NBA).
     *
     * @param <L>    Type of resultant automaton transition alphabet
     * @param mulAut An automaton with a set of accepting states (colors).
     * @return An equivalent automaton with a single set of accepting states.
     */
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        Automaton<Pair<?, Integer>, L> aut = new Automaton();
        int k = mulAut.getColors().size();
        boolean next_aut = false;

        // Initial states
        for (Object init_state : mulAut.getInitialStates()) {
            aut.setInitial(new Pair(init_state, 0));
        }

        // Accepting states
        for (Object accepeting_state : mulAut.getAcceptingStates(0)) {
            aut.setAccepting(new Pair(accepeting_state, 0));
        }

        // Transitions and states
        for (Entry<?, ?> entry : mulAut.getTransitions().entrySet()) {
            Object state = entry.getKey();
            Map<Set<L>, Set<Object>> inside_map = (Map<Set<L>, Set<Object>>) entry.getValue();
            for (int i = 0; i < k; i++) {
                next_aut = false;
                // if it's accepting state in Fi
                if (mulAut.getAcceptingStates(i).contains(state)) {
                    next_aut = true;
                }
                for (Entry<Set<L>, Set<Object>> inside_entry : inside_map.entrySet()) {
                    for (Object o : inside_entry.getValue()) {
                        if (next_aut) {
                            aut.addTransition(new Pair(state, i), inside_entry.getKey(), new Pair(o, ((i + 1) % k)));
                        } else {
                            aut.addTransition(new Pair(state, i), inside_entry.getKey(), new Pair(o, i));
                        }
                    }
                }
            }
        }

        return aut;
    }

    /**
     * Translation of Linear Temporal Logic (LTL) formula to a Nondeterministic
     * Bֳ¼chi Automaton (NBA).
     *
     * @param <L> Type of resultant automaton transition alphabet
     * @param ltl The LTL formula represented as a parse-tree.
     * @return An automaton A such that L_\omega(A)=Words(ltl)
     */
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        return GNBA2NBA(LTL2GNBA(ltl));
    }

    // Creating pairs of each ltl-statement and its negation
    private static <L> void createPairs(Set<Pair<LTL<L>, LTL<L>>> pairs, Set<LTL<L>> subs) {
        subs.forEach(ltl2 -> {
            if (ltl2 instanceof TRUE) pairs.add(new Pair<LTL<L>, LTL<L>>(ltl2, ltl2));
            else {
                if (!subs.contains(LTL.not(ltl2))) {
                    if (ltl2 instanceof Not) pairs.add(new Pair<LTL<L>, LTL<L>>(ltl2, ((Not<L>) ltl2).getInner()));
                    else pairs.add(new Pair<LTL<L>, LTL<L>>(ltl2, LTL.not(ltl2)));
                }
            }
        });
    }

    // Creating color for each until-ltl
    private static <L> void mapColors(Set<LTL<L>> subs, Map<LTL<L>, Integer> colorsMap, int nextColor) {
        for (LTL<L> ltl2 : subs) {
            if (ltl2 instanceof Until) {
                colorsMap.put(ltl2, nextColor);
                nextColor++;
            }
        }
    }

    private static <L> MultiColorAutomaton<?, L> LTL2GNBA(LTL<L> ltl) {
        MultiColorAutomaton<Set<LTL<L>>, L> gnbaAuto = new MultiColorAutomaton<>();
        Set<LTL<L>> subs = subLTL(ltl);
        Map<LTL<L>, Integer> colorsMap = new HashMap<LTL<L>, Integer>();
        int firstColor = 0;

        // Determine how many colors we need
        mapColors(subs, colorsMap, firstColor);
        // Making pairs of subs, adding the negation for each ltl(if needed) and ignoring duplications(if needed).
        Set<Pair<LTL<L>, LTL<L>>> pairs = new HashSet<>();
        createPairs(pairs, subs);

        Set<LTL<L>> initial = new HashSet<>();
        initial.add(ltl);
        Set<Set<LTL<L>>> initialStates = createConsistenciesBStates(initial, pairs);

        for (Set<LTL<L>> s : initialStates)
            gnbaAuto.setInitial(s);

        Set<Set<LTL<L>>> currStates = new HashSet<>(initialStates);
        Set<Set<LTL<L>>> newStates = new HashSet<>();
        Set<Set<LTL<L>>> allStates = new HashSet<>(initialStates);
        boolean itsFirst = true;

        while (currStates.size() > 0 || itsFirst) {
            itsFirst = false;
            for (Set<LTL<L>> cur_s : currStates) {
                Set<Set<LTL<L>>> nextStates = LTLNextStates(cur_s, pairs);
                Set<L> symbol = new HashSet<L>();
                for (LTL<L> ltl2 : cur_s) {
                    if (ltl2 instanceof AP) symbol.add(((AP<L>) ltl2).getName());
                }
                nextStates.forEach(s -> gnbaAuto.addTransition(cur_s, symbol, s));
                nextStates.removeAll(allStates);
                newStates.addAll(nextStates);
                allStates.addAll(nextStates);
                List<Integer> colors = new ArrayList<Integer>();
                for (LTL<L> ltl2 : cur_s) {
                    if (ltl2 instanceof Not) {
                        LTL<L> until = ((Not<L>) ltl2).getInner();
                        if (until instanceof Until) {
                            Integer color = colorsMap.get(until);
                            colors.add(color);
                        }
                    } else if (ltl2 instanceof Until) {
                        LTL<L> right = ((Until<L>) ltl2).getRight();
                        if (cur_s.contains(right)) {
                            Integer color = colorsMap.get(ltl2);
                            colors.add(color);
                        }
                    }
                }
                colors.forEach(color -> gnbaAuto.setAccepting(cur_s, color));
            }
            currStates = newStates;
            newStates = new HashSet<>();
        }

        if (colorsMap.isEmpty()) allStates.forEach(s -> gnbaAuto.setAccepting(s, 0));
        return gnbaAuto;
    }

    private static <L> void addSubOfAnd(Set<LTL<L>> sub, LTL<L> ltl) {
        And<L> and_ltl = (And<L>) ltl;
        LTL<L> ltl_left = and_ltl.getLeft();
        LTL<L> ltl_right = and_ltl.getRight();
        sub.addAll(subLTL(ltl_left));
        sub.addAll(subLTL(ltl_right));
    }

    private static <L> void addSubOfUntil(Set<LTL<L>> sub, LTL<L> ltl) {
        Until<L> until_ltl = (Until<L>) ltl;
        LTL<L> ltl_left = until_ltl.getLeft();
        LTL<L> ltl_right = until_ltl.getRight();
        sub.addAll(subLTL(ltl_left));
        sub.addAll(subLTL(ltl_right));
    }

    private static <L> void addSubOfNot(Set<LTL<L>> sub, LTL<L> ltl) {
        Not<L> not_ltl = (Not<L>) ltl;
        LTL<L> ltl_not = not_ltl.getInner();
        sub.addAll(subLTL(ltl_not));
    }

    private static <L> void addSubOfNext(Set<LTL<L>> sub, LTL<L> ltl) {
        Next<L> next_ltl = (Next<L>) ltl;
        LTL<L> ltl_1 = next_ltl.getInner();
        sub.addAll(subLTL(ltl_1));
    }

    private static <L> Set<LTL<L>> subLTL(LTL<L> ltl) {
        Set<LTL<L>> sub = new HashSet<>();
        sub.add(ltl);
        if (ltl instanceof And) addSubOfAnd(sub, ltl);
        if (ltl instanceof Until) addSubOfUntil(sub, ltl);
        if (ltl instanceof Not) addSubOfNot(sub, ltl);
        if (ltl instanceof Next) addSubOfNext(sub, ltl);
        return sub;
    }

    private static <L> void createOptionalStates(Set<Set<LTL<L>>> currStates, Set<Pair<LTL<L>, LTL<L>>> subs, Set<Set<LTL<L>>> newOptionalStates, Set<Set<LTL<L>>> optionalStates) {
        for (Set<LTL<L>> s : currStates) {
            boolean isMax = true;
            for (Pair<LTL<L>, LTL<L>> ltlPair : subs) {
                LTL<L> first = ltlPair.getFirst();
                LTL<L> second = ltlPair.getSecond();
                if ((!s.contains(first)) && (!s.contains(second))) {
                    isMax = false;
                    Set<LTL<L>> newState_1 = new HashSet<>(s);
                    Set<LTL<L>> newState_2 = new HashSet<>(s);
                    newState_1 = checkConsistencies(newState_1, first);
                    newState_2 = checkConsistencies(newState_2, second);
                    if (newState_1 != null) newOptionalStates.add(newState_1);
                    if (newState_2 != null) newOptionalStates.add(newState_2);
                    break;
                }
            }
            if (isMax) optionalStates.add(s);
        }
    }

    private static <L> Set<Set<LTL<L>>> createConsistenciesBStates(Set<LTL<L>> ltls, Set<Pair<LTL<L>, LTL<L>>> subs) {
        Set<Set<LTL<L>>> optionalStates = new HashSet<>();
        Set<Set<LTL<L>>> currStates = new HashSet<>();
        currStates.add(ltls);
        Set<Set<LTL<L>>> newOptionalStates = new HashSet<>();
        boolean itsFirst = true;

        while (currStates.size() > 0 || itsFirst) {
            itsFirst = false;
            createOptionalStates(currStates, subs, newOptionalStates, optionalStates);
            currStates = newOptionalStates;
            newOptionalStates = new HashSet<>();
        }
        return optionalStates;
    }

    private static <L> Set<Set<LTL<L>>> LTLNextStates(Set<LTL<L>> currState, Set<Pair<LTL<L>, LTL<L>>> subPairs) {
        Set<LTL<L>> nextState = new HashSet<LTL<L>>();
        for (LTL<L> ltl : currState) {
            if (ltl instanceof Next) nextState.add(((Next<L>) ltl).getInner());
            if (ltl instanceof Not) {
                if (((Not<L>) ltl).getInner() instanceof Next) {
                    Next<L> next = (Next<L>) ((Not<L>) ltl).getInner();
                    LTL<L> not_a = getNegateLtl(next.getInner());
                    nextState.add(not_a);
                }
            }
            if (ltl instanceof Until) {
                if (currState.contains(((Until<L>) ltl).getRight())) continue;
                else if (currState.contains(((Until<L>) ltl).getLeft())) nextState.add(ltl);
            }
            if (ltl instanceof Not) {
                Not<L> not = ((Not<L>) ltl);
                if (not.getInner() instanceof Until) {
                    LTL<L> left = ((Until<L>) not.getInner()).getLeft();
                    LTL<L> not_left = getNegateLtl(left);
                    if (!currState.contains(not_left)) nextState.add(getNegateLtl(not.getInner()));
                }
            }
        }
        return createConsistenciesBStates(nextState, subPairs);
    }

    // We check if the added ltl brakes the consistency
    private static <L> Set<LTL<L>> checkConsistencies(Set<LTL<L>> state, LTL<L> ltl) {
        state.add(ltl);
        // Check Logic
        for (LTL<L> ltlOfState : state) {
            if (ltlOfState instanceof And) {
                if (state.contains(getNegateLtl(((And<L>) ltlOfState).getLeft())) || state.contains(getNegateLtl(((And<L>) ltlOfState).getRight())))
                    return null;
            } else if (ltlOfState instanceof Not) {
                Not<L> notLtl = (Not<L>) ltlOfState;
                LTL<L> inner = notLtl.getInner();
                if (state.contains(inner)) return null;
                if (inner instanceof And) {
                    And<L> and = (And<L>) inner;
                    LTL<L> leftLtl = and.getLeft();
                    LTL<L> rightLtl = and.getRight();
                    if (state.contains(leftLtl) && state.contains(rightLtl)) return null;
                }
            }
        }

        // Check Locality
        for (LTL<L> ltlOfState : state) {
            if (ltlOfState instanceof Until) {
                Until<L> until = (Until<L>) ltlOfState;
                LTL<L> not_left = getNegateLtl(until.getLeft());
                LTL<L> not_right = getNegateLtl(until.getRight());
                if (state.contains(not_left) && state.contains(not_right)) return null;
            } else if (ltlOfState instanceof Not) {
                Not<L> not = (Not<L>) ltlOfState;
                LTL<L> inner = not.getInner();
                if (inner instanceof Until) {
                    Until<L> until = (Until<L>) inner;
                    LTL<L> right = until.getRight();
                    if (state.contains(right)) return null;
                }
            }
        }
        return state;
    }

    // Bringing the opposite of the given ltl
    private static <L> LTL<L> getNegateLtl(LTL<L> ltl) {
        if (ltl instanceof Not) return ((Not<L>) ltl).getInner();
        else return LTL.not(ltl);
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
                                                  Pair<L, Map<String, Object>> state, Set<ConditionDef> conditionDefs) {
        ts.addToLabel(state, state.first.toString());
        Map<String, Object> eval = state.getSecond();
        for (String var : eval.keySet()) {
            ts.addToLabel(state, var + " = " + eval.get(var));
        }
    }

    private boolean isSimpleStatement(NanoPromelaParser.StmtContext sc) {
        return ((sc.assstmt() != null) || (sc.skipstmt() != null) || (sc.atomicstmt() != null)
                || (sc.chanreadstmt() != null) || (sc.chanwritestmt() != null));
    }

    private final String TRUE_COND = "";

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
                        if (CameFromIf) {
                            if (!transition.getFrom().equals(TRUE_COND))
                                transition.setFrom(transFrom + ";" + loopTag);
                        } else
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
            addingTransitionsByTypeOfStmt(allTransitions, doStatement, "do", CameFromIf);
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
                if (CameFromIf) {
                    if (!transition.getFrom().equals(TRUE_COND))
                        transition.setFrom(transition.getFrom() + ";" + nextStmt);
                } else
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
                                                    Pair<List<L>, Map<String, Object>> state, Set<ConditionDef> conditionDefs) {
        for (L state_name : state.first) {
            ts.addToLabel(state, state_name.toString());

        }
        Map<String, Object> eval = state.getSecond();
        for (String var : eval.keySet()) {
            ts.addToLabel(state, var + " = " + eval.get(var));
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
        if (state.second.get(channelName) == null) {
            return true;
        }
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

        return first_action + '|' + second_action;
    }

    private <L, A> Set<List<String>> createListOfInitials(List<ProgramGraph<L, A>> pgs) {
        return createListOfInitials(pgs, 0, new HashSet<>());
    }

    private <L, A> Set<List<String>> createListOfInitials(List<ProgramGraph<L, A>> pgs, int pgsIndex,
                                                          Set<List<String>> set) {
        if (pgs.size() <= pgsIndex) {
            return set;
        }
        if (set.isEmpty()) {
            for (List<String> init : pgs.get(pgsIndex).getInitalizations()) {
                List<String> lst = new LinkedList<>();
                lst.addAll(init);
                set.add(lst);
            }
            return createListOfInitials(pgs, pgsIndex + 1, set);
        } else {
            Set<List<String>> newSet = new HashSet<>();
            if (pgs.get(pgsIndex).getInitalizations().size() < 1) {
                return set;
            }
            for (List<String> state : set) {
                for (List<String> init : pgs.get(pgsIndex).getInitalizations()) {
                    List<String> newState = new LinkedList<>(state);
                    newState.addAll(init);
                    newSet.add(newState);
                }
            }
            return createListOfInitials(pgs, pgsIndex + 1, newSet);
        }
    }

    /**
     * Verify that a system satisfies an LTL formula under fairness conditions.
     *
     * @param ts  Transition system
     * @param fc  Fairness condition
     * @param ltl An LTL formula
     * @param <S> Type of states in the transition system
     * @param <A> Type of actions in the transition system
     * @param <P> Type of atomic propositions in the transition system
     * @return a VerificationSucceeded object or a VerificationFailed object with a counterexample.
     */
    public <S, A, P> VerificationResult<Pair<S, A>> verifyFairLTLFormula(TransitionSystem<S, A, P> ts, FairnessCondition<A> fc, LTL<P> ltl) {
        TransitionSystem<Pair<S, A>, A, P> ts_tag = get_ts_tag(ts);
        LTL<P> modifiedLtl = createModifiedLtl(fc, ltl);
        return verifyAnOmegaRegularProperty(ts_tag, LTL2NBA(modifiedLtl));
    }


    private <S, A, P> TransitionSystem<Pair<S, A>, A, P> get_ts_tag(TransitionSystem<S, A, P> ts) {
        TransitionSystem<Pair<S, A>, A, P> new_ts = new TransitionSystem();
        // States
        for (S state : ts.getStates()) {
            for (A act : ts.getActions()) {
                Pair<S, A> new_state = new Pair(state, act);
                if (ts.getInitialStates().contains(state)) {
                    new_ts.addInitialState(new_state);
                } else {
                    new_ts.addState(new_state);
                }
                for (P prop : ts.getLabel(state)) {
//					if(prop=="") {
//						continue;
//					}
                    new_ts.addToLabel(new_state, prop);

                }
                new_ts.addToLabel(new_state, (P) ("t(" + act + ")"));
                for (TSTransition trans : ts.getTransitions()) {
                    if (trans.getFrom().equals(state)) {
                        new_ts.addToLabel(new_state, (P) ("e(" + trans.getAction() + ")"));
                    }
                }
            }
        }

        // Transitions
        for (TSTransition trans : ts.getTransitions()) {
            for (Pair<S, A> state : new_ts.getStates()) {
                if (trans.getFrom().equals(state.first)) {
                    TSTransition new_trans = new TSTransition(state, trans.getAction(),
                            new Pair(trans.getTo(), trans.getAction()));
                    new_ts.addTransition(new_trans);
                }
            }
        }

        return new_ts;
    }

    public <P, A> LTL<P> createModifiedLtl(FairnessCondition<A> fc, LTL<P> ltl) {
        Set<Set<A>> uncond = fc.getUnconditional();
        Set<Set<A>> strong = fc.getStrong();
        Set<Set<A>> weak = fc.getWeak();

        // UNCOND
        LTL<String> finalUncondActionGroup = new TRUE<String>();
        for (Set<A> setOfActions : uncond) {
            LTL<String> uncondLTL = new TRUE<String>();
            for (A action : setOfActions) {
                // De morgan -> a or b = !!(a or b) = !(!a and !b)
                uncondLTL = new Not<String>(new And<String>(new Not<String>(new AP<String>("t(" + (String)action + ")")), new Not<>(uncondLTL)));
            }
            LTL<String> newUncondActionGroup = createAlwaysEventuallyLTL(uncondLTL);
            finalUncondActionGroup = new And(newUncondActionGroup, finalUncondActionGroup);
        }

        // STRONG
        LTL<String> finalStrongActionGroup = new TRUE<String>();
        for (Set<A> setOfActions : strong) {
            LTL<String> strongEnabledLTL = new TRUE<String>();
            LTL<String> strongTriggeredLTL = new TRUE<String>();
            for (A action : setOfActions) {
                // De morgan -> a or b = !!(a or b) = !(!a and !b)
                strongEnabledLTL = new Not<String>(new And<String>(new Not<String>(new AP<String>("e(" + (String)action + ")")), new Not<>(strongEnabledLTL)));
            }
            for (A action : setOfActions) {
                // De morgan -> a or b = !!(a or b) = !(!a and !b)
                strongTriggeredLTL = new Not<String>(new And<String>(new Not<String>(new AP<String>("t(" + (String)action + ")")), new Not<>(strongTriggeredLTL)));
            }
            // If Then.. (a -> b) equals (!a or b =  !!(!a or b) = !(a and !b))
            LTL<String> newStrongActionGroup = new Not<String>(new And<String>(createAlwaysEventuallyLTL(strongEnabledLTL), new Not<String>(createAlwaysEventuallyLTL(strongTriggeredLTL))));
            finalStrongActionGroup = new And(newStrongActionGroup, finalStrongActionGroup);
        }

        // WEAK
        LTL<String> finalWeakActionGroup = new TRUE<String>();
        for (Set<A> setOfActions : weak) {
            LTL<String> weakEnabledLTL = new TRUE<String>();
            LTL<String> weakTriggeredLTL = new TRUE<String>();
            for (A action : setOfActions) {
                // De morgan -> a or b = !!(a or b) = !(!a and !b)
                weakEnabledLTL = new Not<String>(new And<String>(new Not<String>(new AP<String>("e(" + (String)action + ")")), new Not<>(weakEnabledLTL)));
            }
            for (A action : setOfActions) {
                // De morgan -> a or b = !!(a or b) = !(!a and !b)
                weakTriggeredLTL = new Not<String>(new And<String>(new Not<String>(new AP<String>("t(" + (String)action + ")")), new Not<>(weakTriggeredLTL)));
            }
            // If Then.. (a -> b) equals (!a or b =  !!(!a or b) = !(a and !b))
            LTL<String> newWeakActionGroup = new Not<String>(new And<String>(createEventuallyAlwaysLTL(weakEnabledLTL), new Not<String>(createAlwaysEventuallyLTL(weakTriggeredLTL))));
            finalWeakActionGroup = new And(newWeakActionGroup, finalWeakActionGroup);
        }

        LTL<String> conjunctionFinalFairLtl = new And(finalUncondActionGroup, new And(finalStrongActionGroup, finalWeakActionGroup));
        LTL<String> finalFairLtl = new Not<String>(new And<String>(conjunctionFinalFairLtl, new Not<String>((LTL<String>)ltl)));
        return (LTL<P>)finalFairLtl;
    }

    public <P> LTL<P> createAlwaysEventuallyLTL(LTL<P> ltl) {
        return new Not<>(new Until<>(new TRUE<>(),
                new Not<>(new Until<>(new TRUE<>(), ltl))));
    }

    public <P> LTL<P> createEventuallyAlwaysLTL(LTL<P> ltl) {
        return new Until<>(new TRUE<>(),
                new Not<>(new Until<>(new TRUE<>(), new Not<>(ltl))));
    }
}
