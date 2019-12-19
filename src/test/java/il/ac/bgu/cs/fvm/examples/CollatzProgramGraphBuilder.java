package il.ac.bgu.cs.fvm.examples;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import static java.util.Arrays.asList;


public class CollatzProgramGraphBuilder {

    static FvmFacade fvmFacadeImpl = FvmFacade.get();

    public static ProgramGraph<String, String> build() {
        ProgramGraph<String, String> pg = fvmFacadeImpl.createProgramGraph();

        String running = "running";
        String finished = "finished";

        pg.addLocation(running);
        pg.addLocation(finished);

        pg.setInitial(running, true);

        pg.addTransition(new PGTransition<>(running, "x % 2 == 1 && x != 1", "x:= (3 * x) + 1", running));
        pg.addTransition(new PGTransition<>(running, "x % 2 == 0", "x:= x / 2", running));
        pg.addTransition(new PGTransition<>(running, "x == 1", "", finished));

        pg.addInitalization(asList("x:=6"));

        return pg;
    }

}
