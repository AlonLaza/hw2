package il.ac.bgu.cs.fvm.examples;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import java.util.LinkedList;
import java.util.List;

public class AlternatingBitProtocolBuilder {

    static FvmFacade fvmFacadeImpl = FvmFacade.get();

    public static ChannelSystem<String, String> build() {
        List<ProgramGraph<String, String>> pgs = new LinkedList<>();

        pgs.add(buildSender());
        pgs.add(buildTimer());
        pgs.add(buildReciever());

        return new ChannelSystem<>(pgs);
    }

    private static ProgramGraph<String, String> buildReciever() {
        ProgramGraph<String, String> pg = fvmFacadeImpl.createProgramGraph();

        String wait_0 = "wait(0)";
        String pr_msg_0 = "pr_msg(0)";
        String snd_ack_0 = "snd_ack(0)";
        String wait_1 = "wait(1)";
        String pr_msg_1 = "pr_msg(1)";
        String snd_ack_1 = "snd_ack(1)";

        pg.addLocation(wait_0);
        pg.addLocation(pr_msg_0);
        pg.addLocation(snd_ack_0);
        pg.addLocation(wait_1);
        pg.addLocation(pr_msg_1);
        pg.addLocation(snd_ack_1);

        pg.setInitial(wait_0, true);

        pg.addTransition(new PGTransition<>(wait_0, "", "C?y", pr_msg_0));
        pg.addTransition(new PGTransition<>(pr_msg_0, "y == 1", "", wait_0));
        pg.addTransition(new PGTransition<>(pr_msg_0, "y == 0", "", snd_ack_0));
        pg.addTransition(new PGTransition<>(snd_ack_0, "size(D)<3", "D!0", wait_1));

        pg.addTransition(new PGTransition<>(wait_1, "", "C?y", pr_msg_1));
        pg.addTransition(new PGTransition<>(pr_msg_1, "y == 0", "", wait_1));
        pg.addTransition(new PGTransition<>(pr_msg_1, "y == 1", "", snd_ack_1));
        pg.addTransition(new PGTransition<>(snd_ack_1, "size(D)<3", "D!1", wait_0));

        return pg;

    }

    private static ProgramGraph<String, String> buildSender() {
        ProgramGraph<String, String> pg = fvmFacadeImpl.createProgramGraph();

        String snd_msg_0 = "snd_msg(0)";
        String st_tmr_0  = "set_tmr(0)";
        String wait_0    = "wait(0)";
        String chk_ack_0 = "chk_ack(0)";
        String snd_msg_1 = "snd_msg(1)";
        String st_tmr_1  = "set_tmr(1)";
        String wait_1    = "wait(1)";
        String chk_ack_1 = "chk_ack(1)";

        pg.addLocation(snd_msg_0);
        pg.addLocation(st_tmr_0);
        pg.addLocation(wait_0);
        pg.addLocation(chk_ack_0);
        pg.addLocation(snd_msg_1);
        pg.addLocation(st_tmr_1);
        pg.addLocation(wait_1);
        pg.addLocation(chk_ack_1);

        pg.setInitial(snd_msg_0, true);

        pg.addTransition(new PGTransition<>(snd_msg_0, "size(C)<3", "C!0", st_tmr_0));
        pg.addTransition(new PGTransition<>(snd_msg_0, "", "", st_tmr_0));
        pg.addTransition(new PGTransition<>(st_tmr_0, "", "_tmr_on!", wait_0));
        pg.addTransition(new PGTransition<>(wait_0, "", "_timeout?", snd_msg_0));
        pg.addTransition(new PGTransition<>(wait_0, "", "D?x", chk_ack_0));
        pg.addTransition(new PGTransition<>(chk_ack_0, "x == 1", "", wait_0));
        pg.addTransition(new PGTransition<>(chk_ack_0, "x == 0", "_tmr_off!", snd_msg_1));
                                         
        pg.addTransition(new PGTransition<>(snd_msg_1, "size(C)<3", "C!1", st_tmr_1));
        pg.addTransition(new PGTransition<>(snd_msg_1, "", "", st_tmr_1)); // lost
        pg.addTransition(new PGTransition<>(st_tmr_1, "", "_tmr_on!", wait_1));
        pg.addTransition(new PGTransition<>(wait_1, "", "_timeout?", snd_msg_1));
        pg.addTransition(new PGTransition<>(wait_1, "", "D?x", chk_ack_1));
        pg.addTransition(new PGTransition<>(chk_ack_1, "x == 0", "", wait_1));
        pg.addTransition(new PGTransition<>(chk_ack_1, "x == 0", "_tmr_off!", snd_msg_0));

        return pg;

    }

    private static ProgramGraph<String, String> buildTimer() {
        ProgramGraph<String, String> pg = fvmFacadeImpl.createProgramGraph();

        String onLocation = "on";
        String offLocation = "off";

        pg.addLocation(onLocation);
        pg.addLocation(offLocation);

        pg.setInitial(offLocation, true);

        pg.addTransition(new PGTransition<>(onLocation, "", "_tmr_off?", offLocation));
        pg.addTransition(new PGTransition<>(onLocation, "", "_timeout!", offLocation));
        pg.addTransition(new PGTransition<>(offLocation, "", "_tmr_on?", onLocation));

        return pg;

    }

}
