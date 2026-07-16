package cn.edu.nju.Iot_Verify.component.fuzz.paper;

/** Resolves one structured specification atom against the current model state. */
@FunctionalInterface
public interface PaperAtomValuation {

    boolean isTrue(PaperAtom atom);
}
