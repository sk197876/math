(** Federer (1969), 4.1.5, p. 350:
    weak convergence of distributions implies
    convergence of each original real evaluation.
    Use the original weak convergence laws
    and the actual scalar norm balls. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import WeakEvaluationConvergenceUP OpenFamilyConvergence RealOpenSequenceFacts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weak_sequence_real_evaluations_limit]: the
    original evaluation limits used in both
    lower-semicontinuity inequalities of Federer
    4.1.5, p. 350. *)
Theorem weak_sequence_real_evaluations_limit (R:realType) (E D:choiceType)
    (ev:D->E->R) (O:set (set D)) (hO:is_weak_evaluation_convergence ev O)
    (S:nat->D) (T:D):
  open_family_converges O (S @ \oo) T ->forall phi:E,forall eta:R,0<eta ->
    exists N,forall i,(N<=i)%N ->`|ev (S i) phi-ev T phi|<eta.
Proof.
move=>hCvg phi eta hEta.
have hF:Filter (S @ \oo):=fmap_filter S (@filter_filter nat eventually eventually_filter).
have hCoordinate:=(hO (S @ \oo) hF T).1 hCvg phi.
have hAt:([set t:R | `|t-ev T phi|<eta]) (ev T phi) by rewrite /= subrr normr0.
have[N _ hN]:=hCoordinate _ (@real_open_scalar_ball R (ev T phi) eta) hAt.
exists N=>i hI; exact:hN i hI.
Qed.
