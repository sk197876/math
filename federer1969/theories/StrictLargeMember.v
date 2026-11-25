(** Supporting supremum selection in Federer (1969), proof of 2.8.10, p.
    147: among the remaining positive radii choose t with tau*t strictly
    larger than their supremum. it does not state this lemma. We retain
    Federer's supremum argument, without assuming attainment of a maximum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_positive_strict_large_member]: the
    choice tau*t>sup radii in Federer 2.8.10, p. 147.
    Positivity of the weights excludes zero supremum; a member
    above sup/tau exists since tau>1. This supporting version
    is stated for an arbitrary nonempty family of positive weights. *)
Lemma bounded_positive_strict_large_member (R : realType) (I : choiceType)
    (P : set I) (d : I -> R) (tau : R) :
  (exists i, P i) -> (forall i, P i -> 0 < d i) ->
  (exists C, forall i, P i -> d i <= C) -> 1 < tau ->
  exists w, P w /\ forall i, P i -> d i < tau * d w.
Proof.
move=> [i0 hi0] hpos [C hC] ht.
pose S := d @` P.
have hS : S !=set0 by exists (d i0); exists i0.
have hb : has_ubound S by exists C=> x [i hi <-]; exact: hC.
have hupper i (hi : P i) : d i <= sup S.
  have hd : S (d i) by exists i.
  exact (@ub_le_sup R S hb (d i) hd).
have hM : 0 < sup S := lt_le_trans (hpos i0 hi0) (hupper i0 hi0).
have ht0 : 0 < tau := lt_trans ltr01 ht.
have hsmall : sup S / tau < sup S by rewrite ltr_pdivrMr // ltr_pMr.
have [y [w hw <-] hy] := @sup_gt R S (sup S / tau) hS hsmall.
have hmul : sup S < tau * d w.
  move: hy; by rewrite ltr_pdivrMr // mulrC.
exists w; split=> // i hi; exact: le_lt_trans (hupper i hi) hmul.
Qed.
