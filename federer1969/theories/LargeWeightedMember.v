(** Supporting real-order estimate for Federer (1969), proof of 2.8.4, p.
    143: choose W whose weight times tau bounds the weights of all remaining
    eligible members. This lemma proves the supremum selection, including
    the zero supremum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_nonnegative_large_member]: the selection of W in the
    final paragraph of Federer 2.8.4, p. 143 For a nonempty family of
    bounded nonnegative weights and tau>1, one member has tau times its
    weight at least every weight in the family. Neither a positive weight
    nor attainment of the supremum is assumed. *)
Lemma bounded_nonnegative_large_member (R : realType) (I : choiceType)
    (P : set I) (d : I -> R) (tau : R) :
  (exists i, P i) -> (forall i, P i -> 0 <= d i) ->
  (exists C, forall i, P i -> d i <= C) -> 1 < tau ->
  exists w, P w /\ forall i, P i -> d i <= tau * d w.
Proof.
move=> [i0 hi0] hnon [C hC] ht.
pose S := d @` P.
have hS : S !=set0 by exists (d i0); exists i0.
have hb : has_ubound S.
  exists C=> x [i hi <-]; exact: hC.
have hupper i (hi : P i) : d i <= sup S.
  have hd : S (d i) by exists i.
  exact (@ub_le_sup R S hb (d i) hd).
have hM : 0 <= sup S := le_trans (hnon i0 hi0) (hupper i0 hi0).
have ht0 : 0 < tau := lt_trans ltr01 ht.
case: (eqVneq (sup S) 0)=> [hz|hnz].
- exists i0; split=> // i hi.
  apply: le_trans (hupper i hi) _; rewrite hz.
  exact: mulr_ge0 (ltW ht0) (hnon i0 hi0).
- have hMp : 0 < sup S by rewrite lt_neqAle eq_sym hnz hM.
  have hsmall : sup S / tau < sup S.
    by rewrite ltr_pdivrMr // ltr_pMr.
  have [y [w hw <-] hy] := @sup_gt R S (sup S / tau) hS hsmall.
  have hmul : sup S < tau * d w.
    move: hy; by rewrite ltr_pdivrMr // mulrC.
  exists w; split=> // i hi; exact: le_trans (hupper i hi) (ltW hmul).
Qed.
