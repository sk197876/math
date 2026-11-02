(** Federer (1969), 1.8.1, p. 38: supporting reduction of finite convex
    representations. Choose the least positive-coefficient ratio to
    eliminate one weight without making another negative. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [convex_coefficient_elimination]: Federer 1.8.1,
    p. 38, supporting coefficient step: if a nonnegative weight family
    is adjusted along a relation with nonnegative total, a suitable
    nonnegative adjustment kills one weight, preserves nonnegativity,
    and does not increase the total. *)
Theorem convex_coefficient_elimination (R : realFieldType) (I : finType)
    (a b : I -> R) : (forall i, 0 <= a i) -> 0 <= \sum_i b i ->
    (exists i, 0 < b i) -> exists t : R, exists j : I,
    0 <= t /\ (forall i, 0 <= a i-t*b i) /\ a j-t*b j = 0 /\
    \sum_i (a i-t*b i) <= \sum_i a i.
Proof.
move=> ha hb [i0 hi0].
have [j hj hmin] := @arg_minP _ _ I i0 (fun i => 0 < b i)
  (fun i => a i / b i) hi0.
pose t := a j / b j.
have ht : 0 <= t by rewrite /t divr_ge0 //; exact: ltW hj.
have hc i : 0 <= a i-t*b i.
  rewrite subr_ge0; have [hbi|hbi] := ltP 0 (b i).
  - rewrite -(@ler_pdivlMr R (b i) t (a i) hbi); exact: hmin i hbi.
  - have hh := ler_wpM2l ht hbi.
    rewrite mulr0 in hh; exact: le_trans hh (ha i).
exists t, j; split=> //; split=> //; split.
- by rewrite /t divfK ?subrr // (gt_eqF hj).
- rewrite sumrB -mulr_sumr lerBlDr lerDl.
  exact: mulr_ge0 ht hb.
Qed.

(** Source for [weighted_relation_adjustment]: Federer 1.8.1,
    p. 38, supporting algebra: subtracting a scalar multiple of a
    vanishing linear relation preserves the represented vector. *)
Lemma weighted_relation_adjustment (R : fieldType) (I : finType)
    (V : lmodType R) (a b : I -> R) (u : I -> V) t :
  \sum_i b i *: u i = 0 ->
  \sum_i (a i-t*b i) *: u i = \sum_i a i *: u i.
Proof.
move=> hb; under eq_bigr do rewrite scalerBl -scalerA.
by rewrite sumrB -scaler_sumr hb scaler0 subr0.
Qed.
