(** Federer (1969), 2.2.9, p. 65, supporting continuity and interval filling
    of finite continued fractions. The pseudometric_normed_Zmodule and
    normed_module imports supply ordinary real arithmetic continuity and the
    intermediate value theorem, used only as real order-topology background.
    No external continued-fraction theorem is used. Source context and
    supporting references: ContinuedFractionBranches.v and
    ContinuedFractionWords.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import ContinuedFractionBranches ContinuedFractionBlocks ContinuedFractionWords.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continued_fraction_branch_continuous]: supporting
    finite-expression continuity for the continued-fraction map
    of Federer 2.2.9, p. 65. Nonnegative tails
    keep each reciprocal denominator strictly positive. *)
Lemma continued_fraction_branch_continuous (R : realType) a (t : R) :
  0 <= t -> {for t, continuous (continued_fraction_branch a : R^o -> R^o)}.
Proof.
move=> ht; rewrite /continued_fraction_branch.
apply: continuousV.
- by rewrite gt_eqF //; exact: (@continued_fraction_denominator_positive R a t ht).
- exact (@cvgD R [the pseudoMetricNormedZmodType R of R^o] R^o (nbhs t) _
    (fun _ => a.+1%:R) id a.+1%:R t (cvg_cst _) (fun U hU => hU)).
Qed.

(** Source for [continued_fraction_block_continuous]: supporting
    continuity of four grouped terms of the continued fraction
    in Federer 2.2.9, p. 65. *)
Lemma continued_fraction_block_continuous (R : realType) d (t : R) :
  0 <= t -> {for t, continuous (continued_fraction_block d : R^o -> R^o)}.
Proof.
move=> ht; case: d=> [[a b] [c d]]; rewrite /continued_fraction_block /=.
have hdt := ltW (continued_fraction_branch_unit_bounds d ht).1.
have hct := ltW (continued_fraction_branch_unit_bounds c hdt).1.
have hbt := ltW (continued_fraction_branch_unit_bounds b hct).1.
apply: continuous_comp; last exact: (@continued_fraction_branch_continuous R a _ hbt).
apply: continuous_comp; last exact: (@continued_fraction_branch_continuous R b _ hct).
apply: continuous_comp; last exact: (@continued_fraction_branch_continuous R c _ hdt).
exact: continued_fraction_branch_continuous ht.
Qed.

(** Source for [continued_fraction_word_continuous]: supporting
    continuity of every finite grouped prefix in Federer 2.2.9,
    p. 65, including the empty prefix. *)
Lemma continued_fraction_word_continuous (R : realType) d s (t : R) :
  0 <= t -> {for t, continuous (continued_fraction_word d s : R^o -> R^o)}.
Proof.
elim: s t=> [|j s IH] t ht /=; first by move=> U hU.
apply: continuous_comp; first exact: continued_fraction_block_continuous ht.
exact: IH _ (ltW (continued_fraction_block_inside (d j) ht).1).
Qed.

(** Source for [continued_fraction_word_interval_image]: supporting
    exact open cylinder image in the continued-fraction comparison
    of Federer 2.2.9, p. 65. Every point strictly
    between the endpoint values is attained by a unique tail
    strictly between zero and one; uniqueness follows separately
    from strict monotonicity. Bell2016 Theorem 2, p. 5,
    states the corresponding irrational cylinders. *)
Lemma continued_fraction_word_interval_image (R : realType) d s (x : R) :
  continued_fraction_word d s 0 < x -> x < continued_fraction_word d s 1 ->
  exists t : R, 0 < t /\ t < 1 /\ continued_fraction_word d s t = x.
Proof.
move=> hx0 hx1.
pose f : R^o -> R^o := continued_fraction_word d s.
have h01 : f 0 < f 1 := continued_fraction_word_increasing d s (lexx 0) ltr01.
have hc : {within `[0,1], continuous f}.
  apply: continuous_in_subspaceT=> t ht.
  apply: continued_fraction_word_continuous.
  by move: ht; rewrite inE /= => /andP[ht _].
have hh : Order.min (f 0) (f 1) <= x <= Order.max (f 0) (f 1).
  by rewrite min_l ?max_r ?(ltW h01) // (ltW hx0) (ltW hx1).
have [t ht hft] := @IVT R f 0 1 x ler01 hc hh.
have /andP[ht0 ht1] : (0 : R) <= t <= 1 by move: ht; rewrite in_itv.
exists t; split.
- rewrite lt_neqAle ht0 andbT; apply/eqP=> he; subst t.
  by move: hx0; rewrite -hft ltxx.
- split; last exact hft.
  rewrite lt_neqAle ht1 andbT; apply/eqP=> he; subst t.
  by move: hx1; rewrite -hft ltxx.
Qed.
