(** Supporting pseudometric consequence of Federer (1969), 2.3.10, p. 80:
    convergence in measure implies the Cauchy property. The corollary is
    additional supporting material, not a separately numbered Federer
    assertion. Source context: CauchyIndexSelectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP
  MeasurableNormedFunctionUP MeasureConvergenceUP MeasureDistanceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convergent_in_measure_cauchy]: supporting Cauchy property
    for the completeness assertion in Federer 2.3.10, p. 80 *)
Lemma convergent_in_measure_cauchy (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (h : partial_function X (real_norm_metric_space hN)) :
  (forall n, is_measurable_normed_function mu (f n)) ->
  is_measurable_normed_function mu h -> converges_in_measure mu N f h ->
  cauchy_in_measure mu N f.
Proof.
move=> hf hh hl e he.
have he2 : (0 < e/2)%R by rewrite divr_gt0 // ltr0n.
have [K hK] := hl _ he2; exists K=> n m hn hm'.
have ht := @measure_normed_distance_triangle R X V N hN mu hm (f n) h (f m)
  (hf n) hh (hf m).
rewrite (@measure_normed_distance_symmetric R X V N hN mu h (f m)) in ht.
apply: le_lt_trans ht _.
have hsum := lteD (hK n hn) (hK m hm').
by rewrite -EFinD -splitr in hsum.
Qed.
