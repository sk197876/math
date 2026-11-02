(** Federer (1969), 2.5.5, p. 97: the almost-everywhere subsequence must
    converge to the prescribed limits f and zero. Uniqueness up to almost
    equality follows from the pseudometric laws in 2.3.8, p. 78. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasureAlmostUP
  MeasurableNormedFunctionUP MeasureConvergenceUP MeasureDistanceLaws ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convergent_in_measure_limits_almost_equal]: supporting
    uniqueness for the two uses of Federer 2.3.10 in 2.5.5, p. 97 *)
Lemma convergent_in_measure_limits_almost_equal (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g h : partial_function X (real_norm_metric_space hN)) :
  (forall n, is_measurable_normed_function mu (f n)) ->
  is_measurable_normed_function mu g -> is_measurable_normed_function mu h ->
  converges_in_measure mu N f g -> converges_in_measure mu N f h -> measure_almost_equal mu g h.
Proof.
move=> hf hg hh hfg hfh.
have hsmall e : (0 < e)%R -> measure_normed_distance mu N g h < e%:E.
  move=> he; have he2 : (0 < e/2)%R by rewrite divr_gt0 // ltr0n.
  have [K hK] := hfg _ he2; have [M hM] := hfh _ he2.
  pose n := maxn K M.
  have hb := @measure_normed_distance_triangle R X V N hN mu hm g (f n) h hg (hf n) hh.
  rewrite (@measure_normed_distance_symmetric R X V N hN mu g (f n)) in hb.
  have hs := lteD (hK n (leq_maxl K M)) (hM n (leq_maxr K M)).
  rewrite -EFinD -splitr in hs; exact: le_lt_trans hb hs.
apply: (@measure_normed_distance_zero_iff R X V N hN mu hm g h hg hh).1.
apply/eqP; rewrite eq_le (@measure_normed_distance_nonnegative R X V N hN mu g h) andbT.
apply: (@extended_real_reciprocal_upper_bound R (measure_normed_distance mu N g h) 0%R)=> n.
rewrite add0r; apply: ltW; apply: hsmall; by rewrite invr_gt0 ltr0n.
Qed.
