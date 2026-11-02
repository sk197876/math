(** Federer (1969), 2.3.8, p. 79, last paragraph: the finite-measure
    hypothesis is on the set where f is nonzero. This identifies it with the
    positive norm locus used in the tail proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  MeasureUP MeasurableNormedFunctionUP MeasurableNormSuperlevels MeasureGauge MeasureGaugeScalarContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_nonzero_norm_locus]: supporting equality
    of the nonzero and positive-norm loci in the last paragraph
    of Federer 2.3.8, p. 79, using norm definiteness. *)
Lemma partial_nonzero_norm_locus (R : realType) (X : Type) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (f : partial_function X V) :
  partial_norm_superlevel N f 0 = partial_function_preimage f [set y | y <> 0%R].
Proof.
apply/seteqP; split=> x [y [hy hn]]; exists y; split=> //.
- move=> he; have hn' : (0 < N y)%R := hn.
  by rewrite he (real_seminorm_zero hN.1) ltxx in hn'.
- change (0 < N y)%R; rewrite (@real_norm_positive R V N hN.1 hN.2).
  by apply/eqP.
Qed.

(** Source for [measurable_normed_scalar_continuity]: direct
    finite-nonzero-locus formulation of Federer 2.3.8, p. 79 The conclusion
    is the epsilon-delta form of cf tending to zero in measure as the scalar
    c tends to zero. *)
Theorem measurable_normed_scalar_continuity (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measurable_normed_function mu f ->
  mu (partial_function_preimage f [set y | y <> 0%R]) < +oo ->
  forall e : R, (0 < e)%R -> exists d : R, (0 < d)%R /\ forall c : R,
    (`|c| < d)%R -> measure_gauge mu N (partial_vector_scale c f) < e%:E.
Proof.
move=> hf hfin e he.
apply: (@measure_gauge_scalar_continuity R X V mu hm N hN.1 f e _ _ he).
- exact (@measurable_norm_superlevel R X V N hN mu hm f hf.1).
- by rewrite (partial_nonzero_norm_locus hN).
Qed.
