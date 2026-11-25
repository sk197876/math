(** Federer (1969), 2.2.15, p. 71, final target characterisation: a Baire
    map from R has finite collections of values approximable by one
    continuous curve. This supplies the sequential-closure argument for
    necessity. Federer states the criterion without its proof; the lemmas
    here are supporting details, not separately printed assertions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground PointwiseLimit PointwiseFiniteSamples
  BaireFunctionUP BaireFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [curve_sample_approximable]: supporting class
    for the necessity of the final criterion in Federer 2.2.15,
    p. 71. Its members have every finite collection
    of source values approximable by the image of one continuous curve. *)
Definition curve_sample_approximable (R : realType) (Y : metricType R)
    (f : real_line_metric R -> Y) : Prop :=
  forall F : set (real_line_metric R), finite_set F -> forall epsilon : R, 0 < epsilon ->
  exists c : real_line_metric R -> Y, continuous c /\
    forall x, F x -> exists t, mdist (f x) (c t) < epsilon.

(** Source for [continuous_curve_samples]: continuous generators
    for the finite-sample class supporting Federer 2.2.15,
    p. 71. The continuous function itself is the curve. *)
Lemma continuous_curve_samples (R : realType) (Y : metricType R)
    (f : real_line_metric R -> Y) : continuous f -> curve_sample_approximable f.
Proof.
move=> hf F hF e he; exists f; split=> // x hx; exists x; by rewrite mdistxx.
Qed.

(** Source for [curve_samples_pointwise_closed]: supporting
    sequential closure for the necessity proof of Federer 2.2.15,
    p. 71. Approximate the finitely many limiting values
    by one sequence stage within epsilon/2, then approximate
    that stage's values by a curve within epsilon/2. *)
Lemma curve_samples_pointwise_closed (R : realType) (Y : metricType R) :
  @is_baire_class R (real_line_metric R) Y (@curve_sample_approximable R Y).
Proof.
move=> f g hf hlim F hF e he.
have he2 : 0 < e / 2 by rewrite divr_gt0 // ltr0n.
have [N hN] := @pointwise_limit_finite_samples R [the choiceType of real_line_metric R]
  Y f g F (e/2) hlim hF he2.
have [c [hc happ]] := hf N F hF (e/2) he2.
exists c; split=> // x hx; have [t ht] := happ x hx; exists t.
have hh := ltrD (hN N (leqnn N) x hx) ht.
rewrite -splitr in hh; exact: le_lt_trans (metric_triangle (g x) (f N x) (c t)) hh.
Qed.

(** Source for [baire_real_domain_curve_samples]: supporting
    necessity principle for Federer 2.2.15, p. 71.
    The smallest Baire class is contained in the sequentially
    closed finite-sample class, which contains all continuous curves. *)
Theorem baire_real_domain_curve_samples (R : realType) (Y : metricType R)
    (f : real_line_metric R -> Y) :
  is_baire_function f -> curve_sample_approximable f.
Proof.
apply: (@baire_function_induction R [the topologicalType of real_line_metric R] Y
  (@curve_sample_approximable R Y)).
- exact: curve_samples_pointwise_closed.
- exact: continuous_curve_samples.
Qed.
