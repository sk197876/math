(** Federer (1969), 2.9.20, statement p. 165 and proof p. 166: the four
    equivalent characterisations of absolute continuity for a real function
    of locally finite variation on a finite nondegenerate segment. The proof
    follows the printed cycle (1)=>(2)=>(3)=>(4)=>(1), with the dyadic
    finite-union implementation documented for (3)=>(4). No relevant Federer
    erratum entry applies. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesImageMeasures
  RealAbsoluteContinuityUP IndefiniteDerivativeVariationEquality
  VariationEqualityAbsoluteContinuity AbsoluteContinuityInducedMeasures
  ContinuousInducedIntegralRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [federer_2_9_20]: complete corollary in Federer 2.9.20, pp.
    165–166 All four printed conditions are equivalent under the original
    locally finite variation and induced-pair hypotheses. Integrals are
    actual relations for the partial derivative, cell lengths are strict
    with non-strict sum bounds, and condition (4) uses relative
    closed-segment continuity and open-interval measure restrictions. No
    global endpoint continuity, prior derivative existence, or derivative
    measurability is added. *)
Theorem federer_2_9_20 (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> a<b ->
  (real_curve_indefinite_derivative_integral g a b <->
    real_curve_variation_integral_equality g a b) /\
  (real_curve_variation_integral_equality g a b <->
    is_absolutely_continuous_real_curve g a b) /\
  (is_absolutely_continuous_real_curve g a b <->
    real_curve_continuous_induced_measures g psip psim a b).
Proof.
move=> hg hp hab.
have h12 := @indefinite_derivative_integral_variation_equality R g psip psim a b hg hp (ltW hab).
have h23 := @variation_integral_equality_absolute_continuity R g psip psim a b hg hp (ltW hab).
have h34 := @real_absolute_continuity_induced_measures R g psip psim a b hg hp.
have h41 := @continuous_induced_integral_representation R g psip psim a b hg hp hab.
split.
- split; [exact h12|move=> h2; exact: h41 (h34 (h23 h2))].
- split.
  + split; [exact h23|move=> h3; exact: h12 (h41 (h34 h3))].
  + split; [exact h34|move=> h4; exact: h23 (h12 (h41 h4))].
Qed.
