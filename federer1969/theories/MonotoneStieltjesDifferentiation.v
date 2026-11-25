(** Federer (1969), 2.9.19, p. 164: the monotone case. A finite derivate of
    the positive induced measure controls the increment quotient at almost
    every point. We remove the already known countable discontinuity set
    before that argument; the final almost-everywhere assertion has no added
    continuity hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesMonotone
  StieltjesImageMeasures StieltjesIntervalIncrements StieltjesFiniteDerivates
  RealBVContinuityPoints ScalarIntervalDerivationContext ScalarIntervalDerivateBounds
  MonotoneDenseIncrementBounds RealCurveDerivativeUP RealIncrementDifferentiation
  MeasureAlmostUP MeasureAlmostBasic MeasureDerivates PartialFunctionUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [monotone_stieltjes_derivative_at_continuity_point]: direct
    pointwise monotone argument in Federer 2.9.19, p. 164 At a continuity
    point, a finite nonnegative derivate lambda of psi+ equals the
    derivative of g. Dense continuity endpoints first give the increment
    estimates; monotonicity extends them to all endpoints, then both signs
    of the increment give the two-sided derivative. *)
Lemma monotone_stieltjes_derivative_at_continuity_point (R : realType)
    (g : R -> R) (psip psim : set R -> \bar R) (x lambda : R) :
  (forall a b : R, a<=b -> g a<=g b) -> is_induced_measure_pair g psip psim ->
  g @ x --> g x -> 0<=lambda ->
  partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R] psip (@lebesgue_scalar_measure R)
    (@scalar_nondegenerate_interval_relation R)) x lambda%:E ->
  has_real_curve_derivative g x lambda.
Proof.
move=> hmono hp hcx hlambda hD.
have hg := @monotone_locally_finite_variation R g hmono.
pose D : set (real_line_metric R) := [set t | g @ t --> g t].
have hDense : dense D := @real_bv_continuity_points_dense R g hg.
have hxD : D x := hcx.
apply: interval_increment_bounds_derivative=> e he.
have [d [hd hmass]] := @scalar_interval_derivate_mass_bounds R psip x lambda e hD he.
exists d; split=> // a b haxb hwidth.
have hEnds (u v : R) : D u -> D v -> u<=x<=v -> 0<v-u<d ->
    (lambda-e)*(v-u)<=g v-g u /\ g v-g u<=(lambda+e)*(v-u).
  move=> huD hvD huxv hw.
  have huv : u<v by have hpos := (andP hw).1; rewrite -subr_gt0.
  have hinc := @stieltjes_monotone_closed_interval_increment R g psip psim u v
    hg hmono hp huv huD hvD.
  have [hl hu] := hmass u v huxv hw.
  split; [by move: hl; rewrite hinc lee_fin|by move: hu; rewrite hinc lee_fin].
split.
- apply: (@monotone_dense_increment_lower_bound R D g x hDense hxD hmono (lambda-e) d a b)=> //.
  by move=> u v hu hv huxv hw; exact: (hEnds u v hu hv huxv hw).1.
- have hU : 0<lambda+e by lra.
  apply: (@monotone_dense_increment_upper_bound R D g x hDense hmono (lambda+e) d a b hU)=> //.
  by move=> u v hu hv huxv hw; exact: (hEnds u v hu hv huxv hw).2.
Qed.

(** Source for [monotone_stieltjes_derivative_ae]: direct almost-everywhere
    monotone conclusion in Federer 2.9.19, p. 164 For every induced pair,
    the finite nonnegative derivative agrees with the positive
    induced-measure derivate outside a null set. The countable discontinuity
    set is removed only in the proof, not added as a hypothesis on g. *)
Lemma monotone_stieltjes_derivative_ae (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) :
  (forall a b : R, a<=b -> g a<=g b) -> is_induced_measure_pair g psip psim ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set x | exists v : R,
    0<=v /\ has_real_curve_derivative g x v /\
    partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R] psip (@lebesgue_scalar_measure R)
      (@scalar_nondegenerate_interval_relation R)) x v%:E].
Proof.
move=> hmono hp.
have hg := @monotone_locally_finite_variation R g hmono.
have hvals := @stieltjes_induced_derivates_finite_ae R g psip psim hg hp.
have hcont := @real_bv_continuity_ae R g hg.
have hboth := measure_almost_everywhere_and (lebesgue_scalar_is_measure R) hvals hcont.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hboth).
move=> x [[p [m [hp0 [hm0 [hpD hmD]]]]] hcx].
exists p; split=> //; split=> //.
exact (@monotone_stieltjes_derivative_at_continuity_point R g psip psim x p hmono hp hcx hp0 hpD).
Qed.

(** Source for [monotone_real_derivative_exists_ae]: the monotone
    differentiability result used in Federer 2.9.19, p. 164 Existence of the
    induced measures is supplied by 2.5.17. A nondecreasing real function
    has a finite nonnegative derivative almost everywhere. *)
Theorem monotone_real_derivative_exists_ae (R : realType) (g : R -> R) :
  (forall a b : R, a<=b -> g a<=g b) ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : R, 0<=v /\ has_real_curve_derivative g x v].
Proof.
move=> hmono.
have hg := @monotone_locally_finite_variation R g hmono.
have [psip [psim hp]] := @induced_measure_pair_exists R g hg.
have hD := @monotone_stieltjes_derivative_ae R g psip psim hmono hp.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hD).
by move=> x [v [hv [hder _]]]; exists v.
Qed.
