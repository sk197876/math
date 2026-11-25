(** Federer (1969), 2.5.12, printed pp. 104–105: the measurable members of Q
    are summable in norm. These adapters connect that statement to the
    project's partial-function L1 interface from 2.4.12, pp. 86–87. The
    closed linear span of the countable dense set is the whole target. it
    has no counterpart to 2.5.12. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ModuleQuotient MetricSubsetBackground
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialNormedArithmetic
  PartialNormPower RealPower MeasureUP MeasureBasic MeasurableFunctionUP
  MeasurableNormedFunctionUP MeasurableNormedDifference ClosedLinearSpanUP
  ClosedLinearSpanSealed NormClosureLaws SummableRealFunctionUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralUniqueness
  MeasureLoneNormIntegralGeneral MeasureLpNorm MeasureLpMembershipUP
  MeasureLpConvergence MeasureLpCountableMeasurability VectorDaniellRationalSpan.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_separable_vector_total]: the
    separability assumption in Federer 2.5.12(1), p. 102,
    ensures that every measurable E-valued function belongs
    to A(phi,E) from 2.3.8, p. 78. This also handles an
    empty source and a zero-dimensional target. *)
Lemma measurable_separable_vector_total (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (D : set E) (hD : is_rational_dense_subspace hN D)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (f : X -> real_norm_metric_space hN) :
  is_measure_measurable_function phi (partial_function_total f) ->
  is_measurable_normed_function phi (partial_function_total f).
Proof.
move=> hf; split=> //.
pose Z := @ClosedLinearSpan.value R E N hN D.
have hZ := @ClosedLinearSpan.laws R E N hN D.
have hwhole : forall x : real_norm_metric_space hN, Z x.
  exact: dense_closed_superset_all hD.2.1
    (closed_linear_span_closed hZ) (closed_linear_span_contains hZ).
exists Z; split; first exact: ClosedLinearSpan.countable_separable hD.1.
rewrite partial_function_total_preimage.
have he : f @^-1` [set y | ~ Z y] = set0.
  apply/seteqP; split=> x; last by [].
  move=> hx; exact: hx (hwhole (f x)).
rewrite he; exact: measure_empty hphi.
Qed.

(** Source for [total_vector_norm_integral]: the L1 norm is
    the integral of the pointwise norm, Federer 2.4.12, p. 86,
    used for the error estimates in 2.5.12, p. 105.
    The identity permits an infinite value. *)
Lemma total_vector_norm_integral (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (f : X -> real_norm_metric_space hN) :
  is_measure_measurable_function phi (partial_function_total f) ->
  is_measure_integral phi (real_total_integrand (fun x => N (f x)))
    (measure_lp_norm phi N 1%R (partial_function_total f)).
Proof.
move=> hf.
have hi := measurable_lone_norm_integral hphi hf.
apply: (measure_integral_graph_equivalent _ hi)=> x z.
rewrite real_total_integrand_graph; split.
- move=> [y [hy he]].
  by rewrite -(hy : f x=y) real_power_one_exponent
    ?(real_seminorm_nonnegative hN.1) in he.
- move=> he; exists (f x); split=> //.
  by rewrite real_power_one_exponent ?(real_seminorm_nonnegative hN.1).
Qed.

(** Source for [separable_vector_summable_norm_lone]: the
    inference that w is in L1 from measurability and summable
    norm, Federer 2.5.12, p. 105. Countable measurability
    is derived from finite L1 norm rather than assumed. *)
Lemma separable_vector_summable_norm_lone (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (D : set E) (hD : is_rational_dense_subspace hN D)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (f : X -> real_norm_metric_space hN) (a : R) :
  is_measure_measurable_function phi (partial_function_total f) ->
  is_measure_integral phi (real_total_integrand (fun x => N (f x))) a%:E ->
  is_measure_lp_function phi 1%R (partial_function_total f).
Proof.
move=> hf hi.
have he := measure_integral_unique (total_vector_norm_integral hphi hf) hi.
have hfin : measure_lp_norm phi N 1%R (partial_function_total f) < +oo.
  by rewrite he ltry.
split; first exact: lexx.
split; first exact (@measurable_separable_vector_total R X E N hN D hD phi hphi f hf).
split=> //; exact (@finite_lp_norm_countably_measurable R X E N hN phi hphi 1%R (partial_function_total f) (lexx _) hf hfin).
Qed.

(** Source for [total_vector_lone_distance_integral]: the
    integral of nu(f-g) is the L1 distance used in the
    approximation estimate of Federer 2.5.12, p. 105.
    This is a graph adapter for the abstract L1 norm. *)
Lemma total_vector_lone_distance_integral (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (f g : X -> real_norm_metric_space hN) :
  is_measurable_normed_function phi (partial_function_total f) ->
  is_measurable_normed_function phi (partial_function_total g) ->
  is_measure_integral phi (real_total_integrand (fun x => N (f x-g x)%R))
    (measure_lp_distance phi N 1%R (partial_function_total f) (partial_function_total g)).
Proof.
move=> hf hg.
have hd := measurable_normed_function_subtract hphi hf hg.
have hi := measurable_lone_norm_integral hphi hd.1.
apply: (measure_integral_graph_equivalent _ hi)=> x z.
rewrite real_total_integrand_graph; split.
- move=> [y [/partial_vector_subtract_graph [u [v [hu [hv hy]]]] he]].
  rewrite -(hu : f x=u) -(hv : g x=v) in hy; subst y.
  by rewrite real_power_one_exponent ?(real_seminorm_nonnegative hN.1) in he.
- move=> he; exists (f x-g x)%R; split.
  + apply/partial_vector_subtract_graph; exists (f x), (g x); by split=> //; split.
  + by rewrite real_power_one_exponent ?(real_seminorm_nonnegative hN.1).
Qed.
