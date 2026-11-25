(** Federer (1969), 2.9.9, pp. 156–157: fixed-target distance functions in
    the Lebesgue-point proof. We retain Federer's exponent one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureSubsetIntegral MeasureDerivationContext CoveringFamilyUP CoveringRelationUP
  CoveringRelationLimits MeasurableDistanceTo DistanceSubsetIntegral MetricPairDistance
  MeasureMeanFunction MeasureLebesgueSet DistanceMeanFamily CoveringLipschitzFamily
  NonnegativeMeasureDifferentiation NormClosureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [metric_lebesgue_points_almost_everywhere]: supporting metric
    form of Federer 2.9.9, pp. 156–157, using its exact countable dense set
    and closed T(x) proof. Local integrability of the distance to one base
    point replaces the norm hypothesis in this supporting generalisation.
    its broader p-version is not assumed. *)
Theorem metric_lebesgue_points_almost_everywhere (R : realType) (X Y : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X Y) (base : Y) (D : set Y) :
  is_measure_derivation_context phi V -> is_measure_measurable_function phi f ->
  countable D -> dense D ->
  (forall A, metric_set_bounded A -> measure_measurable phi A -> exists a : R,
    is_measure_subset_integral phi A (partial_distance_to f base) a%:E) ->
  measure_almost_everywhere phi (measure_lebesgue_set phi V f).
Proof.
move=> hc hf hDc hDd hlocal.
have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
have hu := @distance_means_form_lipschitz_family R X Y phi V f base hc hf hlocal.
have hlocal_y y A : metric_set_bounded A -> measure_measurable phi A -> exists a : R,
    is_measure_subset_integral phi A (partial_distance_to f y) a%:E.
  move=> hAb hAm; have [a ha] := hlocal A hAb hAm.
  have hAf : phi A \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm A)).
    exact: derivation_measure_bounded_finite hphi A hAb.
  have he : phi A=(fine (phi A))%:E by rewrite fineK.
  have [b [hb _]] := @distance_subset_integral_bound R X Y phi f A a (fine (phi A)) base y hm hf hAm he ha.
  by exists b.
pose P y := partial_function_agreement
  (covering_relation_limit V (measure_mean_function phi (partial_distance_to f y)))
  (partial_distance_to f y).
have hP : measure_almost_everywhere phi (\bigcap_(y in D) P y).
  apply: (@measure_almost_everywhere_countable R X Y phi hm D P hDc)=> y _.
  exact (@nonnegative_measure_differentiation R X phi V (partial_distance_to f y) hc
    (@measurable_partial_distance_to R X Y phi f y hm hf)
    (@partial_distance_to_nonnegative R X Y phi f y hm hf) (hlocal_y y)).
have hgood := @measure_almost_everywhere_and R X phi hm _ _ (measurable_function_domain hf) hP.
apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ hgood)=> x [[a ha] hPx].
pose l y := mdist a y.
pose T := [set y | partial_function_graph
  (covering_relation_limit V (measure_mean_function phi (partial_distance_to f y))) x (l y)%:E].
have hl y z : (`|l y-l z|<=mdist y z)%R.
  have h := metric_pair_distance_change_bound a y a z.
  by rewrite mdistxx add0r in h.
have hT : closed T.
  exact (@covering_lipschitz_limit_locus_closed R X Y V
    (fun y => measure_mean_function phi (partial_distance_to f y)) 1%R l x (@ltr01 R) hu hl).
have hDT : D `<=` T.
  move=> y hy; have [r [hmean [b [hb he]]]] := hPx y hy.
  have eba := partial_function_single_valued hb ha.
  rewrite eba in he; rewrite -he in hmean; exact hmean.
have hTa := @dense_closed_superset_all Y D T hDd hT hDT a.
exists a; split=> //.
have hzero : (l a)%:E=(0 : \bar R) by rewrite /l mdistxx.
by rewrite -hzero.
Qed.
