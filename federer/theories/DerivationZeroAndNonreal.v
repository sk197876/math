(** The exceptional value sets in Federer (1969), 2.9.7, p. 155. Z consists
    of zero derivate values. W is corrected by Federer's May 1987 erratum,
    p. 3, book p. 155 line 26: D is not real valued there. For a partial
    graph this includes undefined points as well as infinite values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology CountableOrderIntervals TopologicalBorel BorelFamilyBasic
  PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureDerivationContext MeasureDerivates CoveringRelationLimits AbsoluteContinuousPart
  MeasureAbsoluteContinuity BoundedNullLocalisation SmallCoefficientMeasureBound
  DerivationComparison DerivationExistence DerivationMeasurable
  MeasurableFunctionBorel DensityCellBounds MeasureDensityUP MeasureDensityNullSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_zero_points]: direct Z in
    Federer 2.9.7, p. 155. Only points
    with a defined zero value belong to Z. *)
Definition derivation_zero_points (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop) :=
  [set x | partial_function_graph (measure_derivate psi phi V) x 0].

(** Source for [derivation_nonreal_points]: corrected W in
    Federer 2.9.7, p. 155; erratum p. 3,
    book p. 155 line 26. No finite real
    graph value exists at a point of W, including
    points outside the partial derivative's domain. *)
Definition derivation_nonreal_points (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop) :=
  [set x | ~ exists r : R, partial_function_graph (measure_derivate psi phi V) x r%:E].

(** Source for [derivation_zero_points_measurable]: measurability
    of Z from 2.9.6 in the proof of Federer
    2.9.7, p. 155. The value singleton is
    the intersection of two closed order rays. *)
Lemma derivation_zero_points_measurable (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  measure_measurable phi (derivation_zero_points psi phi V).
Proof.
move=> hc hp; have hm := derivation_measure_law (derivation_context_measure hc).
have hf := @federer_2_9_6 R X phi psi V hc hp.
have he : [set y : extended_real_line R | y=0]=
    [set y | y<=0] `&` [set y | 0<=y].
  apply/seteqP; split=> [y ->|y [h1 h2]]; first by split; exact: lexx.
  apply/eqP; by rewrite eq_le h1 h2.
have hB : borel_set [set y : extended_real_line R | y=0].
  rewrite he; apply: (@borel_family_binary_intersection (extended_real_line R) setT _ (borel_sets_family (extended_real_line R))).
  - apply: closed_borel_set; exact (@order_closed_lower_ray_closed _ [the orderTopologicalType _ of order_topology (\bar R)] 0).
  - apply: closed_borel_set; exact (@order_closed_upper_ray_closed _ [the orderTopologicalType _ of order_topology (\bar R)] 0).
have hz := @measurable_function_borel_preimage R X (extended_real_line R) phi hm (measure_derivate psi phi V) hf _ hB.
have hpre : partial_function_preimage (measure_derivate psi phi V) [set y | y=0]=derivation_zero_points psi phi V.
  apply/seteqP; split.
  - move=> x [y [hy hy0]]; change (partial_function_graph (measure_derivate psi phi V) x 0).
    by rewrite -hy0.
  - move=> x hx; exists 0; by split.
by rewrite hpre in hz.
Qed.

(** Source for [derivation_nonreal_points_null]: phi(W)=0
    in Federer 2.9.7, p. 155, with
    the erratum's corrected W. The finite graph
    existence theorem 2.9.5 excludes both infinite values
    and undefined points almost everywhere. *)
Lemma derivation_nonreal_points_null (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  phi (derivation_nonreal_points psi phi V)=0.
Proof.
move=> hc hp; have hm := derivation_measure_law (derivation_context_measure hc).
have h := @federer_2_9_5 R X phi psi V hc hp.
apply: (@measure_null_subset R X phi hm _
  (~` [set x | exists y, partial_function_graph (measure_derivate psi phi V) x y /\ 0<=y /\ y< +oo])) h.
move=> x hn [y [hy [hy0 hyf]]].
have hyfin : y \is a fin_num by rewrite (ge0_fin_numE hy0).
apply: hn; exists (fine y); by rewrite fineK.
Qed.

(** Source for [continuous_part_zero_points_null]: psi_phi(Z)=0
    in Federer 2.9.7, p. 155. On
    bounded subsets, apply 2.9.4 at every positive
    coefficient and use finite reference mass; then
    exhaust by countably many bounded pieces. *)
Lemma continuous_part_zero_points_null (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  measure_continuous_part psi phi (derivation_zero_points psi phi V)=0.
Proof.
move=> hc hp; have hf := derivation_context_measure hc.
have hm := derivation_measure_law hf.
have hmg := @measure_continuous_part_is_measure R X psi phi hm (derivation_measure_law hp).
apply: (@measure_null_of_bounded_subsets R X (measure_continuous_part psi phi) _ hmg)=> A hAb hAZ.
apply (@finite_reference_small_coefficients_zero R (measure_continuous_part psi phi A) (phi A)
  (measure_nonnegative hmg A) (measure_nonnegative hm A)
  (@derivation_measure_bounded_finite R X phi hf A hAb)).
move=> c hcpos; apply: (@derivation_lower_comparison R X phi psi V A c hc hp hcpos)=> x hx.
have [_ [_ hl]] := hAZ x hx; rewrite hl lte_fin; exact hcpos.
Qed.

(** Source for [continuous_part_nonreal_points_null]: psi_phi(W)=0
    in Federer 2.9.7, p. 155, using
    the corrected non-real-value exceptional set and
    absolute continuity from 2.9.2. *)
Lemma continuous_part_nonreal_points_null (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  measure_continuous_part psi phi (derivation_nonreal_points psi phi V)=0.
Proof.
move=> hc hp.
exact (@continuous_part_absolutely_continuous R X phi psi (measure_continuous_part psi phi)
  (derivation_measure_law hp) (measure_continuous_part_specification psi phi) _
  (@derivation_nonreal_points_null R X phi psi V hc hp)).
Qed.

(** Source for [derivation_density_zero_points_null]: zero
    integral over Z in Federer 2.9.7, p. 155.
    Both constant bounds are zero, including when
    phi(Z) is infinite under the special product convention. *)
Lemma derivation_density_zero_points_null (R : realType) (X : metricType R)
    (phi psi nu : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  is_measure_density phi (measure_derivate psi phi V) nu ->
  nu (derivation_zero_points psi phi V)=0.
Proof.
move=> hc hp hn.
have hm := derivation_measure_law (derivation_context_measure hc).
have hvalues x : derivation_zero_points psi phi V x -> exists y,
    partial_function_graph (measure_derivate psi phi V) x y /\ (0%R)%:E<=y /\ y<=(0%R)%:E.
  move=> hx; exists 0; by split=> //; split.
have [hl hu] := @density_measurable_cell_bounds R X phi nu (measure_derivate psi phi V)
  (derivation_zero_points psi phi V) 0%R 0%R hm hn
  (@derivation_zero_points_measurable R X phi psi V hc hp) (lexx 0%R) (lexx 0%R) hvalues.
rewrite !mul0e in hl hu; apply/eqP; by rewrite eq_le hu hl.
Qed.
