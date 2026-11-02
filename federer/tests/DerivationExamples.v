(** Regression examples for Federer's derivates, subsection 2.9.
    Source passages and edition comparisons accompany each example;
    the public definitions and laws are in DerivationTheorems.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology ring lra.
From Federer Require Import DerivationTheorems MeasureUP MeasureBasic RealNormUP NormMetric
  MeasureVectorIntegralUP MeasurableTotalBasic ModuleQuotient SubspaceCarrier
  Hom ContinuousDualUP ContinuousDualNorm ContinuousBidualUP ContinuousRealFunctional CompleteMetricUP
  MeasureLpMembershipUP MeasureIntegralUP ExtendedRealOrderLimit SummableRealSpace SummableRealFunctionUP SummableRealArithmetic
  RealErrorOrderLimit StieltjesIntegral StieltjesContinuityPoints StieltjesMonotone
  StieltjesSubstitution
  PartialFunctionUP MeasureDerivates AbsoluteContinuousPartBasic PointMassMeasure
  FiniteExceptionalBorel MeasureRestriction MeasureAlmostBasic CoveringFamilyUP MetricDiameter TopologicalBorel
  CoveringRelationLimits ExtendedRealBounds MeasurableFunctionUP ExtendedRealOrderTopology PartialFunctionBasic MeasureSubsetIntegral MeasureSplit RealMetricBackground PartialFunctionPostcomposition PointMassRegularity
  FunctionLatticeUP TotalScalarLpUP MeasureAlmostUP MeasureHull
  InfiniteDiscreteMeasure CoveringRelationUP CoveringFamilyLaws MetricClosedBalls PositiveRightOrderLimit
  GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanCoordinateMetric LebesgueScalarMeasure DirectionalLimitationUP
  CurveVariationUP CurveArcLength StieltjesImageMeasures MeasureSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_denominator_ratio_undefined]: zero-
    denominator regression for the quotient in Federer 2.9.1,
    p. 153, under the partial arithmetic convention of
    2.1.1, p. 51. Even a zero numerator does
    not assign a value to 0/0. *)
Example null_denominator_ratio_undefined (R : realType) (X : Type) (A : set X) :
  ~ partial_function_domain
    (measure_ratio_function (fun _ : set X => (0 : \bar R)) (fun _ => 0)) A.
Proof. exact: measure_ratio_zero_denominator. Qed.

(** Source for [unit_denominator_ratio_evaluates]: positive-
    denominator regression for Federer 2.9.1, p. 153.
    Division by a finite unit preserves an arbitrary numerator,
    including an infinite one. *)
Example unit_denominator_ratio_evaluates (R : realType) (X : Type)
    (psi : set X -> \bar R) (A : set X) :
  partial_function_graph (measure_ratio_function psi (fun _ => 1)) A (psi A).
Proof.
have he := @measure_ratio_positive_finite_denominator R X psi (fun _ => 1) A.
rewrite inve1 mule1 in he; apply: he; [exact: lte01|by rewrite fin_numE].
Qed.

(** Source for [null_reference_continuous_part_zero]: null-
    reference-measure regression for the infimum in Federer
    2.9.1, p. 152. If the reference measure
    vanishes everywhere, every set has zero continuous-part value,
    independently of the numerator measure's total mass. *)
Example null_reference_continuous_part_zero (R : realType) (X : topologicalType)
    (psi : set X -> \bar R) : is_measure psi ->
  forall A, measure_continuous_part psi (fun _ => 0) A = 0.
Proof.
move=> hm A; exact (@continuous_part_null R X (fun _ => 0) psi
  (measure_continuous_part psi (fun _ => 0)) hm
  (measure_continuous_part_specification psi (fun _ => 0)) A (erefl _)).
Qed.

(** Source for [infinite_pair_ratio_undefined]: infinity/
    infinity regression for Federer 2.9.1, p. 153,
    under the ordinary arithmetic of 2.1.1, p. 51.
    Globally unbounded cells are not assigned a default quotient;
    later local boundedness arguments avoid this case. *)
Example infinite_pair_ratio_undefined (R : realType) (X : Type) (A : set X) :
  ~ partial_function_domain
    (measure_ratio_function (fun _ : set X => (+oo : \bar R)) (fun _ => +oo)) A.
Proof.
move=> [y hy]; move: hy; rewrite /measure_ratio_function /=
  ExtendedRealConventions.extended_divide_infinities; discriminate.
Qed.

(** Source for [continuous_part_of_self]: self-reference
    regression for Federer 2.9.2, p. 153,
    also used explicitly in 2.9.4, p. 154.
    The total measure need not be finite. *)
Example continuous_part_of_self (R : realType) (X : metricType R)
    (phi : set X -> \bar R) :
  is_derivation_measure phi -> measure_continuous_part phi phi=phi.
Proof.
move=> hphi; symmetry.
apply: (@continuous_part_equality_iff_absolute_continuity R X phi phi
  (measure_continuous_part phi phi) (derivation_measure_law hphi)
  (derivation_measure_law hphi) (derivation_measure_borel_regular hphi)
  (measure_continuous_part_specification phi phi)).2.
by move=> A hz.
Qed.

(** Source for [empty_ambient_bounded_borel_partition]:
    empty-space regression for the global partition in
    Federer 2.9.2, p. 153. The constant
    empty sequence meets every law without choosing a center. *)
Example empty_ambient_bounded_borel_partition (R : realType) (X : metricType R) :
  (forall x : X, False) -> is_bounded_borel_partition (fun _ : nat => @set0 X).
Proof.
move=> hempty; constructor.
- by move=> n; exact: open_borel_set open0.
- by move=> n; rewrite /metric_set_bounded extended_metric_diameter_empty ltry.
- apply/seteqP; split=> [x [n _ []]|x _]; exfalso; exact: hempty x.
- by move=> n m h x [].
Qed.

(** Source for [null_reference_remaining_component]: totally
    singular reference regression for Federer 2.9.2, p. 153.
    If the reference measure is zero, the complementary
    restriction recovers the whole numerator measure, even
    when it has infinite total mass. *)
Example null_reference_remaining_component (R : realType) (X : metricType R)
    (psi : set X -> \bar R) (B : set X) :
  is_derivation_measure psi ->
  is_continuous_part_decomposition (fun _ => 0) psi (measure_continuous_part psi (fun _ => 0)) B ->
  measure_restrict psi (~` B)=psi.
Proof.
move=> hpsi hd; apply: funext=> A.
have hzero := @continuous_part_null R X (fun _ => 0) psi
  (measure_continuous_part psi (fun _ => 0)) (derivation_measure_law hpsi)
  (measure_continuous_part_specification psi (fun _ => 0)) A (erefl _).
have he := @continuous_decomposition_sum R X (fun _ => 0) psi
  (measure_continuous_part psi (fun _ => 0)) B hd A.
by rewrite hzero add0e in he; exact: esym he.
Qed.

(** Source for [reference_null_atom_continuous_part_zero]: singular-atom
    regression for Federer 2.9.2, p. 153. this supporting generalisation
    uses any reference measure null on the atom. *)
Example reference_null_atom_continuous_part_zero (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (a : X) :
  is_measure phi -> phi [set a]=0 ->
  forall A, measure_continuous_part (point_mass R a) phi A=0.
Proof.
move=> hphi hz A.
have hm := @point_mass_is_measure R X a.
have hg := @measure_continuous_part_specification R X (point_mass R a) phi.
have hb : borel_set (~` [set a]) := borel_set_complement
  (@finite_metric_set_borel R X [set a] (finite_set1 a)).
have hpoint : point_mass R a (~` [set a])=0.
  apply: (@point_mass_out R X a (~` [set a]))=> hn; exact: hn (erefl _).
apply/eqP; rewrite eq_le (continuous_part_nonnegative hm hg A) andbT -hpoint.
apply: (@continuous_part_lower R X phi (point_mass R a)
  (measure_continuous_part (point_mass R a) phi) hg A (~` [set a]) hb).
apply: (@measure_null_subset R X phi hphi _ [set a]) hz.
move=> x [_ hn]; apply: contrapT=> hx; apply: hn; exact hx.
Qed.


(** Source for [empty_target_lower_comparison]: empty-target
    regression for Federer 2.9.3, p. 154. The
    theorem does not require the target or ambient space
    to be nonempty. *)
Example empty_target_lower_comparison (R : realType) (X : metricType R)
    (phi alpha beta : set X -> \bar R) (V : X -> set X -> Prop) (c : R) :
  is_measure_derivation_context phi V ->
  is_derivation_measure alpha -> is_derivation_measure beta -> (0<c)%R ->
  measure_continuous_part alpha phi set0<=c%:E*measure_continuous_part beta phi set0.
Proof. move=> hc ha hb hp; apply: (@federer_2_9_3 R X phi alpha beta V set0 c hc ha hb hp); by move=> x []. Qed.

(** Source for [zero_denominator_excludes_sublevel_cell]:
    partial-domain regression for the auxiliary relation in
    Federer 2.9.3, p. 154, under the ordinary
    arithmetic of 2.1.1, p. 51. A zero
    denominator cannot be made eligible by assigning 0/0
    a default value. *)
Example zero_denominator_excludes_sublevel_cell (R : realType) (X : metricType R)
    (alpha : set X -> \bar R) (V : X -> set X -> Prop) W b cap x S :
  ~ covering_lower_sublevel V (measure_ratio_function alpha (fun _ => 0)) b W cap x S.
Proof.
move=> [_ [_ [_ [y [hy _]]]]].
apply: (@measure_ratio_zero_denominator R X alpha (fun _ => 0) S (erefl _)).
by exists y.
Qed.

(** Source for [vanishing_error_zero_mass_bound]: zero-mass
    boundary for the final epsilon argument in Federer 2.9.3,
    p. 154. Arbitrarily small positive error bounds
    force a nonpositive value even though extended infinities
    are allowed in the candidate value. *)
Example vanishing_error_zero_mass_bound (R : realType) (a : \bar R) :
  (forall e : R, (0<e)%R -> a<=e%:E) -> a<=0.
Proof.
move=> h.
have hh := @scaled_nonnegative_measure_approximation_bound R a 0 1%R (lexx 0) (@ltr01 R).
rewrite mule0 in hh; apply: hh=> e he.
by rewrite add0e mul1e; exact: h e he.
Qed.


(** Source for [infinite_upper_ratio_reciprocal_bound]:
    infinite-upper-limit regression for the reciprocal step
    of Federer 2.9.4, p. 154. The threshold
    chosen below the upper limit remains finite even when
    that limit is positive infinity. *)
Example infinite_upper_ratio_reciprocal_bound (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop) x :
  is_derivation_measure psi -> is_derivation_measure phi ->
  covering_upper_limit V (measure_ratio_function psi phi) x=+oo ->
  covering_lower_limit V (measure_ratio_function phi psi) x<1.
Proof.
move=> hp hf hu.
have hh := @derivation_strict_reciprocal_limit R X psi phi V x 1%R hp hf (@ltr01 R).
rewrite invr1 in hh; apply: hh; rewrite hu; exact: ltry.
Qed.

(** Source for [empty_target_upper_comparison]: empty-target
    regression for the second implication of Federer 2.9.4,
    p. 154. No ambient inhabitedness or target
    nonemptiness is assumed in either implication. *)
Example empty_target_upper_comparison (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) (c : R) :
  is_measure_derivation_context phi V -> is_derivation_measure psi -> (0<c)%R ->
  c%:E*phi set0<=measure_continuous_part psi phi set0.
Proof.
move=> hc hp hpos.
apply: (@federer_2_9_4 R X phi psi V c hc hp hpos).2.
by move=> x [].
Qed.


(** Source for [null_reference_derivate_nowhere_defined]:
    partial-domain boundary for Federer 2.9.5, pp. 154–155.
    A zero reference measure gives no defined quotient,
    hence no defined ordinary derivate at any point.
    Its almost-everywhere assertion is nevertheless valid
    because the whole space is reference-null. This is
    a supporting regression, not a separate printed claim. *)
Example null_reference_derivate_nowhere_defined (R : realType) (X : metricType R)
    (psi : set X -> \bar R) (V : X -> set X -> Prop) x :
  ~ partial_function_domain (measure_derivate psi (fun _ => 0) V) x.
Proof.
pose f := measure_ratio_function psi (fun _ => 0).
have hempty e : covering_value_range V f x e=set0.
  apply/seteqP; split=> [y [S [_ [_ hy]]]|y []].
  exfalso; apply: (@measure_ratio_zero_denominator R X psi (fun _ => 0) S (erefl _)).
  by exists y.
have hu := @covering_upper_limit_le_level R X V f x 1%R (@ltr01 R).
have hl := @covering_lower_limit_ge_level R X V f x 1%R (@ltr01 R).
rewrite hempty extended_real_sup_empty in hu.
rewrite hempty extended_real_inf_empty in hl.
move=> [y [_ [hyu hyl]]].
rewrite hyu in hu; rewrite hyl in hl.
by have := le_trans hl hu.
Qed.

(** Source for [infinite_bound_does_not_force_zero_mass]:
    finiteness regression for the Q argument in Federer
    2.9.5, p. 155. Every positive multiple
    of a unit mass is below infinity, although that
    mass is positive. Thus the finite numerator bound
    in the proof cannot simply be dropped. *)
Example infinite_bound_does_not_force_zero_mass (R : realType) :
  (forall c : R, (0<c)%R -> c%:E*(1 : \bar R)<=+oo) /\ 0<(1 : \bar R).
Proof. split; [by move=> c _; exact: leey|exact: lte01]. Qed.

(** Source for [positive_gap_from_zero_to_infinity]: endpoint
    regression for the rational-gap exhaustion in Federer
    2.9.5, p. 154. A zero lower endpoint
    and an infinite upper endpoint still admit two
    strictly positive rational indices. *)
Example positive_gap_from_zero_to_infinity (R : realType) :
  exists p : rat*rat, positive_rational_gaps R p /\
    0<(ratr p.1 : R)%:E /\ (ratr p.2 : R)%:E< +oo.
Proof.
apply: (@positive_rational_gap_between R 0 +oo (lexx 0)).
exact: ltry.
Qed.


(** Source for [negative_derivate_level_empty]: negative-level
    regression for the sign reduction in Federer 2.9.6,
    p. 155. Every defined value is nonnegative,
    so the closed level at minus one is empty,
    independently of the almost-everywhere existence theorem. *)
Example negative_derivate_level_empty (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure phi -> is_measure psi ->
  partial_function_preimage (measure_derivate psi phi V) [set y | y<=(-1%R)%:E]=set0.
Proof.
move=> hf hp; apply/seteqP; split=> [x [y [hy hyle]]|x []].
have hy0 := @measure_derivate_value_nonnegative R X phi psi V x y hf hp hy.
have hneg : (-1%R : R)%:E<0 by rewrite lte_fin oppr_lt0 ltr01.
by have := le_lt_trans (le_trans hy0 hyle) hneg; rewrite ltxx.
Qed.

(** Source for [null_reference_measurable_empty_derivate]:
    partial-domain regression for Federer 2.9.6, p. 155,
    under the conull-domain convention of 2.3.2, p. 73.
    For a null reference, the derivate's empty domain
    is conull and the partial function is measurable.
    No value is inserted into the empty graph. *)
Example null_reference_measurable_empty_derivate (R : realType) (X : metricType R)
    (psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context (fun _ => 0) V -> is_derivation_measure psi ->
  @is_measure_measurable_function R X (extended_real_line R) (fun _ => 0) (measure_derivate psi (fun _ => 0) V) /\
    partial_function_domain (measure_derivate psi (fun _ => 0) V)=set0.
Proof.
move=> hc hp; split; first exact (@federer_2_9_6 R X (fun _ => 0) psi V hc hp).
apply/seteqP; split=> [x hx|x []].
exfalso; exact (@null_reference_derivate_nowhere_defined R X psi V x hx).
Qed.


(** Source for [null_reference_nonreal_set_whole]: regression
    for the corrected W in Federer 2.9.7, p. 155;
    erratum p. 3, book p. 155 line 26.
    With a zero reference measure the derivate is
    nowhere defined, so every point lies in W,
    although no point has an infinite graph value. *)
Example null_reference_nonreal_set_whole (R : realType) (X : metricType R)
    (psi : set X -> \bar R) (V : X -> set X -> Prop) :
  derivation_nonreal_points psi (fun _ => 0) V=setT.
Proof.
apply/seteqP; split=> [x _|x _] //.
move=> [r hr]; apply: (@null_reference_derivate_nowhere_defined R X psi V x).
by exists r%:E.
Qed.

(** Source for [geometric_unit_endpoint_convention]: endpoint
    regression for the half-open levels in Federer 2.9.7,
    p. 156. The unit value belongs to
    [1,t) and is excluded from the preceding band,
    retaining exactly the book's endpoint convention. *)
Example geometric_unit_endpoint_convention (R : realType) (X : Type) (x : X) (t : R) :
  (1<t)%R ->
  geometric_function_band (partial_function_total (fun _ : X => (1 : extended_real_line R))) t 0%Z x /\
  ~ geometric_function_band (partial_function_total (fun _ : X => (1 : extended_real_line R))) t (-1)%Z x.
Proof.
move=> ht; split.
- exists 1; split; first by [].
  rewrite expr0z add0r expr1z; split; [exact: lexx|by rewrite lte_fin].
- move=> [y [hy [_ hhi]]].
  have hy1 : (1 : \bar R)=y := hy.
  by move: hhi; rewrite -hy1 ltxx.
Qed.

(** Source for [empty_target_derivate_integral]: empty-target
    regression for the complete integral formula in Federer
    2.9.7, pp. 155–156. The subset integral
    is zero even if the derivate is undefined
    at points outside the target. *)
Example empty_target_derivate_integral (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  is_measure_subset_integral phi set0 (measure_derivate psi phi V) 0.
Proof.
move=> hc hp; have hm := derivation_measure_law (derivation_context_measure hc).
have h := (@federer_2_9_7 R X phi psi V set0 hc hp (measure_measurable_empty hm)).2.
have hmg := @measure_continuous_part_is_measure R X psi phi hm (derivation_measure_law hp).
by rewrite (measure_empty hmg) in h.
Qed.


(** Source for [zero_mass_bound_allows_positive_reference]: local scalar
    counterexample to the printed conclusion phi(C)=0. The inequality at
    every positive coefficient forces psi_phi(C)=0, as used by Federer
    2.9.7, p. 155, and does not force the reference mass to vanish. *)
Example zero_mass_bound_allows_positive_reference (R : realType) :
  (forall c : R, (0<c)%R -> (0 : \bar R)<=c%:E*1) /\ 0<(1 : \bar R).
Proof.
split; last exact: lte01.
move=> c hc; rewrite mule1 lee_fin; exact: ltW hc.
Qed.


(** Source for [empty_cell_mean_undefined]: empty-cell
    regression for the integral means in Federer 2.9.8,
    p. 156. The empty subset integral is
    zero, but its zero denominator still leaves
    the ordinary mean undefined. *)
Example empty_cell_mean_undefined (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R)) :
  is_measure phi -> ~ partial_function_domain (measure_mean_function phi f) set0.
Proof. move=> hm; exact: measure_mean_zero_denominator (measure_empty hm). Qed.

(** Source for [zero_reference_mean_undefined]: partial-domain
    regression for Federer 2.9.8, p. 156.
    A null reference gives no mean value on
    any cell, regardless of its numerator integral. *)
Example zero_reference_mean_undefined (R : realType) (X : choiceType)
    (f : partial_function X (extended_real_line R)) S :
  ~ partial_function_domain (measure_mean_function (fun _ : set X => (0 : \bar R)) f) S.
Proof. exact: measure_mean_zero_denominator. Qed.

(** Source for [negative_unit_cell_mean]: signed-value
    regression for Federer 2.9.8, p. 156.
    A subset integral of minus one and unit
    reference mass give a mean of minus one,
    with no nonnegative-only restriction on the numerator. *)
Example negative_unit_cell_mean (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R)) S :
  is_measure_subset_integral phi S f (-1%R)%:E -> phi S = 1 ->
  partial_function_graph (measure_mean_function phi f) S (-1%R)%:E.
Proof.
move=> hi hS.
have h := @finite_measure_mean_value R X phi f S (-1)%R 1%R hi hS (@ltr01 R).
by rewrite divr1 in h.
Qed.

(** Source for [empty_graph_needs_limit_domain_fineness]: domain-fineness
    regression for the signed limit step in Federer 2.9.8, p. 156 An empty
    graph satisfies all value bounds vacuously and still has no ordinary
    covering limit. *)
Example empty_graph_needs_limit_domain_fineness (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) x :
  (forall e : R, (0<e)%R -> exists d : R, (0<d)%R /\ forall S y,
    V x S -> extended_metric_diameter S<d%:E ->
    partial_function_graph (@partial_function_empty (set X) (\bar R)) S y ->
    (-e)%R%:E<y /\ y<e%:E) /\
  ~ partial_function_domain (covering_relation_limit V (@partial_function_empty (set X) (\bar R))) x.
Proof.
split.
- move=> e he; exists 1%R; split; first exact: ltr01.
  by move=> S y hS hd [].
- move=> [y [_ [hu hl]]].
  rewrite covering_upper_limit_empty_function in hu.
  rewrite covering_lower_limit_empty_function in hl.
  by rewrite -hu in hl.
Qed.


(** Source for [real_distance_integrand_value]: scalar-target
    regression for the integrand in Federer 2.9.9, p. 156.
    The identity function on the real line gives exactly the
    absolute value of x-y, preserving the subtraction order. *)
Example real_distance_integrand_value (R : realType) (x y : real_line_metric R) :
  partial_function_graph
    (partial_distance_to (partial_function_total (fun z : real_line_metric R => z)) y)
    x (`|x-y|%R)%:E.
Proof. exists x; split=> //; exact: real_line_metric_distanceE. Qed.

(** Source for [empty_function_has_empty_lebesgue_set]: partial-domain
    regression for the Lebesgue-set definition in Federer 2.9.9,
    p. 156. An undefined value cannot be a Lebesgue point. *)
Example empty_function_has_empty_lebesgue_set (R : realType) (X Y : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) :
  measure_lebesgue_set phi V (@partial_function_empty X Y)=set0.
Proof. apply/seteqP; split=> x; [by move=> [a [[] _]]|by move=> []]. Qed.

(** Source for [zero_reference_has_no_lebesgue_points]: null-reference
    regression for Federer 2.9.9, p. 156. All ordinary cell means
    have undefined zero denominator; their empty graphs give no
    Lebesgue point, even though an almost-everywhere assertion for
    the null measure is vacuous. *)
Example zero_reference_has_no_lebesgue_points (R : realType) (X Y : metricType R)
    (V : X -> set X -> Prop) (f : partial_function X Y) :
  measure_lebesgue_set (fun _ : set X => (0 : \bar R)) V f=set0.
Proof.
apply/seteqP; split=> x; last by move=> [].
move=> [a [_ hlim]].
have heq t S : V t S -> forall b,
    partial_function_graph (measure_mean_function (fun _ : set X => (0 : \bar R))
      (partial_distance_to f a)) S b <->
    partial_function_graph (@partial_function_empty (set X) (\bar R)) S b.
  move=> _ b; split; last by move=> [].
  move=> hb; apply: (@measure_mean_zero_denominator R X (fun _ => 0)
    (partial_distance_to f a) S erefl); by exists b.
have h := (@covering_limit_graph_equivalent R X V _ _ heq x 0).1 hlim.
have [_ [_ hl]] := h.
by rewrite covering_lower_limit_empty_function in hl.
Qed.


(** Source for [reference_null_atom_derivate_zero]: singular-atom regression
    for Federer 2.9.10, p. 157. A point mass at a reference-null singleton
    has zero reference derivate almost everywhere. Membership of the point
    mass in M is proved. *)
Example reference_null_atom_derivate_zero (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (a : X) :
  is_measure_derivation_context phi V -> phi [set a]=0 ->
  measure_almost_everywhere phi [set x | partial_function_graph (measure_derivate (point_mass R a) phi V) x 0].
Proof.
move=> hc hz.
have hpoint : is_derivation_measure (point_mass R a).
  constructor.
  - exact: point_mass_is_measure.
  - apply: point_mass_borel_regular.
    apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
  - move=> S _; exact: le_lt_trans (@point_mass_le1 R X a S) (ltry 1%R).
apply: (@zero_continuous_part_derivate_zero R X phi (point_mass R a) V hc hpoint).
apply: funext=> A; exact (@reference_null_atom_continuous_part_zero R X phi a
  (derivation_measure_law (derivation_context_measure hc)) hz A).
Qed.

(** Source for [unit_linfinity_with_infinite_reference_mass]:
    boundary regression for the L-infinity tests in Federer
    2.9.10, p. 157. Constant one remains an admissible
    test when phi(X) is infinite. The finite-mass hypothesis
    of the Daniell observation concerns psi, not phi. *)
Example unit_linfinity_with_infinite_reference_mass (R : realType) (X : metricType R)
    (phi : set X -> \bar R) :
  is_derivation_measure phi -> phi setT=+oo ->
  total_scalar_lp phi +oo (fun _ => 1%R).
Proof. move=> hphi _; exact: derivation_constant_one_linfinity hphi. Qed.

(** Source for [empty_bounded_target_unit_cutoff]: empty-target
    regression for the bounded-support continuous lattice of
    Federer 2.9.10, p. 157. A unit cutoff on the empty
    target exists without an inhabited ambient metric space. *)
Example empty_bounded_target_unit_cutoff (R : realType) (X : metricType R) :
  exists f : X -> R, positive_function_lattice (@bounded_support_continuous_functions R X) f /\
    forall x, set0 x -> f x = 1%R.
Proof.
apply: (@bounded_set_unit_test_exists R X set0).
by rewrite /metric_set_bounded extended_metric_diameter_empty ltry.
Qed.


(** Source for [zero_reference_density_point_sets_empty]: partial-domain
    regression for P and Q in Federer 2.9.11, p. 158. A
    zero reference measure gives no defined ratio or derivate, so
    both level sets are empty; their almost-everywhere conclusions
    remain valid because every set is reference-null. *)
Example zero_reference_density_point_sets_empty (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (A : set X) :
  measure_density_one_points (fun _ : set X => (0 : \bar R)) V A=set0 /\
  measure_density_complement_zero_points (fun _ : set X => (0 : \bar R)) V A=set0.
Proof.
split; apply/seteqP; split=> x; try by move=> [].
- move=> hx; exfalso; apply: (@null_reference_derivate_nowhere_defined R X
    (measure_restrict (fun _ => 0) A) V x); by exists 1.
- move=> hx; exfalso; apply: (@null_reference_derivate_nowhere_defined R X
    (measure_restrict (fun _ => 0) (~` A)) V x); by exists 0.
Qed.

(** Source for [atom_density_point_conditions]: positive-mass
    regression for Federer 2.9.11, p. 158. If an arbitrary
    set contains the atom of a unit point mass, both density
    conditions hold at that atom for every admissible Vitali
    relation. The limits are actual defined values, rather than
    consequences of a vacuous zero-reference assertion. *)
Example atom_density_point_conditions (R : realType) (X : metricType R)
    (a : X) (V : X -> set X -> Prop) (A : set X) :
  is_measure_derivation_context (point_mass R a) V -> A a ->
  measure_density_one_points (point_mass R a) V A a /\
  measure_density_complement_zero_points (point_mass R a) V A a.
Proof.
move=> hc ha.
have hP := @density_one_points_conclusions R X (point_mass R a) V A hc.
have hQ := @density_complement_zero_points_conclusions R X (point_mass R a) V A hc.
split.
- apply: contrapT=> hn.
  have hmass := @point_mass_in R X a (A `\` measure_density_one_points (point_mass R a) V A) (conj ha hn).
  by move: hP.2.1; rewrite hmass=> /eqP; rewrite eqe oner_eq0.
- apply: contrapT=> hn.
  have hz := hQ.2.2.2.1 (@point_mass_every_set_measurable R X a A).
  have hmass := @point_mass_in R X a (A `\` measure_density_complement_zero_points (point_mass R a) V A) (conj ha hn).
  by move: hz; rewrite hmass=> /eqP; rewrite eqe oner_eq0.
Qed.

(** Source for [empty_target_borel_hull_null]: empty-target regression for
    the hull choice in Federer 2.9.11, p. 158 The Borel hull of the empty
    set has zero mass even when the total reference mass is infinite. No
    ambient point or positive mass is assumed. *)
Example empty_target_borel_hull_null (R : realType) (X : metricType R)
    (phi : set X -> \bar R) :
  is_derivation_measure phi -> exists B, borel_set B /\ is_measure_hull phi set0 B /\ phi B=0.
Proof.
move=> hphi; have hm := derivation_measure_law hphi.
have [B [hBb hB]] := @derivation_measure_borel_hull R X phi set0 hphi.
exists B; split=> //; split=> //.
have he := @measure_hull_equal_measure R X phi hm set0 B hB.
by rewrite -(he) (measure_empty hm).
Qed.


(** Source for [zero_reference_no_approximate_limit]: partial-domain
    regression for Federer 2.9.12, pp. 158–159. A zero
    reference has no actual zero-density graph, so no function
    has an approximate limit at any point, although almost-
    everywhere assertions for that reference remain vacuous. *)
Example zero_reference_no_approximate_limit (R : realType) (X : metricType R)
    (Y : topologicalType) (V : X -> set X -> Prop) (f : partial_function X Y) x y :
  ~ is_measure_approximate_limit (fun _ : set X => (0 : \bar R)) V f x y.
Proof.
move=> hl; have hd := approximate_limit_domain_density hl.
apply: (@null_reference_derivate_nowhere_defined R X
  (measure_restrict (fun _ => 0) (~` partial_function_domain f)) V x).
by exists 0.
Qed.

(** Source for [empty_domain_approximate_limits_diverge]: erratum
    regression for Federer 2.9.12, p. 159, corrected in
    erratum p. 3, book p. 159 line 7. For an empty-domain
    function every corrected exceptional set is X; the upper
    and lower approximate limits are opposite infinities. *)
Example empty_domain_approximate_limits_diverge (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) x :
  is_measure_derivation_context phi V ->
  measure_approximate_upper_limit phi V (@partial_function_empty X (\bar R)) x = +oo /\
  measure_approximate_lower_limit phi V (@partial_function_empty X (\bar R)) x = -oo.
Proof. exact: empty_function_approximate_order_limits. Qed.

(** Source for [atom_approximate_continuity]: positive-atom regression for
    Federer 2.9.12, pp. 158–159 Every partial function defined at the atom
    is approximately continuous there, with its actual value, regardless of
    its other domain points. *)
Example atom_approximate_continuity (R : realType) (X : metricType R)
    (Y : topologicalType) (a : X) (V : X -> set X -> Prop)
    (f : partial_function X Y) y :
  is_measure_derivation_context (point_mass R a) V -> partial_function_graph f a y ->
  is_measure_approximately_continuous_at (point_mass R a) V f a.
Proof.
move=> hc hy; exists y; split=> // W hW.
have hin : partial_function_preimage f W a.
  exists y; split=> //; exact: nbhs_singleton hW.
exact: (atom_density_point_conditions hc hin).2.
Qed.


(** Source for [zero_reference_partial_function_measurable]:
    null-reference regression for Federer 2.9.13, p. 159.
    Every partial function is measurable and approximately
    continuous almost everywhere for a zero reference, despite
    having no actual approximate limit at any point. The target
    need not be metric or inhabited for the converse argument. *)
Example zero_reference_partial_function_measurable (R : realType) (X : metricType R)
    (Y : topologicalType) (V : X -> set X -> Prop) (f : partial_function X Y) :
  is_measure_derivation_context (fun _ : set X => (0 : \bar R)) V ->
  is_measure_measurable_function (fun _ : set X => (0 : \bar R)) f /\
  measure_almost_everywhere (fun _ : set X => (0 : \bar R))
    [set x | is_measure_approximately_continuous_at (fun _ => 0) V f x].
Proof.
move=> hc; have ha : measure_almost_everywhere (fun _ : set X => (0 : \bar R))
    [set x | is_measure_approximately_continuous_at (fun _ => 0) V f x] by [].
split=> //; exact: almost_approximate_continuity_measurable hc ha.
Qed.

(** Source for [empty_function_measurable_only_null_space]:
    empty-domain regression for Federer 2.9.13, p. 159.
    The conull-domain requirement permits the empty function
    exactly when the whole reference space is null; the
    converse approximate-continuity argument handles this case. *)
Example empty_function_measurable_only_null_space (R : realType) (X : metricType R)
    (Y : topologicalType) (phi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V ->
  (is_measure_measurable_function phi (@partial_function_empty X Y) <-> phi setT=0).
Proof.
move=> hc; have hm := derivation_measure_law (derivation_context_measure hc); split.
- move=> hf; have hd := measurable_function_domain hf.
  by rewrite /measure_almost_everywhere partial_function_empty_domain setC0 in hd.
- move=> hz; apply: (@almost_approximate_continuity_measurable R X Y phi V
    (@partial_function_empty X Y) hc).
  apply: (@measure_null_subset R X phi hm _ setT _ hz).
  by move=> x _.
Qed.

(** Source for [atom_partial_function_measurable]: positive-reference
    regression for Federer 2.9.13, p. 159. Any partial
    function defined at a unit atom is measurable for that
    point mass. Approximate continuity at the atom proves this
    via the converse, without any condition on the other values
    or topological separability of the target. *)
Example atom_partial_function_measurable (R : realType) (X : metricType R)
    (Y : topologicalType) (a : X) (V : X -> set X -> Prop)
    (f : partial_function X Y) y :
  is_measure_derivation_context (point_mass R a) V -> partial_function_graph f a y ->
  is_measure_measurable_function (point_mass R a) f.
Proof.
move=> hc hy; apply: (@almost_approximate_continuity_measurable R X Y (point_mass R a) V f hc).
apply: point_mass_out=> hn.
exact: hn (atom_approximate_continuity hc hy).
Qed.


(** Source for [empty_radius_ball_comparison_empty]: empty-radius
    regression for Federer 2.9.14, p. 159. An empty
    allowed open radius set gives an empty comparison locus,
    irrespective of either measure's total mass. *)
Example empty_radius_ball_comparison_empty (R : realType) (X : metricType R)
    (alpha beta : set X -> \bar R) :
  ball_measure_comparison_points alpha beta set0=set0.
Proof.
apply/seteqP; split=> x; first by move=> [r [[] _]].
by move=> [].
Qed.

(** Source for [equal_measures_ball_comparison_empty]: strictness
    regression for Federer 2.9.14, p. 159. Equal
    measures never satisfy the strict ball inequality, even
    if some common ball values are infinite. *)
Example equal_measures_ball_comparison_empty (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (J : set (real_line_metric R)) :
  ball_measure_comparison_points mu mu J=set0.
Proof.
apply/seteqP; split=> x; last by move=> [].
by move=> [r [_ h]]; move: h; rewrite ltxx.
Qed.

(** Source for [infinite_numerator_ball_comparison_full]: infinite-
    numerator regression for Federer 2.9.14, p. 159.
    The measure infinite on every nonempty set need not belong
    to M: every positive closed ball has infinite numerator
    and finite beta mass. One allowed positive radius therefore
    makes the comparison locus all of X. *)
Example infinite_numerator_ball_comparison_full (R : realType) (X : metricType R)
    (beta : set X -> \bar R) (J : set (real_line_metric R)) :
  is_derivation_measure beta -> (exists r : R, J r /\ (0<r)%R) ->
  ball_measure_comparison_points (@infinite_discrete_measure R X) beta J=setT.
Proof.
move=> hbeta [r [hJr hr]]; apply/seteqP; split=> x; first by move=> _.
move=> _; exists r; split=> //.
have hx : metric_closed_ball x r x by rewrite /metric_closed_ball /= mdistxx; exact: ltW hr.
rewrite (@infinite_discrete_measure_nonempty R X (metric_closed_ball x r) (ex_intro _ x hx)).
exact (@derivation_measure_bounded_finite R X beta hbeta _
  (@covering_closed_ball_bounded R X x r (ltW hr))).
Qed.


(** Source for [null_reference_centered_exceptional_sets]: partial-
    division regression for W and P in Federer 2.9.15,
    p. 160. With a zero reference P is the whole space
    and W is empty: small undefined 0/0 quotients do not
    produce an infinite ordinary radius density. *)
Example null_reference_centered_exceptional_sets (R : realType) (X : metricType R)
    (psi : set X -> \bar R) :
  measure_null_ball_points (fun _ : set X => (0 : \bar R))=setT /\
  measure_infinite_centered_density_points psi (fun _ => 0)=set0.
Proof.
have hP : measure_null_ball_points (fun _ : set X => (0 : \bar R))=setT.
  apply/seteqP; split=> x; first by move=> _.
  move=> _; exists 1%R; by split; first exact: ltr01.
split=> //; apply/seteqP; split=> x; last by move=> [].
move=> [hn _]; exfalso; apply: hn; by rewrite hP.
Qed.

(** Source for [self_reference_infinite_centered_density_empty]:
    self-reference regression for W in Federer 2.9.15,
    p. 160. Every actual positive finite self ratio is
    one. A null denominator supplies no ordinary limit,
    so no point has infinite self density. *)
Example self_reference_infinite_centered_density_empty (R : realType) (X : metricType R)
    (phi : set X -> \bar R) :
  is_derivation_measure phi -> measure_infinite_centered_density_points phi phi=set0.
Proof.
move=> hphi; apply/seteqP; split=> x; last by move=> [].
move=> [hn hl]; exfalso.
have [d [hd hb]] := (positive_right_infinite_real_thresholds _).1 hl 2%R.
pose r := (d/2)%R.
have hr : (0<r)%R by rewrite /r divr_gt0 // ltr0n.
have hrd : (r<d)%R.
  by rewrite /r ltr_pdivrMr ?ltr0n // -{1}(mulr1 d) ltr_pM2l // ltr1n.
have hm := derivation_measure_law hphi.
have hp := @outside_null_ball_points_positive R X phi x r hm hn hr.
have hf : phi (metric_closed_ball x r) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  exact (@derivation_measure_bounded_finite R X phi hphi _
    (@covering_closed_ball_bounded R X x r (ltW hr))).
have hnz : phi (metric_closed_ball x r)!=0 by rewrite (gt_eqF hp).
have he := @divee R (phi (metric_closed_ball x r)) hf hnz.
by have := hb r hr hrd; rewrite he lte_fin ltrn1.
Qed.

(** Source for [atom_geometric_restriction_preserves_atom]: positive-
    reference regression for the assembled identity in Federer
    2.9.15, pp. 160–161. At a unit atom the exceptional
    union is absent, and the restriction formula preserves the
    numerator mass of that singleton. The numerator may have
    arbitrary finite or infinite total mass. *)
Example atom_geometric_restriction_preserves_atom (R : realType) (X : metricType R)
    (a : X) (psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context (point_mass R a) V -> is_derivation_measure psi ->
  is_centered_density_geometry (point_mass R a) ->
  measure_continuous_part psi (point_mass R a) [set a]=psi [set a].
Proof.
move=> hc hpsi hgeo.
pose E := measure_infinite_centered_density_points psi (point_mass R a) `|`
  measure_null_ball_points (point_mass R a).
have hnull := @centered_density_exceptional_union_null R X (point_mass R a) psi V hc hpsi hgeo.
have hn : ~ E a.
  move=> ha; have hone := @point_mass_in R X a E ha.
  by move: hnull; rewrite hone=> /eqP; rewrite eqe oner_eq0.
have hid := (@federer_2_9_15 R X (point_mass R a) psi V hc hpsi hgeo).2.2.
rewrite hid /measure_restrict.
change (psi ((~` E) `&` [set a])=psi [set a]).
have he : (~` E) `&` [set a]=[set a].
  apply/seteqP; split=> x; first by move=> [_ hx].
  by move=> ->; split.
by rewrite he.
Qed.

(** Source for [euclidean_zero_dimensional_noncentered_vitali]:
    dimension-zero regression for the supporting ball criterion
    in Federer 2.9.16, p. 161. The all-ball Vitali
    assertion includes the one-point space; the line counterexample
    itself requires at least two distinct coordinate directions. *)
Example euclidean_zero_dimensional_noncentered_vitali (R : realType) :
  is_vitali_relation (@euclidean_lebesgue_measure R 0)
    (@noncentered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R 0)]).
Proof. exact: euclidean_noncentered_balls_vitali. Qed.

(** Source for [euclidean_plane_noncentered_derivation_failure]:
    explicit plane regression for the counterexample in Federer
    2.9.16, p. 161. With any translate of the
    horizontal line, the all-ball relation is Lebesgue Vitali,
    both exceptional loci are empty, and the continuous part
    still differs from the numerator. *)
Example euclidean_plane_noncentered_derivation_failure (R : realType)
    (v : inner_metric_space (@euclidean_inner_productP R 2)) :
  let phi := @euclidean_lebesgue_measure R 2 in
  let psi := euclidean_affine_line_measure ord0 v in
  let V := @noncentered_closed_ball_relation R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)] in
  is_measure_derivation_context phi V /\ is_derivation_measure psi /\
  (forall x, covering_lower_limit V (measure_ratio_function psi phi) x=0) /\
  measure_infinite_derivate_points psi phi V=set0 /\
  measure_null_ball_points phi=set0 /\ measure_continuous_part psi phi<>psi.
Proof.
move=> phi psi V.
have [hc [hpsi [hl [hW [hP [_ [_ hneq]]]]]]] :=
  @federer_2_9_16 R 2 ord0 ord_max v (ltac:(by [])).
by split=> //; split=> //; split=> //; split=> //; split.
Qed.

(** Source for [euclidean_one_dimensional_line_segment_mass]:
    dimension-one calibration for the line measure supporting
    Federer 2.9.16, p. 161. A unit parameter
    segment has unit line measure under arbitrary translation;
    the ambient-nullity counterexample needs a second coordinate. *)
Example euclidean_one_dimensional_line_segment_mass (R : realType)
    (v : inner_metric_space (@euclidean_inner_productP R 1)) :
  euclidean_affine_line_measure ord0 v
    (euclidean_coordinate_line ord0 v @` `[0%R,1%R])= 1.
Proof.
rewrite euclidean_affine_line_measure_preimage.
have hi := can_inj (@euclidean_coordinate_line_retraction R 1 ord0 v).
have he : (euclidean_coordinate_line ord0 v) @^-1`
    (euclidean_coordinate_line ord0 v @` `[0%R,1%R])=`[0%R,1%R].
  apply/seteqP; split=> t /=.
  - move=> [s hs heq]; have hst := hi _ _ heq.
    by rewrite -hst.
  - by move=> ht; exists t.
have hab : (0<=1 :> R)%R := ler01.
by rewrite he (@lebesgue_scalar_segment R 0%R 1%R hab) subr0.
Qed.

(** Source for [null_reference_strict_growth_impossible]: strict-
    growth boundary regression for Federer 2.9.17, p. 162.
    On an inhabited space the zero reference measure cannot
    satisfy the printed strict fivefold inequality at any
    positive radius cutoff, regardless of its finite coefficient. *)
Example null_reference_strict_growth_impossible (R : realType) (X : metricType R)
    (x : X) (lambda mu : R) : (0<mu)%R ->
  ~ has_uniform_fivefold_ball_growth (fun _ : set X => (0 : \bar R)) setT mu lambda.
Proof.
move=> hmu hg.
have hr : (0<mu/2)%R by rewrite divr_gt0 // ltr0n.
have hrm : (mu/2<mu)%R by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
have h := hg x I (mu/2)%R hr hrm.
by rewrite mule0 ltxx in h.
Qed.

(** Source for [empty_restriction_upper_ratio_zero]: zero-
    numerator regression for Federer 2.9.17, p. 162.
    Restricting any class-M reference to the empty set gives
    zero upper radial ratio at every point having positive
    ball masses; actual quotient domains remain explicit. *)
Example empty_restriction_upper_ratio_zero (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (x : X) :
  is_derivation_measure phi -> ~ measure_null_ball_points phi x ->
  centered_ball_ratio_upper_limit (measure_restrict phi set0) phi x=0.
Proof.
move=> hphi hn; have hm := derivation_measure_law hphi.
apply: (@centered_ball_ratio_upper_limit_zero R X (measure_restrict phi set0) phi x
  hphi (@measure_restrict_is_measure R X phi hm set0) hn)=> e he.
exists 1%R; split; first exact: ltr01.
move=> r hr _.
by rewrite /measure_restrict set0I (measure_empty hm) mul0e lte_fin.
Qed.

(** Source for [positive_self_upper_ratio_not_dichotomous]:
    hypothesis regression for Federer 2.9.17, p. 162.
    The upper self-ratio is one wherever all balls have positive
    mass, so the zero-or-infinite conclusion cannot hold there
    after dropping the numerator-null target condition. *)
Example positive_self_upper_ratio_not_dichotomous (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (x : X) :
  is_derivation_measure phi -> ~ measure_null_ball_points phi x ->
  ~ has_zero_or_infinite_upper_ball_ratio phi phi x.
Proof.
move=> hphi hn; have hm := derivation_measure_law hphi.
have hgraph (r : R) (hr : (0<r)%R) :
    partial_function_graph (measure_ratio_function phi phi) (metric_closed_ball x r) 1.
  have hp := @outside_null_ball_points_positive R X phi x r hm hn hr.
  have hf : phi (metric_closed_ball x r) \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm _)).
    exact (@derivation_measure_bounded_finite R X phi hphi _
      (@covering_closed_ball_bounded R X x r (ltW hr))).
  have hq := @measure_ratio_positive_finite_denominator R X phi phi (metric_closed_ball x r) hp hf.
  by rewrite divee ?(gt_eqF hp) // in hq.
have hu : centered_ball_ratio_upper_limit phi phi x= 1.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - have hlev : centered_ball_ratio_upper_limit phi phi x<=
        extended_real_sup (centered_ball_ratio_values phi phi x 1%R).
      apply: extended_real_inf_lower; exists 1%R; split=> //; exact: ltr01.
    apply: le_trans hlev _; apply: extended_real_sup_least=> y [r [hr [_ hy]]].
    have hey := partial_function_single_valued hy (hgraph r hr).
    by rewrite hey.
  - apply: extended_real_inf_greatest=> b [d [hd ->]].
    have hr : (0<d/2)%R by rewrite divr_gt0 // ltr0n.
    have hrd : (d/2<d)%R by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
    apply: extended_real_sup_upper; by exists (d/2)%R; split=> //; split=> //; exact: hgraph.
move=> [hz|hinf].
- by move: hz; rewrite hu=> /eqP; rewrite eqe oner_eq0.
- by move: hinf; rewrite hu=> /eqP; rewrite -leye_eq leNgt ltry.
Qed.

(** Source for [weighted_hit_empty_regression]: empty-set
    boundary check for the correct measure formula in Federer
    2.9.18(1), p. 163. Arbitrary coefficient signs
    do not change the zero value on the empty set. *)
Example weighted_hit_empty_regression (R : realType) (X : choiceType)
    (c : nat -> R) (S : nat -> set X) : weighted_hit_measure c S set0=0.
Proof. exact: weighted_hit_measure_empty. Qed.

(** Source for [erratum_miss_empty_centers_regression]: local
    correction regression for erratum p. 3, book p. 163
    line 11, concerning Federer 2.9.18(1). Even an
    empty carrier and empty center sets do not rescue the
    printed empty-intersection replacement when coefficients are one.
    The book's nonempty-intersection formula is retained. *)
Example erratum_miss_empty_centers_regression (R : realType) :
  ~is_measure (@weighted_miss_capacity R [the choiceType of 'I_0]
    (fun _ => 1%R) (fun _ => set0)).
Proof. exact: weighted_miss_capacity_not_measure (ltr01). Qed.

(** Source for [euclidean_line_radius_zero_regression]:
    degenerate-radius check for the line reference supporting
    Federer 2.9.18(2), p. 163. Radius zero has
    zero length; the printed quotient assertions require
    positive radius and do not totalise division by zero. *)
Example euclidean_line_radius_zero_regression (R : realType)
    (v : inner_metric_space (@euclidean_inner_productP R 1)) (s : R) :
  euclidean_affine_line_measure ord0 v
    (metric_closed_ball (euclidean_coordinate_line ord0 v s) 0%R)=0.
Proof.
by rewrite (@euclidean_affine_line_centered_ball_measure R 1 ord0 v s 0%R (lexx _)) mulr0.
Qed.

(** Source for [euclidean_plane_projected_ratio_regression]:
    the actual plane example in Federer 2.9.18(2), p. 163.
    At every point of a translated horizontal line the
    off-line projected/reference ball quotient is one, and its
    upper radial limit is one. Positive radii remain explicit. *)
Example euclidean_plane_projected_ratio_regression (R : realType)
    (v : inner_metric_space (@euclidean_inner_productP R 2)) (s r : R) : (0<r)%R ->
  partial_function_graph
    (measure_ratio_function (off_line_projection_measure ord0 v) (euclidean_affine_line_measure ord0 v))
    (metric_closed_ball (euclidean_coordinate_line ord0 v s) r) 1 /\
  centered_ball_ratio_upper_limit (off_line_projection_measure ord0 v)
    (euclidean_affine_line_measure ord0 v) (euclidean_coordinate_line ord0 v s)= 1.
Proof.
move=> hr; split.
- exact (@line_projection_centered_ball_ratio R 2 ord0 ord_max v s r (ltac:(by [])) hr).
- exact (@line_projection_upper_ball_ratio_one R 2 ord0 ord_max v s (ltac:(by []))).
Qed.

(** Source for [euclidean_zero_dimensional_directional_regression]:
    dimension-zero boundary check for directional limitation
    supporting Federer 2.9.18(2), p. 163, via the
    finite-dimensional example of 2.8.9, p. 146. The
    singleton zero-dimensional space is included by the general
    norm result, although the sharpness example needs two directions. *)
Example euclidean_zero_dimensional_directional_regression (R : realType) (eta : R) :
  (0<eta<=1/3)%R -> exists zeta : nat,
    @is_directionally_limited_at R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R 0)] setT +oo eta zeta.
Proof. exact: euclidean_directional_limitation. Qed.

(** Source for [constant_curve_derivative_zero_regression]:
    constant-function boundary case of Federer 2.9.19, p. 163. Every nonzero
    difference quotient is zero on both sides of the base point. *)
Example constant_curve_derivative_zero_regression (R : realType) (c x : R) :
  has_real_curve_derivative (fun _ : R => c) x 0%R.
Proof.
move=> e he; exists 1%R; split; first exact: ltr01.
by move=> h _; rewrite subrr mul0r subrr normr0.
Qed.

(** Source for [negative_affine_curve_derivative_regression]: signed
    derivative check for Federer 2.9.19, p. 163. The curve g(t)=-t has
    derivative -1 at every real point; positive and negative increments are
    both included. *)
Example negative_affine_curve_derivative_regression (R : realType) (x : R) :
  has_real_curve_derivative (fun t : R => (-t)%R) x (-1)%R.
Proof.
move=> e he; exists 1%R; split; first exact: ltr01.
move=> h /andP [hh _].
have hn : h!=0%R by move: hh; rewrite normr_gt0.
have hq : (((-(x+h))-(-x))/h)%R= (-1)%R by field; rewrite (negbTE hn).
by rewrite hq subrr normr0.
Qed.

(** Source for [zero_length_derivative_integral_regression]:
    degenerate-segment extension of the integral bound in Federer 2.9.19,
    pp. 164–165 Even if the derivative is undefined at the endpoint, its
    partial absolute-derivative integral on that singleton exists and equals
    zero. *)
Example zero_length_derivative_integral_regression (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (a : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,a]
    (real_curve_absolute_derivative_integrand g) 0.
Proof.
move=> hg hp.
have [I [hI0 [hInt hBound]]] := @real_bv_absolute_derivative_interval_integral R
  g psip psim a a hg hp (lexx _).
rewrite curve_variation_self lee_fin in hBound.
have hI : I=0%R by apply/le_anti/andP; split.
by rewrite hI in hInt.
Qed.

Local Open Scope ring_scope.

(** Source for [constant_absolute_continuity_regression]: zero-increment
    boundary case of Federer 2.9.20(3), p. 165 Constant curves satisfy the
    actual finite-family law without derivative hypotheses. *)
Example constant_absolute_continuity_regression (R : realType) (c a b : R) :
  is_absolutely_continuous_real_curve (fun _ : R => c) a b.
Proof. exact: constant_real_curve_absolutely_continuous. Qed.

(** Source for [empty_absolute_continuity_family_regression]: empty
    finite-family boundary of Federer 2.9.20(3), p. 165 Both sums are zero,
    so allowing an empty family adds no extra constraint. *)
Example empty_absolute_continuity_family_regression (R : realType) (g : R -> R)
    (a b : R) : is_ordered_real_interval_family a b [::] /\
  real_interval_family_length (R:=R) [::]=0 /\
  real_interval_family_increment_sum g [::]=0.
Proof. by split=> //; split; rewrite /real_interval_family_length /real_interval_family_increment_sum big_nil. Qed.

(** Source for [degenerate_absolute_continuity_regression]: degenerate-
    segment extension of the definition in Federer 2.9.20(3), p. 165 The
    epsilon law alone is vacuous on [a,a], since no strictly positive
    eligible cell can lie in it. *)
Example degenerate_absolute_continuity_regression (R : realType) (g : R -> R) (a : R) :
  is_absolutely_continuous_real_curve g a a.
Proof.
move=> e he; exists 1; split; first exact: ltr01.
move=> s hs hlen; case: s hs hlen=> [|[u v] s] hs hlen.
- rewrite /real_interval_family_increment_sum big_nil; exact: ltW he.
- have [hau [huv [hva _]]] := hs; exfalso; lra.
Qed.

(** Source for [one_sided_endpoint_absolute_continuity_regression]: relative
    endpoint-continuity convention in Federer 2.9.20(4), pp. 165–166 This
    curve is constant on [0,1] and jumps just outside its left endpoint. *)
Example one_sided_endpoint_absolute_continuity_regression (R : realType) :
  is_absolutely_continuous_real_curve
    (fun x : R => if x<0 then 1 else 0) 0 1.
Proof.
move=> e he; exists 1; split; first exact: ltr01.
move=> s hs hlen; rewrite /real_interval_family_increment_sum big_seq.
have hsum : \sum_(uv <- s | uv \in s)
    `|(if uv.2<0 then 1 else 0)-(if uv.1<0 then 1 else 0)|=(0 : R).
  apply: big1=> uv huv; case: uv huv=> u v huv.
  have [h0u [huv' hv1]] := ordered_real_interval_family_cell_bounds hs huv.
  have h0v : 0<=v := le_trans h0u (ltW huv').
  have hu : (u<0)=false by apply/negbTE; rewrite -leNgt.
  have hv : (v<0)=false by apply/negbTE; rewrite -leNgt.
  by rewrite /= hu hv subrr normr0.
rewrite hsum; exact: ltW he.
Qed.

(** Source for [noncompact_constant_stieltjes_density_regression]:
    continuous-integrand extension of the first formula in Federer 2.9.21,
    p. 166 The constant factor one is admitted by the proved compact cutoff
    reduction, without a false global compact-support claim. *)
Example noncompact_constant_stieltjes_density_regression (R : realType) (g : R -> R)
    (a b : R) : curve_locally_finite_variation (g : R -> real_line_metric R) ->
  a<b -> is_absolutely_continuous_real_curve g a b ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (weighted_real_curve_derivative_integrand (fun _ => 1) g)
    (StieltjesIntegral.stieltjes_integral g (fun _ => 1) a b)%:E.
Proof.
move=> hg hab hAC.
apply: absolutely_continuous_stieltjes_integral hg hab hAC _.
by move=> x; exact: cvg_cst.
Qed.

(** Source for [flat_monotone_substitution_zero_regression]: flat-image case
    of the second formula in Federer 2.9.21, p. 166. The book's increasing
    convention is weak. A constant change of variable has both actual
    integrals equal to zero, including its degenerate image interval. *)
Example flat_monotone_substitution_zero_regression (R : realType) (f : R -> R)
    (c a b : R) : a<b ->
  continuous (f : real_line_metric R -> real_line_metric R) ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (weighted_real_curve_derivative_integrand (fun _ => f c) (fun _ => c)) 0%E /\
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[c,c]
    (SummableRealFunctionUP.real_total_integrand f) 0%E.
Proof.
move=> hab hf.
have hg : curve_locally_finite_variation ((fun _ : R => c) : R -> real_line_metric R).
  apply: StieltjesMonotone.monotone_locally_finite_variation; by move=> x y hxy.
have hmono : forall x y : R, x<=y -> c<=c by [].
have [I [hL hR]] := @absolutely_continuous_monotone_substitution R (fun _ => c) f a b
  hg hab (constant_real_curve_absolutely_continuous c a b) hmono hf.
have hNull : lebesgue_scalar_measure `[c,c]=0%E.
  by rewrite lebesgue_scalar_segment ?lexx // subrr.
have hZero := @null_target_subset_integral R (real_line_metric R) (@lebesgue_scalar_measure R)
  (SummableRealFunctionUP.real_total_integrand f) `[c,c] (lebesgue_scalar_is_measure R) hNull.
have hI0 : I=0 by have := MeasureIntegralUniqueness.measure_integral_unique hR hZero; case.
split; [by rewrite hI0 in hL|exact hZero].
Qed.

(** Source for [zero_factor_preserves_missing_derivative_regression]:
    partial-domain convention for the products in Federer 2.9.21, p. 166,
    with 2.4.10, p. 85 A zero multiplier does not supply a missing actual
    derivative value; common domains are still required. *)
Example zero_factor_preserves_missing_derivative_regression (R : realType)
    (g : R -> R) (x : R) :
  ~partial_function_domain (real_curve_derivative g) x ->
  ~partial_function_domain (weighted_real_curve_derivative_integrand (fun _ => 0) g) x.
Proof.
move=> hMissing [y hy]; have [v [hv _]] := (weighted_real_derivative_integrand_graph _ _ x y).1 hy.
apply: hMissing; exists v; exact: (real_curve_derivative_graph g x v).2 hv.
Qed.

Section NormedDerivativeRegressions.
Local Open Scope ring_scope.

(** Source for [normed_constant_derivative_regression]: constant
    curve boundary case of Federer 2.9.22, p. 167. This
    checks the actual partial norm-derivative graph, in arbitrary
    dimension and including a zero-dimensional target. *)
Example normed_constant_derivative_regression (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (c : E) (x : R) :
  partial_function_graph (normed_curve_derivative hN (fun _ => c)) x 0%R.
Proof. exact: constant_normed_curve_derivative hN c x. Qed.

(** Source for [normed_affine_derivative_regression]: affine
    curve regression for the norm quotient in Federer 2.9.22,
    p. 167. A translated line has its prescribed vector
    velocity at every point, using only the abstract norm laws. *)
Example normed_affine_derivative_regression (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (v c : E) (x : R) :
  has_normed_curve_derivative N (fun t => (t *: v+c)%R) x v.
Proof.
move=> e he; exists 1%R; split; first exact: ltr01.
move=> h /andP [hh _].
have hn : h!=0%R by move: hh; rewrite normr_gt0.
have hid : ((x+h) *: v+c)-(x *: v+c)=(h *: v)%R.
  by rewrite scalerDl addrAC [X in X - _]addrC opprD !addrA addrK subrK.
by rewrite hid scalerA mulVf // scale1r subrr (real_seminorm_zero hN.1).
Qed.

(** Source for [scalar_normed_derivative_agreement_regression]:
    compatibility of the norm derivative in Federer 2.9.22,
    p. 167, with the real derivative in 2.9.19, p. 163.
    The actual candidate-value conditions agree pointwise. *)
Example scalar_normed_derivative_agreement_regression (R : realType)
    (g : R -> R) (x v : R) :
  @has_normed_curve_derivative R R^o (fun y => `|y|%R) g x v <->
  has_real_curve_derivative g x v.
Proof. exact: scalar_normed_curve_derivative. Qed.

End NormedDerivativeRegressions.

Section VectorPrimitiveRegressions.
Local Open Scope ring_scope.

(** Source for [zero_mass_constant_vector_integral_regression]:
    zero-mass boundary case of the constant term in Federer
    2.9.22, p. 168, norm-error display. Every constant
    vector has actual vector integral zero for a measure
    of total mass zero, without requiring that vector to vanish. *)
Example zero_mass_constant_vector_integral_regression (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : E) :
  mu setT=0%:E -> is_measure_vector_integral mu
    (partial_function_total (fun _ : X => (c : real_norm_metric_space hN))) 0.
Proof.
move=> hm0.
have hi := @finite_measure_vector_constant_integral R X E N hN mu hm 0 c hm0.
by rewrite scale0r in hi.
Qed.

(** Source for [affine_vector_primitive_derivative_ae_regression]:
    regression for the vector primitive and Lebesgue-point
    implication in Federer 2.9.22, p. 168. The constant
    field c has interval integral (b-a)c, hence the primitive
    t maps to t c has its actual norm derivative c almost
    everywhere. This tests finite-interval mass and vector
    integral normalisation in an arbitrary separable normed target. *)
Example affine_vector_primitive_derivative_ae_regression (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (C : set (real_norm_metric_space hN)) (c : E) :
  countable C -> dense C -> measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | has_normed_curve_derivative N (fun t => t *: c) x c].
Proof.
move=> hCc hCd.
have hm := lebesgue_scalar_is_measure R.
have hv := @measurable_total_constant R (real_line_metric R)
  [the topologicalType of real_norm_metric_space hN] (@lebesgue_scalar_measure R) hm c.
have hprimitive a b : a<b -> is_measure_vector_integral
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)))
    (partial_function_total (fun _ : real_line_metric R => (c : real_norm_metric_space hN)))
    (b *: c-a *: c).
  move=> hab.
  have hmA := measure_restrict_is_measure hm (`[a,b] : set (real_line_metric R)).
  have hmass : measure_restrict (@lebesgue_scalar_measure R)
      (`[a,b] : set (real_line_metric R)) setT=(b-a)%:E.
    rewrite /measure_restrict setIT; exact: lebesgue_scalar_segment (ltW hab).
  have hi := @finite_measure_vector_constant_integral R (real_line_metric R) E N hN
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R))) hmA
    (b-a) c hmass.
  by rewrite scalerBl in hi.
exact (@bounded_vector_primitive_derivative_ae R E N hN C
  (fun t => t *: c) (fun _ => c) (N c) hCc hCd hv (fun _ => lexx _) hprimitive).
Qed.

End VectorPrimitiveRegressions.

Section ReflexiveSubspaceRegressions.
Local Open Scope ring_scope.

(** Source for [zero_bound_subspace_extension_regression]: zero-bound
    boundary case of the Hahn–Banach subspace extension supporting
    Federer 2.9.22, p. 167, through 2.4.12, p. 86.
    The extension of a zero-bounded functional vanishes on the whole
    ambient space; no division by the bound is permitted. *)
Example zero_bound_subspace_extension_regression (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (Z : subspace E)
    (f : {linear subspace_space Z -> R^o}) :
  (forall z, `|f z|<=0) -> exists a : {linear E -> R^o},
    (forall z, a (subspace_val z)=f z) /\ (forall y, a y=0).
Proof.
move=> hf.
have hb z : `|f z|<=0 * subspace_norm N Z z by rewrite mul0r; exact: hf.
have [a [ha [hbound _]]] := @bounded_subspace_functional_extension R E N hN Z f 0 (lexx _) hb.
exists a; split=> // y.
have h : `|a y|<=0 by move: (hbound y); rewrite mul0r.
have he : `|a y|=0 by apply: le_anti; rewrite h normr_ge0.
by move: he=> /eqP; rewrite normr_eq0=> /eqP.
Qed.

(** Source for [subspace_affine_derivative_inclusion_regression]:
    isometric subspace transport in Federer 2.9.22, p. 167.
    A translated line in the subspace has the same actual norm
    derivative after ambient inclusion, including the zero subspace. *)
Example subspace_affine_derivative_inclusion_regression (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (Z : subspace E)
    (v c : subspace_space Z) (x : R) :
  has_normed_curve_derivative N (fun t => subspace_val (t *: v+c)) x (subspace_val v).
Proof.
apply: (@subspace_norm_derivative_inclusion R E N hN Z).
exact (@normed_affine_derivative_regression R [the lmodType R of subspace_space Z]
  (subspace_norm N Z) (subspace_norm_laws hN Z) v c x).
Qed.

(** Source for [arbitrary_reflexive_constant_derivative_regression]:
    zero-Lipschitz boundary case of Federer 2.9.22, pp. 167–168.
    Apply the arbitrary-target theorem without a separability premise.
    The proved derivative norm bound forces the vector derivative to
    be zero, even when the ambient reflexive space is not separable. *)
Example arbitrary_reflexive_constant_derivative_regression (R : realType)
    (E D B : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (c : E) :
  is_bidual_embedding ed eb tau -> is_reflexive_embedding tau ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | has_normed_curve_derivative N (fun _ => c) x 0].
Proof.
move=> ht hr.
have hg (t u : R) : N (c-c)<=0 * `|t-u| by rewrite subrr (real_seminorm_zero hN.1) mul0r.
have hAE := @reflexive_lipschitz_derivative_ae R E D B N hN ed DN hD eb BN hB
  tau (fun _ => c) 0 ht hr (lexx _) hg.
apply: (@measure_almost_everywhere_mono R (real_line_metric R)
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) _ _ _ hAE)=> x [w [hw [hb _]]].
have hw0 : w=0.
  apply: hN.2; apply: le_anti; by rewrite hb (real_seminorm_nonnegative hN.1).
by rewrite hw0 in hw.
Qed.

End ReflexiveSubspaceRegressions.

Section ReflexiveBVRegressions.
Local Open Scope ring_scope.

(** Source for [constant_parameter_null_preimage_regression]: flat
    parameter case in Federer 2.9.22, p. 168. The inverse image
    of the null singleton {c} under the constant parameter is the
    whole real line. The proved conclusion is s'=0 almost everywhere,
    preserving the weighted statement even for this unbounded fibre. *)
Example constant_parameter_null_preimage_regression (R : realType) (c : R) :
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | has_real_curve_derivative (fun _ => c) x 0].
Proof.
have hs (a b : R) : a<=b -> c<=c by [].
have he := @monotone_null_preimage_zero_derivative R (fun _ => c) [set c]
  hs (lebesgue_scalar_singleton c).
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ he)=> x hx; exact: hx erefl.
Qed.

(** Source for [constant_parameter_diffuse_mass_regression]: weighted
    zero-image boundary case in Federer 2.9.22, p. 168. If a
    diffuse measure has segment mass bounded by the increments of
    a constant parameter, its entire mass vanishes. This checks that
    the interval-to-set step includes unbounded inverse images. *)
Example constant_parameter_diffuse_mass_regression (R : realType)
    (nu : set (real_line_metric R) -> \bar R) (hn : is_measure nu) (c : R) :
  (forall x, nu [set x]=0%E) ->
  (forall a b : R, measure_measurable nu ([set x : real_line_metric R | (a<=x<=b)%R])) ->
  (forall a b : R, a<=b -> (nu ([set x : real_line_metric R | (a<=x<=b)%R])<=0)%E) -> nu setT=0%E.
Proof.
move=> hz hmeas hseg.
have hs (a b : R) : a<=b -> c<=c by [].
have hb a b : a<=b -> (nu ([set x : real_line_metric R | (a<=x<=b)%R])<=(c-c)%:E)%E by rewrite subrr; exact: hseg.
have h := @monotone_atomless_measure_image_bound R (fun _ => c) nu hn hs hz hmeas hb [set c].
have he : (fun _ : real_line_metric R => c) @^-1` [set c]=setT.
  by apply/seteqP; split=> x.
rewrite he lebesgue_scalar_singleton in h.
apply: le_anti; by rewrite h (measure_nonnegative hn).
Qed.

(** Source for [reflexive_affine_bv_derivative_regression]: locally
    BV regression for Federer 2.9.22, pp. 167–168. The theorem
    applies to a line with arbitrary velocity without a global finite
    variation or separable ambient-space premise. Uniqueness identifies
    the resulting actual norm derivative with the prescribed velocity. *)
Example reflexive_affine_bv_derivative_regression (R : realType)
    (E D B : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (v : E) :
  is_complete_metric_space (real_norm_metric_space hN) ->
  is_bidual_embedding ed eb tau -> is_reflexive_embedding tau ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | has_normed_curve_derivative N (fun t => t *: v) x v].
Proof.
move=> hY ht hr.
have hLip (t u : R) : N (t *: v-u *: v)<=N v * `|t-u|.
  by rewrite -scalerBl (real_seminorm_scale hN.1) mulrC.
have hfin := @lipschitz_curve_locally_finite_variation R
  [the metricType R of real_norm_metric_space hN] (fun t => t *: v) (N v) hLip.
have hAE := @reflexive_bv_derivative_ae R E D B N hN ed DN hD eb BN hB tau
  (fun t => t *: v) hY ht hr hfin.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hAE)=> x [w [hw _]].
have hline := @normed_affine_derivative_regression R E N hN v 0 x.
have he : (fun t : R => t *: v+0)=(fun t : R => t *: v) by apply/funext=> t; rewrite addr0.
rewrite he in hline.
have hwv : w=v := punctured_norm_limit_unique hN hw hline.
by rewrite hwv in hw.
Qed.

End ReflexiveBVRegressions.

Section NormedVariationRegressions.
Local Open Scope ring_scope.

(** Source for [zero_lipschitz_postcomposition_variation_regression]:
    zero dual/Lipschitz bound supporting Federer 2.9.22, p. 167.
    A constant postcomposition has zero variation on every segment,
    including a singleton. This tests zero scaling of the finite
    variation representative without an undefined infinite product. *)
Example zero_lipschitz_postcomposition_variation_regression (R : realType)
    (X Y : metricType R) (g : R -> X) (c : Y) (a b : R) :
  curve_locally_finite_variation g -> a<=b ->
  curve_variation (fun _ : R => c) a b=0%E.
Proof.
move=> hg hab.
have hf (x y : X) : mdist c c<=0*mdist x y by rewrite mdistxx mul0r.
have hb := @metric_lipschitz_curve_variation_bound R X Y (fun _ => c) g 0 a b (lexx _) hf hg hab.
rewrite mul0r in hb.
apply: le_anti; by rewrite hb (curve_variation_nonnegative (fun _ : R => c) hab).
Qed.

(** Source for [degenerate_norm_derivative_integral_regression]:
    zero-width boundary case of the norm-integral estimate extended
    by Federer 2.9.22, pp. 167–168, from 2.9.19, p. 165.
    The actual partial norm derivative has subset integral zero on
    a singleton, even if the derivative is absent at that point. *)
Example degenerate_norm_derivative_integral_regression (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) (a : R) :
  curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,a]
    (normed_curve_norm_derivative_integrand hN g) 0%E.
Proof.
move=> hg he.
have [I [hI0 [hi hb]]] := @normed_bv_norm_derivative_interval_integral R E N hN g hg he a a (lexx _).
rewrite curve_variation_self lee_fin in hb.
have hI : I=0 by apply: le_anti; rewrite hI0 hb.
by rewrite hI in hi.
Qed.

(** Source for [zero_dual_induced_derivates_regression]: zero
    functional case of the induced measures in Federer 2.9.22,
    p. 167, extending 2.9.19(2), pp. 163–165. Both positive
    and negative induced derivates vanish almost everywhere, whichever
    scalar alternative is returned; actual partial graph values remain. *)
Example zero_dual_induced_derivates_regression (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g : R -> real_norm_metric_space hN)
    (psip psim : set R -> \bar R) :
  curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] ->
  is_induced_measure_pair (fun t => ed 0 (g t)) psip psim ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set x |
    partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
      psip (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x 0%E /\
    partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
      psim (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x 0%E].
Proof.
move=> hg he hp.
have hAE := @normed_bv_scalar_induced_derivates_ae R E D N hN ed DN hD g 0 psip psim hg he hp.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hAE)=> x [v [_ hAlt]].
have ha0 : ed (0 : D) v=0.
  change ((hom_as_linear ed) 0 v=0); by rewrite linear0 hom_zeroE.
rewrite ha0 oppr0 in hAlt.
by case: hAlt=> [[hP hM]|[hM hP]]; split.
Qed.

End NormedVariationRegressions.

Section NormedAbsoluteContinuityRegressions.
Local Open Scope ring_scope.

(** Source for [singleton_metric_absolute_continuity_regression]:
    strict-cell boundary of the finite-family condition extended by
    Federer 2.9.22, pp. 167–168, from 2.9.20(3), p. 165.
    On a singleton source interval every eligible family is empty,
    so the abstract law holds for any metric curve without regularity. *)
Example singleton_metric_absolute_continuity_regression (R : realType) (Y : metricType R)
    (g : R -> Y) (a : R) : is_absolutely_continuous_metric_curve g a a.
Proof.
move=> e he; exists 1; split; first exact: ltr01.
move=> [|[u v] s] hs hlen.
- rewrite /metric_interval_family_increment_sum big_nil; exact: ltW he.
- have [hau [huv [hva _]]] := hs.
  have haa : a<a := le_lt_trans hau (lt_le_trans huv hva).
  by rewrite ltxx in haa.
Qed.

(** Source for [zero_lipschitz_metric_absolute_continuity_regression]:
    zero functional/Lipschitz bound in the scalarisation supporting
    Federer 2.9.22, p. 167. The absolute-continuity transfer uses
    epsilon/(L+1), so it remains valid for L=0 without dividing by zero. *)
Example zero_lipschitz_metric_absolute_continuity_regression (R : realType)
    (X Y : metricType R) (g : R -> X) (c : Y) (a b : R) :
  is_absolutely_continuous_metric_curve g a b ->
  is_absolutely_continuous_metric_curve (fun _ : R => c) a b.
Proof.
move=> hg.
have hf (x y : X) : mdist c c<=0*mdist x y by rewrite mdistxx mul0r.
exact (@metric_absolute_continuity_lipschitz_postcomposition R X Y (fun _ => c) g 0 a b
  (lexx _) hf hg).
Qed.

(** Source for [singleton_bv_derivative_lone_regression]: zero-source
    case of the L1 requirement in Federer 2.9.22, pp. 167–168,
    extending 2.9.20(1), p. 165. The exact partial derivative
    belongs to full L1 on a singleton restriction, including the
    printed countable-measurability condition, even if absent there. *)
Example singleton_bv_derivative_lone_regression (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) (a : R) :
  is_complete_metric_space (real_norm_metric_space hN) -> curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] ->
  @is_measure_lp_function R (real_line_metric R) E N hN
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,a] : set (real_line_metric R))) 1
    (normed_curve_derivative hN g).
Proof.
move=> hY hg he; exact (@normed_bv_derivative_interval_lone R E N hN g hY hg he a a (lexx _)).
Qed.

(** Source for [singleton_vector_primitive_subsegment_regression]:
    zero-width actual vector subsegment integral in Federer 2.9.22,
    pp. 167–168, extending 2.9.20(1), p. 166. Coincident
    endpoints give the zero vector integral without assuming the
    actual derivative exists at that endpoint. *)
Example singleton_vector_primitive_subsegment_regression (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) (a b u : R) :
  is_complete_metric_space (real_norm_metric_space hN) -> curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] ->
  normed_curve_indefinite_derivative_integral hN g a b -> a<=u -> u<=b ->
  @is_measure_vector_integral R (real_line_metric R) E N hN
    (measure_restrict (@lebesgue_scalar_measure R) (`[u,u] : set (real_line_metric R)))
    (normed_curve_derivative hN g) 0.
Proof.
move=> hY hg he hF hau hub.
have hI := @normed_indefinite_derivative_integral_subsegment R E N hN g a b u u
  hY hg he hF hau (lexx _) hub.
by rewrite subrr in hI.
Qed.

(** Source for [constant_reflexive_curve_primitive_regression]: complete
    theorem regression for Federer 2.9.22, pp. 167–168, including
    all four conditions extending 2.9.20, pp. 165–166. A constant
    curve satisfies the finite-family law; the assembled theorem
    supplies the actual vector integral of its exact derivative on
    every prefix segment, with value zero even at the left endpoint. *)
Example constant_reflexive_curve_primitive_regression (R : realType)
    (E D B : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (c : E) (a b : R) :
  is_complete_metric_space (real_norm_metric_space hN) ->
  is_bidual_embedding ed eb tau -> is_reflexive_embedding tau -> a<b ->
  forall x : R, a<=x -> x<=b ->
    @is_measure_vector_integral R (real_line_metric R) E N hN
      (measure_restrict (@lebesgue_scalar_measure R) (`[a,x] : set (real_line_metric R)))
      (normed_curve_derivative hN (fun _ => c)) 0.
Proof.
move=> hY ht hr hab x hax hxb.
have hLip (t u : R) : mdist (c : real_norm_metric_space hN) c<=0*`|t-u|.
  by rewrite mdistxx mul0r.
have hBV := @lipschitz_curve_locally_finite_variation R
  [the metricType R of real_norm_metric_space hN] (fun _ : R => c) 0 hLip.
have hFull := @federer_2_9_22 R E D B N hN ed DN hD eb BN hB tau (fun _ => c) hY ht hr hBV.
have hEquiv := hFull.2.2.2 a b hab.
have hAC := @constant_metric_curve_absolutely_continuous R
  [the metricType R of real_norm_metric_space hN] c a b.
have hPrimitive := hEquiv.1.2 (hEquiv.2.1.2 hAC).
have hI := hPrimitive x hax hxb.
by rewrite subrr in hI.
Qed.

End NormedAbsoluteContinuityRegressions.

(** Source for [characteristic_curve_zero_endpoint_regression]: exact
    g(0)=0 in Federer 2.9.23, p. 168; regression for the
    empty open interval and the literal-function L1 convention. *)
Example characteristic_curve_zero_endpoint_regression (R : realType) :
  lebesgue_characteristic_curve (0 : R)=0.
Proof. exact: lebesgue_characteristic_curve_nonpositive (lexx _). Qed.

(** Source for [characteristic_curve_cross_zero_regression]: the
    Lipschitz bound of Federer 2.9.23, p. 168, on a pair
    straddling zero. The L1 distance from g(-1) to g(1)
    is one, although the distance between parameters is two. *)
Example characteristic_curve_cross_zero_regression (R : realType) :
  summable_real_seminorm
    (lebesgue_characteristic_curve (1 : R)-lebesgue_characteristic_curve (-1 : R)) = 1.
Proof.
have hle : (-1<= 1 :> R) by lra.
rewrite lebesgue_characteristic_curve_increment //.
have h1 : (0<= 1 :> R) := ler01.
have hn : (-1<=0 :> R) by lra.
by rewrite (max_l h1) (max_r hn) subr0.
Qed.

(** Source for [characteristic_curve_equal_increment_regression]:
    equal-endpoint extension of the exact L1 increment formula in
    Federer 2.9.23, p. 168; includes the zero endpoint. *)
Example characteristic_curve_equal_increment_regression (R : realType) (u : R) :
  0<=u -> summable_real_seminorm
    (lebesgue_characteristic_curve u-lebesgue_characteristic_curve u)=0.
Proof.
move=> hu; have hh := lebesgue_characteristic_curve_positive_increment hu (lexx u).
by move: hh; rewrite !subrr.
Qed.

(** Source for [characteristic_quotient_closed_test_boundary_regression]:
    supporting characteristic test for the weak-limit contradiction
    in Federer 2.9.23, p. 169; the quotient increment may
    equal the test interval width, including its closed endpoint. *)
Example characteristic_quotient_closed_test_boundary_regression (R : realType) (x h : R) :
  0<x -> 0<h ->
  summable_characteristic_functional (lebesgue_closed_test_interval_measurable x (x+h))
    (lebesgue_characteristic_quotient x h) = 1.
Proof. move=> hx hh; exact: lebesgue_characteristic_quotient_test hx hh (lexx h). Qed.

(** Source for [characteristic_curve_no_weak_derivative_regression]:
    the stronger final assertion of Federer 2.9.23, p. 169,
    at parameter one, tested against every proposed L1 limit. *)
Example characteristic_curve_no_weak_derivative_regression (R : realType)
    (v : summable_real_space (lebesgue_scalar_is_measure R)) :
  ~ punctured_seminorm_weak_limit (@summable_real_seminorm R R _ (lebesgue_scalar_is_measure R))
    (lebesgue_characteristic_quotient (1 : R)) v.
Proof. exact: lebesgue_characteristic_quotients_no_weak_limit ltr01. Qed.

(** Source for [characteristic_curve_negative_derivative_regression]:
    supporting negative-parameter boundary of Federer 2.9.23,
    pp. 168–169. The curve is locally zero at -1 and has
    the zero L1 derivative there; the printed failure is for x>0. *)
Example characteristic_curve_negative_derivative_regression (R : realType) :
  has_normed_curve_derivative (@summable_real_seminorm R R _ (lebesgue_scalar_is_measure R))
    (@lebesgue_characteristic_curve R) (-1) 0.
Proof.
move=> e he; exists (1/2); split; first by rewrite divr_gt0 // ltr0n.
move=> h /andP[_ hh].
have hbound : (-1+h<=0 :> R).
  move: hh; rewrite ltr_norml=> /andP[h1 h2]; lra.
have hn : (-1<=0 :> R) by lra.
rewrite (lebesgue_characteristic_curve_nonpositive hbound)
  (lebesgue_characteristic_curve_nonpositive hn) subrr scaler0 subr0.
by rewrite (real_seminorm_zero (summable_real_seminorm_laws (lebesgue_scalar_is_measure R))).
Qed.

Section IntegrationByPartsRegressions.
Local Open Scope ring_scope.

(** Source for [integration_by_parts_diagonal_regression]: the a=b
    boundary explicitly allowed in Federer 2.9.24, p. 169.
    The full theorem gives the zero integral for arbitrary f,g,
    without needing a derivative at the singleton endpoint. *)
Example integration_by_parts_diagonal_regression (R : realType) (f g : R -> R) (a : R) :
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,a]
    (weighted_real_curve_derivative_integrand f g) 0%E.
Proof.
have hAC := (@metric_absolute_continuity_real_agreement R g a a).1
  (@singleton_metric_absolute_continuity_regression R [the metricType R of real_line_metric R] g a).
have hV : (curve_variation (f : R -> real_line_metric R) a a < +oo)%E.
  by rewrite curve_variation_self ltry.
have hi := @federer_2_9_24 R f g a a (lexx a) hV hAC.
by rewrite stieltjes_integral_zero_width !subrr in hi.
Qed.

(** Source for [retracted_singleton_bv_regression]: local-hypothesis
    boundary in Federer 2.9.24, p. 169. Any function,
    even without variation assumptions elsewhere, gives a BV
    representative after retraction to a singleton. *)
Example retracted_singleton_bv_regression (R : realType) (f : R -> R) (a : R) :
  curve_locally_finite_variation (f \o @segment_retraction R a a : R -> real_line_metric R).
Proof.
apply: (@finite_interval_retracted_curve_variation R f a a (lexx a)).
by rewrite curve_variation_self ltry.
Qed.

(** Source for [zero_width_right_step_regression]: empty-cell
    convention in the step approximation of Federer 2.9.24,
    p. 169. Every approximating function on [a,a] is
    zero everywhere, including at a and outside the interval. *)
Example zero_width_right_step_regression (R : realType) (f : R -> R) (a : R)
    (n : nat) (x : R) : uniform_right_step_approximation f a a n x=0.
Proof.
apply: (@uniform_right_step_outside R f a a (lexx a) n x).
case: (leP x a)=> hx; [by left|by right].
Qed.

(** Source for [short_tagged_step_regression]: no-cell boundary
    of the finite step laws supporting Federer 2.9.24,
    p. 169. Two entries do not constitute a tagged cell. *)
Example short_tagged_step_regression (R : realType) (f : R -> R) (a r x : R) :
  tagged_step_function f [:: a;r] x=0.
Proof. exact: (@tagged_step_function_short R f [:: a;r] (leqnn 2) x). Qed.

(** Source for [parts_endpoint_counterexample_regression]: Regression for
    Federer 2.9.24, p. 169: using right endpoints for both factors on a
    single identity-function cell gives two instead of the boundary value
    one. *)
Example parts_endpoint_counterexample_regression (R : realType) :
  (1*(1-0)+1*(1-0) : R) != 1*1-0*0.
Proof. exact: right_tagged_cell_counterexample. Qed.

(** Source for [constant_ac_factor_integration_regression]: actual
    zero derivative integral in Federer 2.9.24, p. 169,
    for f(t)=t and constant g(t)=c. The Stieltjes term is
    c(b-a), so the boundary products cancel for either sign of c. *)
Example constant_ac_factor_integration_regression (R : realType) (c a b : R) :
  a<=b -> is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (weighted_real_curve_derivative_integrand (fun t : R => t) (fun _ => c)) 0%E.
Proof.
move=> hab.
have hId : curve_locally_finite_variation ((fun t : R => t) : R -> real_line_metric R).
  apply: monotone_locally_finite_variation; by move=> x y hxy.
have hAC := @constant_real_curve_absolutely_continuous R c a b.
have hi := @federer_2_9_24 R (fun t : R => t) (fun _ => c) a b hab (hId a b hab) hAC.
have hS := @stieltjes_integral_constant R (fun t : R => t) hId c a b hab.
rewrite hS in hi.
have he : b*c-a*c-c*(b-a)=0 by ring.
by rewrite he in hi.
Qed.

(** Source for [bounded_weighted_zero_regression]: zero-bound
    instance of the bounded-convergence step in Federer 2.9.24,
    p. 169. A summable signed density and M=0 require
    no division by the bound and give the actual zero integral. *)
Example bounded_weighted_zero_regression (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (q : X -> R) :
  summable_real_functions mu q ->
  is_measure_integral mu (real_total_integrand (fun x => 0*q x)) 0%E.
Proof.
move=> hq.
have [s hs] := hq.
have hzero := @real_total_integral_scale R X mu hm q s 0 hs.
rewrite (mul0r s) in hzero.
have hF := @measurable_total_constant R X
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 0.
have hbound (x : X) : `|0 : R|<=0 by rewrite normr0.
have hnbound (n : nat) (x : X) : `|0 : R|<=0 by rewrite normr0.
have hL : extended_order_limit (fun _ : nat => (0 : R)%:E) (0 : R)%:E.
  apply: real_error_extended_order_limit=> e he; exists 0%N=> n _.
  by rewrite subrr normr0.
have hAE : measure_almost_everywhere mu
    [set x | q x=0 \/ extended_order_limit (fun _ : nat => (0 : R)%:E) (0 : R)%:E].
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=> x _; right; exact: hL.
exact (@bounded_weighted_integral_limit R X mu hm (fun _ _ => 0) (fun _ => 0)
  q 0 (fun _ => 0) 0 hq hF (lexx _) hbound hnbound hAE (fun _ => hzero) hL).
Qed.

End IntegrationByPartsRegressions.

From Federer Require Import MeasureConullZeroIntegral MeasureIntegralGraphEquivalence
  MeasureIntegralUniqueness PartialZeroExtension ProductMeasure ParameterizedIntegral PartialProductSections.
Section ParameterIntegralRegressions.
Local Open Scope ring_scope.

(** Source for [zero_subset_integral_regression]: zero-integrand
    regression for Federer 2.9.25, p. 169, using the
    subset convention 2.4.10, p. 85. An arbitrary target
    and an infinite ambient measure still give integral zero. *)
Example zero_subset_integral_regression (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) :
  is_measure_subset_integral mu A (real_total_integrand (fun _ : X => (0 : R))) 0%E.
Proof.
apply: (@measure_almost_zero_integral R X mu hm).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
  (measure_almost_everywhere_true hm))=> x _.
case: (pselect (A x))=> hx.
- apply/(partial_function_zero_extension_on _ _ _ hx); by apply/real_total_integrand_graph.
- by apply/(partial_function_zero_extension_off _ _ _ hx).
Qed.

(** Source for [empty_summable_restriction_regression]: empty-prefix
    boundary for Federer 2.9.25, p. 169. Restrict a signed
    summable partial integrand to the empty set; its actual
    finite integral is zero, regardless of its original domain. *)
Example empty_summable_restriction_regression (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_summable mu f -> exists J : R,
    is_measure_subset_integral mu set0 f J%:E /\ J=0.
Proof.
move=> hf.
have [J hJ] := @summable_measurable_zero_extension R X mu hm set0 f
  (measure_measurable_empty hm) hf.
exists J; split=> //.
have hz := @null_target_subset_integral R X mu f set0 hm (measure_empty hm).
have he := measure_integral_unique hJ hz.
change (J%:E=(0 : R)%:E) in he; by case: he.
Qed.

(** Source for [zero_parameter_integral_local_regression]: local and
    infinite-measure regression for the complete proposition Federer 2.9.25,
    p. 169 Use u=0 and any g vanishing on [a,b], with arbitrary behaviour
    outside it. Neither finite nor sigma-finite mass of phi is assumed, and
    the actual derivative equals zero almost everywhere on the interval. *)
Example zero_parameter_integral_local_regression (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (hp : is_measure phi) (g : R -> R) (a b : R) :
  a<b -> (forall t, a<=t -> t<=b -> g t=0) ->
  is_absolutely_continuous_real_curve g a b /\
  measure_almost_everywhere_on (@lebesgue_scalar_measure R) `[a,b]
    [set t | has_real_curve_derivative g t 0].
Proof.
move=> hab hg.
pose U := real_total_integrand (fun _ : X*real_line_metric R => (0 : R)).
have hJ := @zero_subset_integral_regression R (X*real_line_metric R)%type
  (product_measure hp (lebesgue_scalar_is_measure R))
  (product_measure_is_measure hp (lebesgue_scalar_is_measure R)) (setT `*` `[a,b]).
have hG t : a<=t -> t<=b -> is_measure_integral phi
    (parameterized_integral (@lebesgue_scalar_measure R) (fun x =>
      partial_function_zero_extension (0 : extended_real_line R) `[a,t]
        (partial_product_vertical_section U x))) (g t)%:E.
  move=> hat htb; rewrite (hg t hat htb).
  apply: (@measure_almost_zero_integral R X phi hp).
  apply: (@measure_almost_everywhere_mono R X phi hp setT _ _
    (measure_almost_everywhere_true hp))=> x _.
  apply/(parameterized_integral_specification _ _ x 0%E).
  apply: (@measure_integral_graph_equivalent R (real_line_metric R)
    (@lebesgue_scalar_measure R) _ _ 0%E _
    (@zero_subset_integral_regression R (real_line_metric R) (@lebesgue_scalar_measure R)
      (lebesgue_scalar_is_measure R) `[a,t]))=> y z.
  by [].
have [hAC hAE] := @federer_2_9_25 R X phi hp (fun _ => (0 : R)) g a b 0 hab hJ hG.
split=> //.
apply/(measure_almost_everywhere_on_implication (@lebesgue_scalar_measure R) `[a,b] _).
have hAE' := (measure_almost_everywhere_on_implication (@lebesgue_scalar_measure R) `[a,b] _).1 hAE.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hAE')=> t ht hIt.
have [v [hd hi]] := ht hIt.
have hz : is_measure_integral phi (partial_product_horizontal_section U t) 0%E.
  apply: (@measure_almost_zero_integral R X phi hp).
  apply: (@measure_almost_everywhere_mono R X phi hp setT _ _
    (measure_almost_everywhere_true hp))=> x _.
  by apply/real_total_integrand_graph.
have hv : v=0.
  have he := measure_integral_unique hi hz.
  change (v%:E=(0 : R)%:E) in he; by case: he.
by rewrite -hv.
Qed.

End ParameterIntegralRegressions.
