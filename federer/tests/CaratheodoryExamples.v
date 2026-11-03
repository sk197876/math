(** Regression examples for Federer (1969), subsection 2.10.
    Source locators accompany each example. The public metric
    and corrected topological specifications and interfaces are
    exported by CaratheodoryTheorems.v. No concrete witness
    construction is imported by these regressions. *)
From mathcomp Require Import lra ring.
From Federer Require Import FinitePrefixes EuclideanCoordinateMetric LipschitzBasic LipschitzConstant.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology num_normedtype normed_module.
From Federer Require Import CoveringFamilyUP OrthonormalFamilies CoordinateProjection LipschitzCurveVariation NormMetricScaleContinuity
  CurveVariationUP CaratheodoryTheorems NonnegativeSum NonnegativeSumSupport NonnegativeSumConstant
  MeasureUP MeasureBasic RealMetricBackground MetricClosedBalls MetricDiameterUP MetricDiameter MetricDiameterMaps MetricDiameterReal
  RealNormUP NormMetric CountingMeasure CountingMeasureBorel HausdorffLengthUP HausdorffLength
  GrassmannAbbreviations InnerProductUP EuclideanInnerProduct InnerMetric InnerNorm InnerNormedTopology
  FiniteCoordinates EuclideanBallVolume EuclideanLebesgueDimensions EuclideanOneCoordinate
  LebesgueScalarMeasure MeasureSplit PointMassMeasure ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic MeasurableFunctionUP MeasurableTotalBasic PointMassRegularity
  MeasureAlmostUP MeasureAlmostBasic ExtendedRealReciprocalBounds MeasureIndexedCover
  ExtendedRealOrderLimit ExtendedRealBounds TopologicalBorel ReciprocalSequenceLimits CompleteMetricUP
  LipschitzUP MeasureIntegralUP MeasureIntegralBounds InfiniteDiscreteMeasure.
From Federer Require Import InnerConvex ExteriorNorm ExteriorGrading FiniteExteriorPowers
  AssociatedSubspace SimpleElementary ExteriorProductFactors OrthogonalProjectionConstants.
From Federer Require Import MetricSubsetBackground EuclideanBlockCoordinates MetricScaleCutoffCost.
From Federer Require Import CoveringRelationLimits ExtendedRealConventions SuslinSetUP BorelClosedProjection.
From Federer Require Import AffineSubspaceSpace EuclideanProjectionSpace EuclideanLinearMaps MappingMultiplicity.
From Federer Require Import StieltjesSubstitution MeasureConullZeroIntegral MeasureIntegralUniqueness.
From Federer Require Import CharacteristicFunctionUP CharacteristicFunctionSealed MeasureExtendedCharacteristicIntegral SphericalCountingMeasure BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [closed_infinity_caratheodory_regression]:
    regression combining the independent closed
    convex construction and the identity Q_infinity=C
    in Federer 2.10.5(2), p. 173. The target
    can be unbounded or have infinite measure. *)
Example closed_infinity_caratheodory_regression (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @closed_convex_integral_geometric_measure R n m hmn +oo A=
    @caratheodory_projection_measure R n m A.
Proof.
rewrite -(@infinity_convex_integral_geometric_open_closed_agreement R n m hmn A).
exact: convex_integral_geometric_infinity.
Qed.

(** Source for [zero_weight_infinite_input_norm_regression]:
    zero times infinity convention in 2.4.12, p. 86,
    used for the finite real weights of 2.10.24,
    pp. 186–188. An everywhere infinite input, without
    an almost-finite-value hypothesis, becomes the total
    zero input when its coefficient is zero; its actual
    extended-input norm is zero at every exponent. *)
Example zero_weight_infinite_input_norm_regression (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (p : \bar R) :
  is_measure mu -> 1<=p ->
  nonnegative_extended_exponent_norm mu (fun _ : X=>0%:E*(+oo : extended_real_line R)) p=0.
Proof.
move=> hm hp.
rewrite (@nonnegative_extended_norm_scale R X mu hm (fun _ : X=>(+oo : extended_real_line R))
  p 0%R (fun _=>leey _) hp (lexx _)
  (@measurable_total_constant R X (extended_real_line R) mu hm +oo)).
exact: mul0e.
Qed.

(** Source for [zero_dimensional_perturbation_inverse_regression]:
    boundary regression for the inverse estimates
    supporting Federer 2.10.5(2), p. 173,
    from 2.7.16, p. 134. In dimension zero
    the unique endomorphism still has an inverse,
    although its operator norm is zero. *)
Example zero_dimensional_perturbation_inverse_regression (R : realType)
    (f : {linear R_n R 0 -> R_n R 0}) :
  exists g : {linear R_n R 0 -> R_n R 0}, cancel f g /\ cancel g f /\
    forall y, (inner_norm (@euclidean_inner_productP R 0) (g y)<=
      2*inner_norm (@euclidean_inner_productP R 0) y)%R.
Proof.
apply: near_identity_euclidean_inverse_bound=> x _.
by rewrite (coordinate_zero (f x-x)) inner_norm0 invr_ge0 ler0n.
Qed.

(** Source for [extended_infinite_input_nonzero_regression]:
    boundary regression for the zero-norm criterion
    used in Federer 2.10.5, p. 173, from
    2.4.12, p. 86. A function constantly
    infinity on a probability space cannot have
    zero norm at any admissible exponent. *)
Example extended_infinite_input_nonzero_regression (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (t : \bar R) :
  mu setT = 1 -> 1<=t -> nonnegative_extended_exponent_norm mu
    (fun _ : X => (+oo : extended_real_line R)) t<>0.
Proof.
move=> hprob ht hz.
have hf := @measurable_total_constant R X (extended_real_line R) mu hm +oo.
have hae := (@nonnegative_extended_norm_zero_iff R X mu hm
  (fun _ : X => (+oo : extended_real_line R)) t (fun _ => leey 0) ht hf).1 hz.
have hset : [set x : X | (+oo : \bar R)=0]=set0.
  by apply/seteqP; split=> x //.
have hwhole : mu setT=0 by move: hae; rewrite /measure_almost_everywhere hset setC0.
have hbad : (1 : \bar R)=0 by rewrite -hprob hwhole.
by have := (lte01 : (0 : \bar R)<1); rewrite hbad ltxx.
Qed.

(** Source for [extended_infinite_null_exception_regression]:
    regression for the almost everywhere reduction
    needed by Federer 2.10.5, p. 173, and
    2.3.1, p. 72. On a two-point space
    with unit mass at false, infinity at true
    is a null exception and every norm is zero.
    This complements the positive-mass infinity test. *)
Example extended_infinite_null_exception_regression (R : realType) (t : \bar R) :
  1<=t -> nonnegative_extended_exponent_norm (point_mass R false)
    (fun b : bool => if b then (+oo : extended_real_line R) else 0) t=0.
Proof.
move=> ht.
pose mu := point_mass R false.
pose f (b : bool) : extended_real_line R := if b then +oo else 0.
have hm : is_measure mu := point_mass_is_measure R false.
have hf : is_measure_measurable_function mu (partial_function_total f).
  constructor.
  - rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
  - move=> U _; exact: point_mass_every_set_measurable.
have h0 b : 0<=f b by case: b; rewrite /f //= leey.
apply: (@nonnegative_extended_norm_zero_iff R _ mu hm f t h0 ht hf).2.
apply: point_mass_out=> hnot; apply: hnot; by [].
Qed.

(** Source for [extended_infinite_input_essential_regression]:
    regression for the unbounded projected-volume
    inputs in Federer 2.10.5, p. 172. A
    function constantly positive infinity on a
    probability space has infinite essential norm;
    replacing its values by their scalar parts
    would incorrectly turn this value into zero. *)
Example extended_infinite_input_essential_regression (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  mu setT = 1 -> nonnegative_extended_exponent_norm mu
    (fun _ : X => (+oo : extended_real_line R)) +oo = +oo.
Proof.
move=> hprob.
have hf := @measurable_total_constant R X (extended_real_line R) mu hm +oo.
have hn := @nonnegative_extended_exponent_norm_specification R X mu
  (fun _ : X => (+oo : extended_real_line R)) +oo hm (fun _ => leey 0) (leey 1) hf.
apply/eqP; rewrite eq_le leey andTb; apply: hn.2=> r [_ hz].
case: (eqVneq r +oo)=> [->|hne]; first exact: lexx.
have hr : r < +oo by rewrite lt_neqAle hne leey.
have he : [set x : X | r < +oo]=setT by apply/seteqP; split=> x _ //.
have hz' : mu setT=0 by move: hz; rewrite he.
have hbad : (1 : \bar R)=0 by rewrite -hprob hz'.
by have := (lte01 : (0 : \bar R)<1); rewrite hbad ltxx.
Qed.

(** Source for [projection_zero_dimensional_point_volume_regression]:
    boundary regression for the supporting degree-zero
    convention alongside Federer 2.10.5, p. 172.
    The image of the unique zero-dimensional point
    has Lebesgue volume one, rather than zero.
    The printed target itself assumes m positive. *)
Example projection_zero_dimensional_point_volume_regression (R : realType)
    (p : euclidean_projection_space R 0 0) :
  projected_volume_function [set (0 : inner_metric_space (@euclidean_inner_productP R 0))%R] p = 1.
Proof.
rewrite /projected_volume_function /euclidean_lebesgue_measure.
apply: point_mass_in; exists 0%R=> //; exact: linear0.
Qed.

(** Source for [projection_measures_empty_regression]: empty
    target boundary of both measures in Federer 2.10.4,
    p. 172, including the auxiliary m=0 interfaces.
    Empty generators need no special convention beyond
    their actual projected-volume cost. *)
Example projection_measures_empty_regression (R : realType) (n m : nat) :
  (m<=n)%N -> @gross_measure R n m set0=0 /\ @caratheodory_projection_measure R n m set0=0.
Proof.
move=> hmn; split; apply: measure_empty;
  [exact: gross_measure_is_measure|exact: caratheodory_projection_measure_is_measure].
Qed.

(** Source for [projection_measures_closed_convex_regression]:
    closed convex alternative of Federer 2.10.4(2),
    p. 172, instantiated also at the empty-product
    boundary n=m=0. The latter tests the auxiliary
    interface and is not a printed positive-degree claim. *)
Example projection_measures_closed_convex_regression (R : realType) :
  is_closed_convex_projection_measure 0 (@caratheodory_projection_measure R 0 0).
Proof. exact (@caratheodory_projection_closed_cover_specification R 0 0 (leqnn 0)). Qed.

(** Source for [projection_one_hausdorff_regression]: final
    C^1=H^1 equality in Federer 2.10.4, p. 172,
    for an arbitrary target, including nonmeasurable
    and unbounded sets. *)
Example projection_one_hausdorff_regression (R : realType) (n : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (1<=n)%N -> @caratheodory_projection_measure R n 1 A=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 1 A.
Proof. exact: caratheodory_projection_one_hausdorff_measure. Qed.

(** Source for [projection_empty_gauge_regression]: empty
    generator boundary in Federer 2.10.4(1)–(2),
    p. 172. This checks the actual supremum over
    nonempty O*(n,m), without inserting a zero value
    or relying on a nonempty target premise. *)
Example projection_empty_gauge_regression (R : realType) (n m : nat) :
  (m<=n)%N -> @projected_volume_gauge R n m set0=0.
Proof. exact: projected_volume_gauge_empty. Qed.

(** Source for [zero_dimensional_dilation_volume_regression]:
    auxiliary empty-product boundary of the dilation
    estimate supporting Federer 2.10.4(2), p. 172.
    In dimension zero a zero dilation still has unit
    whole-space volume: its determinant factor is 0^0=1. *)
Example zero_dimensional_dilation_volume_regression (R : realType)
    (a : inner_metric_space (@euclidean_inner_productP R 0)) :
  euclidean_lebesgue_measure 0 ((@affine_dilation R (R_n R 0) a 0%R) @` setT) = 1.
Proof.
rewrite euclidean_affine_dilation_volume normr0 expr0 mul1e /euclidean_lebesgue_measure.
exact: point_mass_in.
Qed.

(** Source for [nonconvex_pair_projection_gauge_regression]:
    local regression for the convexity restriction in
    Federer 2.10.4, p. 172. Two distinct points
    have zero degree-one projected-volume gauge and
    positive diameter, so the printed gauge identity
    cannot be extended to arbitrary nonconvex sets. *)
Example nonconvex_pair_projection_gauge_regression (R : realType) :
  let E := inner_metric_space (@euclidean_inner_productP R 1) in
  let e : E := @coordinate_basis R 1 ord0 in
  let A : set E := [set 0%R] `|` [set e] in
  projected_volume_gauge 1 A=0 /\ 1<=extended_metric_diameter A.
Proof.
move=> E e A.
have hA0 : A 0%R by left.
have hAe : A e by right.
have hz : projected_volume_gauge 1 A=0.
  apply/eqP; rewrite eq_le (@projected_volume_gauge_nonnegative R 1 1 A (leqnn 1)) andbT.
  apply: projected_volume_gauge_least_bound=> p hp.
  rewrite euclidean_one_measure_scalar_image image_comp.
  pose f (x : E) := euclidean_one_project (p x).
  have hcover : f @` A `<=` [set f 0%R] `|` [set f e].
    move=> y [x [hx|hx] <-]; [left|right]; by rewrite -hx.
  have hh := measure_binary_cover (lebesgue_scalar_is_measure R) hcover.
  by rewrite !lebesgue_scalar_singleton add0e in hh.
split=> //.
have hh := metric_diameter_upper (extended_metric_diameter_specification A) hA0 hAe.
have hdist : (mdist (0:E)%R e = 1)%R.
  rewrite inner_metric_distanceE sub0r inner_normN.
  rewrite -(@inner_norm_topologyE R (R_n R 1) (@euclidean_inner_product R 1)
    (@euclidean_inner_productP R 1)) (@euclidean_norm_one R e).
  by rewrite /e /coordinate_basis ffunE eqxx normr1.
by rewrite hdist in hh.
Qed.

(** Source for [exterior_measure_empty_regression]: empty
    target boundary of the construction in Federer
    2.10.3, pp. 171–172. Empty targets have zero
    mass even though the generator family excludes empty sets. *)
Example exterior_measure_empty_regression (R : realType) (n m : nat) :
  @exterior_diameter_measure R n m set0=0.
Proof. apply: measure_empty; exact: exterior_diameter_measure_is_measure. Qed.

(** Source for [exterior_measure_three_cover_families_regression]:
    all three alternative families in Federer 2.10.3,
    p. 172, tested on the same selected measure rather
    than by assuming equality of alternative constructions. *)
Example exterior_measure_three_cover_families_regression (R : realType) (n m : nat) :
  is_open_exterior_diameter_measure m (@exterior_diameter_measure R n m) /\
  is_compact_exterior_diameter_measure m (@exterior_diameter_measure R n m) /\
  is_convex_exterior_diameter_measure m (@exterior_diameter_measure R n m).
Proof.
split; first exact: exterior_measure_open_cover_specification.
split; [exact: exterior_measure_compact_cover_specification|exact: exterior_measure_convex_cover_specification].
Qed.

(** Source for [exterior_measure_countable_regression]: supporting
    countable-cover boundary of Federer 2.10.3,
    pp. 171–172, with the printed positive-degree premise
    and no ambient-dimension lower bound. *)
Example exterior_measure_countable_regression (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (0<m)%N -> countable A -> @exterior_diameter_measure R n m A=0.
Proof. exact: exterior_measure_positive_countable_zero. Qed.

(** Source for [exterior_gauge_above_dimension_regression]:
    degree m>n is allowed by Federer 2.10.3,
    p. 171. The actual exterior gauge vanishes even
    on the unbounded whole space, by 1.3.2, pp. 14–15. *)
Example exterior_gauge_above_dimension_regression (R : realType) (n m : nat) :
  (n<m)%N -> @exterior_diameter_cost R n m setT=0.
Proof. exact: exterior_diameter_cost_above_dimension. Qed.

(** Source for [exterior_zero_dimensional_measure_regression]:
    supporting ambient-dimension-zero boundary of Federer
    2.10.3, pp. 171–172. The Euclidean space has
    a sole point and hence zero positive-degree T^m mass. *)
Example exterior_zero_dimensional_measure_regression (R : realType) (m : nat) :
  (0<m)%N -> @exterior_diameter_measure R 0 m setT=0.
Proof.
move=> hm.
have hset : @setT (inner_metric_space (@euclidean_inner_productP R 0))=[set 0%R].
  apply/seteqP; split=> x hx=> //; apply/ffunP=> i.
  have hi := ltn_ord i; by rewrite ltn0 in hi.
rewrite hset; exact: exterior_measure_positive_singleton_zero.
Qed.

(** Source for [exterior_gauge_convex_hull_regression]:
    unchanged convex-hull cost in Federer 2.10.3,
    p. 172, without a finiteness, nonemptiness or
    degree-versus-dimension assumption on the input set. *)
Example exterior_gauge_convex_hull_regression (R : realType) (n m : nat)
    (A : set (R_n R n)) :
  exterior_diameter_cost m (convex_hull A)=exterior_diameter_cost m A.
Proof. exact: exterior_diameter_cost_convex_hull. Qed.

(** Source for [countable_zero_cost_singletons_regression]:
    countable, zero-diameter and zero-cost boundary of Federer
    2.10.1, pp. 169–170. Singleton generators of cost
    zero cover every countable target at every positive cutoff;
    the final measure of such a target is zero. *)
Example countable_zero_cost_singletons_regression (R : realType) (X : metricType R)
    (A : set X) : countable A ->
  caratheodory_measure (fun x : X => [set x]) (fun _ => (0 : \bar R)) A=0.
Proof.
move=> hA.
pose S := fun x : X => [set x].
pose cost := fun _ : X => (0 : \bar R).
have hm := @caratheodory_measure_is_measure R X X S cost (fun _ => lexx 0).
apply/eqP; rewrite eq_le (measure_nonnegative hm A) andbT.
apply: (caratheodory_limit_least (caratheodory_measure_specification S cost))=> delta nu hd hn.
have hdiam x : extended_metric_diameter (S x)<=delta.
  apply: le_trans (_ : extended_metric_diameter (S x)<=0) (ltW hd).
  apply: (metric_diameter_least (extended_metric_diameter_specification (S x)))=> // y z -> ->.
  by rewrite mdistxx.
have hcov : A `<=` \bigcup_(x in A) S x by move=> x hx; exists x.
have hb := @metric_scale_envelope_lower R X X S cost delta nu hn A A hA (fun x _ => hdiam x) hcov.
by rewrite (nonnegative_sum_zero (fun x _ => erefl (cost x))) in hb.
Qed.

(** Source for [integer_dimensional_empty_regression]: empty
    target boundary of Federer 2.10.2(1)–(2), p. 171,
    using the actual independently selected measures at
    every integer degree, including zero. *)
Example integer_dimensional_empty_regression (R : realType) (X : metricType R) (m : nat) :
  @hausdorff_measure R X m set0=0 /\ @spherical_measure R X m set0=0.
Proof.
split; apply: measure_empty; [exact: hausdorff_measure_is_measure|exact: spherical_measure_is_measure].
Qed.

(** Source for [zero_degree_infinite_mass_regression]: infinite set boundary
    of the counting assertion in Federer 2.10.2(1), p. 171, and the
    spherical comparison in (2) *)
Example zero_degree_infinite_mass_regression (R : realType) (X : metricType R) (A : set X) :
  infinite_set A -> @hausdorff_measure R X 0 A=+oo /\ @spherical_measure R X 0 A=+oo.
Proof.
move=> hA; rewrite hausdorff_zero_counting_measure spherical_zero_counting_measure.
by rewrite (@counting_measure_infinite R X A hA).
Qed.

(** Source for [zero_degree_unbounded_gauge_regression]: infinity^0=1
    convention in the gauge of Federer 2.10.2, p. 171 Infinite diameter does
    not give infinite degree-zero cost. *)
Example zero_degree_unbounded_gauge_regression (R : realType) (X : metricType R) (A : set X) :
  extended_metric_diameter A=+oo -> hausdorff_diameter_cost 0 A = 1.
Proof. move=> _; exact: hausdorff_diameter_cost_zero_degree. Qed.

(** Source for [positive_degree_countable_pair_regression]:
    zero-diameter covering boundary for Federer 2.10.2,
    p. 171. Positive-radius spherical balls suffice to
    give zero mass to every countable target at positive
    integer degree, together with Hausdorff measure. *)
Example positive_degree_countable_pair_regression (R : realType) (X : metricType R)
    (m : nat) (A : set X) : (0<m)%N -> countable A ->
  @hausdorff_measure R X m A=0 /\ @spherical_measure R X m A=0.
Proof.
move=> hm hA; split; [exact: hausdorff_positive_degree_countable_zero hm hA|
  exact: spherical_positive_degree_countable_zero hm hA].
Qed.

(** Source for [integer_degree_one_legacy_regression]:
    degree-one normalization in Federer 2.10.2(1), p. 171,
    checked against the independently sealed Hausdorff
    length used previously for 2.5.10, p. 101. *)
Example integer_degree_one_legacy_regression (R : realType) (X : metricType R) (A : set X) :
  @hausdorff_measure R X 1 A=@hausdorff_length R X A.
Proof. exact: hausdorff_measure_one_length. Qed.

(** Source for [convex_covers_counting_regression]: joint
    convex-cover and degree-zero boundary of Federer
    2.10.2(1), p. 171. In any real normed vector
    space, counting measure satisfies the convex-cover
    construction laws, with no dimension bound. *)
Example convex_covers_counting_regression (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) :
  @is_convex_hausdorff_measure R V N hN 0 (@counting_measure R (real_norm_metric_space hN)).
Proof.
have he : @hausdorff_measure R (real_norm_metric_space hN) 0=
    @counting_measure R (real_norm_metric_space hN).
  apply: funext=> A; exact: hausdorff_zero_counting_measure.
rewrite -he; exact: hausdorff_convex_cover_specification.
Qed.

(** Source for [zero_dimensional_open_ball_regression]:
    zero-dimensional Euclidean boundary of Federer
    2.10.2(2), p. 171. At degree zero both positive-
    radius ball families give unit mass to the sole point;
    their diameter factor is zero, rather than two. *)
Example zero_dimensional_open_ball_regression (R : realType) :
  let X := inner_metric_space (@euclidean_inner_productP R 0) in
  @spherical_measure R X 0 setT = 1 /\ @open_ball_spherical_measure R X 0 setT = 1.
Proof.
move=> X.
have hset : @setT X=[set (0 : X)%R].
  apply/seteqP; split=> x hx=> //; apply/ffunP=> i.
  have hi := ltn_ord i; by rewrite ltn0 in hi.
have hs : @spherical_measure R X 0 setT = 1.
  by rewrite spherical_zero_counting_measure hset counting_singleton.
split=> //; rewrite -euclidean_spherical_open_ball_equality; exact hs.
Qed.

(** Source for [open_cutoff_final_measure_distinction_regression]:
    local interval/degree-zero replacement of Federer's
    circle example in 2.10.2(1), p. 171. The fixed
    cutoff values differ while the final measures agree;
    this does not claim the printed circle computation. *)
Example open_cutoff_final_measure_distinction_regression (R : realType) :
  let X := real_line_metric R in
  let A : set X := `[(0:R)%R,(1:R)%R] in
  let phi := metric_scale_envelope (fun j : @nonempty_metric_sets R X => val j)
    (fun j => hausdorff_diameter_cost 0 (val j)) 1 in
  let psi := metric_scale_envelope (fun j : @nonempty_open_metric_sets R X => val j)
    (fun j => hausdorff_diameter_cost 0 (val j)) 1 in
  phi A<>psi A /\ @hausdorff_measure R X 0 A=@open_hausdorff_measure R X 0 A.
Proof.
move=> X A phi psi.
have [hphi hpsi] := @hausdorff_open_cutoff_differs R.
have hphi' : phi A = 1 := hphi.
have hpsi' : (2:R)%:E<=psi A := hpsi.
split; last exact: hausdorff_open_measure_equality.
move=> he; rewrite -he hphi' in hpsi'.
rewrite lee_fin in hpsi'.
have hlt : (1<(2:R))%R by rewrite ltr1n.
by have := lt_le_trans hlt hpsi'; rewrite ltxx.
Qed.

(** Source for [empty_target_infinite_cost_regression]: empty
    covering boundary in Federer 2.10.1, p. 170. Even
    when every generator has infinite cost, the final measure
    of the empty target is zero. *)
Example empty_target_infinite_cost_regression (R : realType) (X : metricType R)
    (S : unit -> set X) :
  caratheodory_measure S (fun _ => (+oo : \bar R)) set0=0.
Proof.
apply: measure_empty; apply: caratheodory_measure_is_measure=> j; exact: leey.
Qed.

(** Source for [empty_generators_nonempty_target_regression]:
    no-cover boundary of Federer 2.10.1, p. 170. Empty
    generators cannot cover a nonempty target, even at infinite
    scale and with zero costs; the final value is infinity. *)
Example empty_generators_nonempty_target_regression (R : realType) (X : metricType R)
    (A : set X) : (exists x, A x) ->
  caratheodory_measure (fun _ : unit => @set0 X) (fun _ => (0 : \bar R)) A=+oo.
Proof.
move=> [x hx].
pose S := fun _ : unit => @set0 X.
pose cost := fun _ : unit => (0 : \bar R).
pose nu := metric_scale_envelope S cost 1.
have hn := metric_scale_envelope_specification S cost 1.
have hinf : nu A=+oo.
  apply/eqP; rewrite eq_le leey /=.
  apply: (metric_scale_envelope_greatest hn)=> G _ _ hcov.
  by have [j _ hfalse] := hcov x hx.
have hb := @caratheodory_limit_upper R X [the choiceType of (unit : Type)] S cost _
  (caratheodory_measure_specification S cost) A 1 nu ltac:(by []) hn.
rewrite hinf in hb; by apply/eqP; rewrite eq_le leey hb.
Qed.

(** Source for [infinite_singleton_cost_regression]: infinite
    gauge value allowed in Federer 2.10.1, pp. 169–170.
    A sole singleton of infinite cost retains infinite mass;
    its zero diameter does not turn the cost into zero. *)
Example infinite_singleton_cost_regression (R : realType) (X : metricType R) (x : X) :
  caratheodory_measure (fun _ : unit => [set x]) (fun _ => (+oo : \bar R)) [set x]=+oo.
Proof.
have hdiam : extended_metric_diameter [set x]<=1.
  apply: (metric_diameter_least (extended_metric_diameter_specification [set x])); first exact: lee01.
  by move=> y z -> ->; rewrite mdistxx lee_fin ler01.
have hinf := @single_generator_scale_mass R X [set x] [set x] 1 +oo
  (leey _) hdiam (fun _ h => h) (ex_intro _ x (erefl x)).
have hb := @caratheodory_limit_upper R X [the choiceType of (unit : Type)]
  (fun _ => [set x]) (fun _ => (+oo : \bar R)) _
  (caratheodory_measure_specification (fun _ : unit => [set x]) (fun _ => (+oo : \bar R)))
  [set x] 1 _ ltac:(by [])
  (metric_scale_envelope_specification (fun _ : unit => [set x]) (fun _ => (+oo : \bar R)) 1).
rewrite hinf in hb; by apply/eqP; rewrite eq_le leey hb.
Qed.

(** Source for [literal_and_corrected_topology_regression]:
    distinguish the local correction to the topological remark
    in Federer 2.10.1, p. 170, from the printed A-cover
    expression. On the same sealed two-point space and gauge,
    the literal expression is not a measure, while the corrected
    whole-space-cover construction satisfies the measure laws. *)
Example literal_and_corrected_topology_regression (R : realType) :
  let X := TwoPointOpenTopology.space in
  let S := fun _ : unit => @setT X in
  let c := fun _ : unit => (1 : \bar R) in
  ~ is_measure (printed_open_refinement_value S c) /\
    is_measure (topological_caratheodory_measure S c).
Proof.
move=> X S c; split.
- exact: (@printed_topological_refinement_not_measure R).2.2.
- apply: topological_caratheodory_measure_is_measure=> j; exact: lee01.
Qed.

(** Source for [corrected_metric_zero_cost_regression]: agreement
    of the two constructions asserted in Federer 2.10.1,
    p. 170, including countable targets and zero costs.
    The corrected topological object has the same zero value
    as the metric singleton-cover construction. *)
Example corrected_metric_zero_cost_regression (R : realType) (X : metricType R)
    (A : set X) : countable A ->
  topological_caratheodory_measure (fun x : X => [set x]) (fun _ => (0 : \bar R)) A=0.
Proof.
move=> hA.
rewrite (@topological_caratheodory_metric_agreement R X X
  (fun x => [set x]) (fun _ => (0 : \bar R)) _ _
  (topological_caratheodory_specification (fun x : X => [set x]) (fun _ => (0 : \bar R)))
  (caratheodory_measure_specification (fun x : X => [set x]) (fun _ => (0 : \bar R)))
  (fun _ => lexx 0) A).
exact: countable_zero_cost_singletons_regression.
Qed.

(** Source for [infinite_cutoff_limit_regression]: full positive-
    cutoff limit in Federer 2.10.1, p. 170, at an infinite
    final value. The sole unit-interval generator has no cover
    below its diameter, so the limit is infinity. *)
Example infinite_cutoff_limit_regression (R : realType) :
  let S : set (real_line_metric R) := `[0%R,1%R] in
  positive_cutoff_order_limit
    (fun delta => metric_scale_envelope (fun _ : unit => S) (fun _ => (1 : \bar R)) delta S) +oo.
Proof.
move=> S.
have hlim := @caratheodory_limit_positive_cutoff_convergence R [the metricType R of real_line_metric R]
  [the choiceType of (unit : Type)] (fun _ => S) (fun _ => (1 : \bar R)) _ S
  (caratheodory_measure_specification (fun _ : unit => S) (fun _ => (1 : \bar R))).
by rewrite caratheodory_single_interval_not_extension in hlim.
Qed.

(** Source for [identity_integrator_all_targets_regression]:
    regression for the final sentence of Federer 2.10.7,
    p. 175. All subsets, including non-Borel ones, have the
    same value for the independent interval construction,
    normalized Hausdorff measure and the sealed Lebesgue measure. *)
Example identity_integrator_all_targets_regression (R : realType)
    (A : set (real_line_metric R)) :
  stieltjes_caratheodory_measure (fun x : R => x) A=
    @hausdorff_measure R [the metricType R of real_line_metric R] 1 A /\
  @hausdorff_measure R [the metricType R of real_line_metric R] 1 A=
    @lebesgue_scalar_measure R A.
Proof.
split; first exact: identity_caratheodory_hausdorff_length.
exact: real_hausdorff_measure_one_lebesgue.
Qed.

(** Source for [jump_endpoint_raw_cost_regression]: local counterexample to
    dropping endpoint continuity from Federer 2.10.7, p. 174. The step
    integrator gives raw cost one to (-1,0), while the constructed measure
    of that interval is zero. This also distinguishes Federer's cost from
    the one-sided-limit cost; it is not a correction in Federer's erratum. *)
Example jump_endpoint_raw_cost_regression (R : realType) :
  let g := fun x : R => if (0<=x)%R then 1%R else 0%R in
  (g 0-g (-1))%:E = (1 : \bar R) /\
  stieltjes_caratheodory_measure g `](-1)%R,0%R[=0.
Proof.
move=> g.
have hg x y : (x<=y)%R -> (g x<=g y)%R.
  move=> hxy; rewrite /g; case: ifP=> hx; case: ifP=> hy; lra.
split; first by rewrite /g lexx ler0N1 /= subr0.
have hd (n : nat) : (0<((n.+1)%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
have hd1 (n : nat) : (((n.+1)%:R : R)^-1<=1)%R.
  by rewrite invf_le1 ?ltr0n // ler1n.
have hab n : ((-2 : R) < -((n.+1)%:R)^-1)%R.
  apply: lt_le_trans (_ : (-1<=-((n.+1)%:R)^-1)%R).
  - by rewrite ltrN2 ltr1n.
  - by rewrite lerN2; exact: hd1.
pose j (n : nat) := @stieltjes_interval_index R (-2) (-((n.+1)%:R)^-1) (hab n).
pose G := j @` setT.
have hG : countable G := sub_countable (card_image_le j setT) (@countableP nat setT).
have hz k : G k -> stieltjes_interval_cost g k=0.
  move=> [n _ <-]; rewrite /stieltjes_interval_cost /j /stieltjes_interval_index /= /g.
  have hn := hd n.
  have hneg : (0<=-((n.+1)%:R : R)^-1)%R=false by rewrite oppr_ge0 leNgt (hd n).
  by rewrite hneg oppr_ge0 leNgt ltr0n /= subrr.
have hcov : `](-1)%R,0%R[ `<=` \bigcup_(k in G) stieltjes_interval_set k.
  move=> x; rewrite /= in_itv /= => /andP[hx0 hx1].
  have hp : (0 < -x)%R by lra.
  have [n hn] := positive_reciprocal_nat_small hp.
  exists (j n); first by exists n.
  rewrite /stieltjes_interval_set /j /stieltjes_interval_index /= in_itv /=.
  apply/andP; split; first lra.
  by rewrite ltrNr; exact: hn.
rewrite (@stieltjes_caratheodory_all_scales R g +oo hg (ltry 0%R) `](-1)%R,0%R[).
apply/eqP; rewrite eq_le (metric_scale_envelope_nonnegative
  (stieltjes_caratheodory_scale_specification g +oo)) andbT.
have hbound := @metric_scale_envelope_lower R [the metricType R of real_line_metric R]
  (stieltjes_open_intervals R) (@stieltjes_interval_set R) (stieltjes_interval_cost g)
  +oo (stieltjes_caratheodory_scale g +oo) (stieltjes_caratheodory_scale_specification g +oo)
  `](-1)%R,0%R[ G hG (fun _ _ => leey _) hcov.
by rewrite (nonnegative_sum_zero hz) in hbound.
Qed.

(** Source for [empty_borel_partition_oscillation_regression]:
    empty-family boundary of Federer 2.10.8, p. 175. Alternate
    the empty partition and the partition containing the empty
    set. All mesh bounds and the cost limit remain valid, even
    though the empty-family diameter supremum is negative infinity.
    This checks the explicitly more general eventual-mesh form. *)
Example empty_borel_partition_oscillation_regression (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c) :
  let H := fun n => if odd n then [set (@set0 X)] else set0 in
  extended_order_limit (fun n => borel_partition_cost c (H n)) 0.
Proof.
move=> H.
have hH n : is_borel_partition set0 (H n).
  rewrite /H; case: ifP=> _; last exact: borel_partition_empty.
  apply: borel_partition_singleton; exact: open_borel_set open0.
have hfine (e : R) : (0<e)%R -> exists N, forall n, (N<=n)%N ->
    forall B, H n B -> extended_metric_diameter B<=e%:E.
  move=> he; exists 0%N=> n _ B; rewrite /H; case: ifP=> _; last by [].
  move=> ->; rewrite extended_metric_diameter_empty lee_fin; exact: ltW he.
have hl := @borel_partition_cost_convergence_fine R X c hc set0 H hH hfine.
by rewrite (measure_empty (borel_caratheodory_is_measure hc)) in hl.
Qed.

(** Source for [infinite_counting_partition_supremum_regression]:
    infinite-value boundary of Federer 2.10.8, p. 175.
    For the actual counting cost, an infinite Borel target has
    infinite supremum of Borel partition sums. No finite-value
    reduction is permitted in the supremum formula. *)
Example infinite_counting_partition_supremum_regression (R : realType) (X : metricType R)
    (D A : set X) : countable D -> dense D -> borel_set A -> infinite_set A ->
  extended_real_sup (borel_partition_cost_values (@counting_measure R X) A) = +oo.
Proof.
move=> hD hden hA hinf.
pose c := @counting_measure R X.
have hm : is_measure c := counting_measure_is_measure R X.
have hc : is_borel_cover_cost c.
  constructor.
  - move=> B _; exact: (@measure_nonnegative R X c hm B).
  - move=> J G S B hG _ _ hcover; exact: (@measure_indexed_cover R X J c hm B G S hG hcover).
rewrite -(@borel_partition_cost_formula R X c hc D A hD hden hA).
apply/eqP; rewrite eq_le leey /=.
have hb := @borel_caratheodory_cost_bound R X c hc A hA.
by rewrite /c (@counting_measure_infinite R X A hinf) in hb.
Qed.

(** Source for [vanishing_normalizer_limit_regression]: local
    boundary regression for removing beta factors in Federer
    2.10.9, p. 175. Positive normalizers tending to zero
    do not permit that step: (n+1)^-1 times (n+1) is one,
    although (n+1) does not tend to one. The actual beta
    limit is strictly positive, as required in the theorem. *)
Example vanishing_normalizer_limit_regression (R : realType) :
  extended_order_limit (fun n => (((n.+1)%:R : R)^-1)%:E) 0 /\
  (forall n, (((n.+1)%:R : R)^-1)%:E*((n.+1)%:R : R)%:E = 1) /\
  ~ extended_order_limit (fun n => ((n.+1)%:R : R)%:E) 1.
Proof.
split; first exact: reciprocal_natural_order_limit.
split.
- move=> n; rewrite -EFinM mulVf //; by rewrite pnatr_eq0.
- move=> hl.
  have h12 : (1 : \bar R)<(2 : R)%:E by rewrite lte_fin ltr1n.
  have [N hN] := hl.2 (2 : R)%:E h12.
  have hn := hN (N+2)%N (leq_addr 2 N).
  have hNat : (2<=(N+2).+1)%N := leq_trans (leq_addl N 2) (leqnSn (N+2)).
  have hge : (((2%N)%:R : R)<=((N+2).+1)%:R)%R by rewrite ler_nat.
  have hb := le_lt_trans (hge : (2 : R)%:E<=((N+2).+1%:R : R)%:E) hn.
  by rewrite ltxx in hb.
Qed.

(** Source for [hausdorff_cost_partition_hypothesis_regression]:
    concrete real-line witness for Federer's warning in
    2.10.9, p. 175: the Hausdorff degree-one cost fails
    the covering hypothesis of the Borel-partition theorem.
    The endpoints zero and one are covered by their two
    singleton Borel sets, each of zero cost. *)
Example hausdorff_cost_partition_hypothesis_regression (R : realType) :
  ~ is_borel_cover_cost (@hausdorff_diameter_cost R [the metricType R of real_line_metric R] 1).
Proof.
apply: (@hausdorff_length_cost_not_borel_cover_cost R [the metricType R of real_line_metric R] 0%R 1%R).
by rewrite real_line_metric_distanceE sub0r normrN normr1 ltr01.
Qed.

(** Source for [constant_map_positive_degree_multiplicity_regression]:
    zero-Lipschitz-bound regression for the integer-degree
    Hausdorff case of Federer 2.10.11, p. 176. The
    multiplicity may be infinite at the image point and
    the source may have infinite measure; the actual
    integral is nevertheless zero in every positive degree. *)
Example constant_map_positive_degree_multiplicity_regression (R : realType)
    (X Y : metricType R) (y0 : Y) (m : nat) (D A : set X) :
  is_complete_metric_space X -> countable D -> dense D -> borel_set A ->
  let beta := @hausdorff_measure R Y m.+1 in
  let F := partial_function_total
    (fun y => (@mapping_multiplicity R X Y (fun _ => y0) A y : extended_real_line R)) in
  is_measure_integral beta F 0.
Proof.
move=> hX hD hden hA beta F.
have hf : is_metric_lipschitz_bound setT (fun _ : X => y0) 0%R.
  split; first exact: lexx.
  by move=> x z _ _; rewrite mdistxx mul0r.
have [hi hb] := @lipschitz_hausdorff_multiplicity_integer_bound R X Y
  (fun _ => y0) 0%R m.+1 D A hX hD hden hf hA.
rewrite exprS mul0r mul0e in hb.
have hn := @nonnegative_total_integral_value_ge0 R Y beta
  (@hausdorff_measure_is_measure R Y m.+1)
  (fun y => (@mapping_multiplicity R X Y (fun _ => y0) A y : extended_real_line R)) _
  (fun y => @mapping_multiplicity_nonnegative R X Y (fun _ => y0) A y) hi.
have he : measure_lower_integral beta F=0 by apply/eqP; rewrite eq_le hb hn.
by rewrite -he.
Qed.

(** Source for [constant_map_zero_degree_multiplicity_regression]:
    zero-degree boundary in the integer-degree specialization
    of Federer 2.10.11, p. 176. A constant map still has
    the counting-multiplicity bound with factor 0^0=1;
    a zero Lipschitz constant must not force this factor to zero. *)
Example constant_map_zero_degree_multiplicity_regression (R : realType)
    (X Y : metricType R) (y0 : Y) (D A : set X) :
  is_complete_metric_space X -> countable D -> dense D -> borel_set A ->
  let beta := @hausdorff_measure R Y 0 in
  let F := partial_function_total
    (fun y => (@mapping_multiplicity R X Y (fun _ => y0) A y : extended_real_line R)) in
  is_measure_integral beta F (measure_lower_integral beta F) /\
  measure_lower_integral beta F<=@hausdorff_measure R X 0 A.
Proof.
move=> hX hD hden hA beta F.
have hf : is_metric_lipschitz_bound setT (fun _ : X => y0) 0%R.
  split; first exact: lexx.
  by move=> x z _ _; rewrite mdistxx mul0r.
have hh := @lipschitz_hausdorff_multiplicity_integer_bound R X Y
  (fun _ => y0) 0%R 0 D A hX hD hden hf hA.
by rewrite expr0 mul1e in hh.
Qed.

(** Source for [disconnected_zero_length_positive_diameter_regression]:
    local boundary example for Federer 2.10.12, p. 176.
    The real two-point set {0,1} has Hausdorff length zero
    and diameter at least one, so the connectedness hypothesis
    cannot be dropped. This is not an erratum correction. *)
Example disconnected_zero_length_positive_diameter_regression (R : realType) :
  let A : set (real_line_metric R) := [set 0%R; 1%R] in
  @hausdorff_measure R [the metricType R of real_line_metric R] 1 A=0 /\
  (1 : \bar R)<=extended_metric_diameter A.
Proof.
move=> A; split.
- apply: (@hausdorff_positive_degree_countable_zero R [the metricType R of real_line_metric R] 1 A).
  + exact: ltn0Sn.
  + exact: finite_set_countable (finite_set2 _ _).
- have hd := @metric_diameter_upper R [the metricType R of real_line_metric R] A _
    (extended_metric_diameter_specification A) 1%R 0%R
    (or_intror (erefl _)) (or_introl (erefl _)).
  by rewrite real_line_metric_distanceE subr0 normr1 in hd.
Qed.

(** Source for [connected_unbounded_real_line_regression]:
    infinite-value regression for Federer 2.10.12, p. 176.
    The connected whole real line has infinite diameter,
    so the proved bound forces its actual H1 measure
    to be infinite, without a finite-measure premise. *)
Example connected_unbounded_real_line_regression (R : realType) :
  @hausdorff_measure R [the metricType R of real_line_metric R] 1 setT=+oo.
Proof.
pose X := [the metricType R of real_line_metric R].
have hcon : connected (@setT R^o).
  apply/(proj2 (connected_intervalP _)); by move=> x y hx hy z hz.
have hd0 := metric_diameter_nonnegative (extended_metric_diameter_specification (@setT X)).
have hd : extended_metric_diameter (@setT X) = +oo.
  case he: (extended_metric_diameter (@setT X))=> [r| |]; last by move: hd0; rewrite he.
  - have hr0 : (0<=r)%R by move: hd0; rewrite he lee_fin.
    have hp : (0<=r+1)%R := addr_ge0 hr0 ler01.
    have hb := @metric_diameter_upper R X setT _
      (extended_metric_diameter_specification (@setT X)) (r+1)%R 0%R I I.
    rewrite he real_line_metric_distanceE subr0 (ger0_norm hp) lee_fin in hb.
    exfalso; have hr : (r<r+1)%R by rewrite ltrDl ltr01.
    have hbad := lt_le_trans hr hb; by rewrite ltxx in hbad.
  - by [].
have hb := @federer_2_10_12 R X setT hcon.
rewrite hd in hb; by apply/eqP; rewrite eq_le leey hb.
Qed.

(** Source for [constant_curve_length_multiplicity_regression]: boundary
    regression for Federer 2.10.13, p. 177. A constant curve
    on a nondegenerate interval has zero variation and actual
    multiplicity integral zero, despite its nontrivial constant fibre. *)
Example constant_curve_length_multiplicity_regression (R : realType) (Y : metricType R)
    (c : Y) (a b : R) : (a<b)%R ->
  is_measure_integral (@hausdorff_measure R Y 1)
    (partial_function_total (fun y => (@mapping_multiplicity R
      [the choiceType of real_line_metric R] Y (fun _ => c) `[a,b] y : extended_real_line R))) 0.
Proof.
move=> hab.
have hv : curve_variation (fun _ : R => c) a b=0.
  apply/eqP; rewrite eq_le (curve_variation_nonnegative _ (ltW hab)) andbT.
  have hb := @lipschitz_curve_variation_bound R Y (fun _ => c) 0%R a b
    (fun t u => ltac:(by rewrite mdistxx mul0r)).
  by rewrite mul0r in hb.
have hc : continuous (fun _ : real_line_metric R => c).
  by move=> x; exact: cvg_cst.
have hi := @federer_2_10_13_length R Y (fun _ => c) a b hc hab.
by rewrite hv in hi.
Qed.

(** Source for [retraced_curve_length_multiplicity_regression]: regression
    for Federer 2.10.13, p. 177. The real curve t -> |t|
    on [-1,1] retraces [0,1]. Its actual multiplicity integral
    is two although its endpoint images agree; this checks that
    the theorem integrates multiplicity rather than image length. *)
Example retraced_curve_length_multiplicity_regression (R : realType) :
  is_measure_integral (@hausdorff_measure R [the metricType R of real_line_metric R] 1)
    (partial_function_total (fun y => (@mapping_multiplicity R
      [the choiceType of real_line_metric R] [the choiceType of real_line_metric R]
      (fun t : real_line_metric R => (`|t|)%R)
      (`[((-1)%R : R),(1%R : R)] : set (real_line_metric R)) y : extended_real_line R))) 2.
Proof.
pose Y := [the metricType R of real_line_metric R].
pose g (t : Y) : Y := (`|t|)%R.
have hlip x y : (mdist (g x) (g y)<=mdist x y)%R.
  have hb := @distance_from_point_nonexpanding R Y 0%R x y.
  by rewrite !real_line_metric_distanceE !sub0r !normrN in hb.
have hc : continuous g.
  apply: (@metric_fixed_lipschitz_continuous R Y Y g 1 ler01)=> x y.
  by rewrite mul1r; exact: hlip.
have hpart : is_variation_partition ((-1)%R : R) 1%R [:: (-1)%R; 0%R; 1%R].
  split; first by rewrite /= lerN10 ler01.
  by [].
have hlow : 2<=curve_variation g ((-1)%R) 1%R.
  have hh : (chain_sum g [:: (-1)%R; 0%R; 1%R])%:E<=curve_variation g ((-1)%R) 1%R.
    apply: extended_real_sup_upper; by exists [:: (-1)%R; 0%R; 1%R].
  by rewrite /= /g !normrN !normr1 !normr0 !real_line_metric_distanceE
    !subr0 !sub0r !normrN !normr1 addr0 in hh.
have hhigh := @lipschitz_curve_variation_bound R Y g 1%R ((-1)%R) 1%R
  (fun x y => ltac:(by rewrite mul1r -real_line_metric_distanceE; exact: hlip)).
have htwo : ((1*(1-(-1)))%R : R)%:E= 2 by rewrite mul1r opprK.
rewrite htwo in hhigh.
have hv : curve_variation g ((-1)%R) 1%R= 2 by apply/eqP; rewrite eq_le hhigh hlow.
have hab : ((-1 : R)<1)%R by lra.
have hi := @federer_2_10_13_length R Y g ((-1)%R) 1%R hc hab.
by rewrite hv in hi.
Qed.

(** Source for [isolated_curve_spike_both_jumps_regression]: local
    regression for both upper-limit terms of Federer 2.10.14,
    p. 177. A real curve equal to one at x and zero
    elsewhere has right and left jumps both equal to one. *)
Example isolated_curve_spike_both_jumps_regression (R : realType) (x : R) :
  let g (t : R) : real_line_metric R := if t==x then 1%R else 0%R in
  curve_right_jump_size g x= 1 /\ curve_left_jump_size g x= 1.
Proof.
move=> g.
have hconst t : t<>x -> g t=0%R.
  move=> htx; rewrite /g; case: ifP=> // /eqP he; exfalso; exact: htx he.
have hval : g x= 1%R by rewrite /g eqxx.
split; rewrite /curve_right_jump_size /curve_left_jump_size
  (@punctured_constant_curve_jump R [the metricType R of real_line_metric R] g x 0%R _ hconst)
  hval real_line_metric_distanceE sub0r normrN normr1; by [].
Qed.

(** Source for [left_endpoint_curve_spike_retraction_regression]:
    local endpoint regression for the ranges [a,b) and (a,b]
    in Federer 2.10.14, p. 177. A spike at a contributes
    its inward right jump; the retracted exterior left jump is zero. *)
Example left_endpoint_curve_spike_retraction_regression (R : realType) (a b : R) :
  (a<b)%R ->
  let g (t : R) : real_line_metric R := if t==a then 1%R else 0%R in
  curve_right_jump_size (g \o @segment_retraction R a b) a= 1 /\
  curve_left_jump_size (g \o @segment_retraction R a b) a=0.
Proof.
move=> hab g; have hj := @isolated_curve_spike_both_jumps_regression R a.
split.
- by rewrite (@curve_right_jump_retracted R [the metricType R of real_line_metric R] g a b a (ltW hab)) lexx hab /=; exact: hj.1.
- by rewrite (@curve_left_jump_retracted R [the metricType R of real_line_metric R] g a b a (ltW hab)) ltxx.
Qed.

(** Source for [right_endpoint_curve_spike_retraction_regression]:
    local endpoint regression for Federer 2.10.14, p. 177.
    At b the inward left jump is retained and the exterior
    right jump is excluded, opposite to the convention at a. *)
Example right_endpoint_curve_spike_retraction_regression (R : realType) (a b : R) :
  (a<b)%R ->
  let g (t : R) : real_line_metric R := if t==b then 1%R else 0%R in
  curve_right_jump_size (g \o @segment_retraction R a b) b=0 /\
  curve_left_jump_size (g \o @segment_retraction R a b) b= 1.
Proof.
move=> hab g; have hj := @isolated_curve_spike_both_jumps_regression R b.
split.
- by rewrite (@curve_right_jump_retracted R [the metricType R of real_line_metric R] g a b b (ltW hab)) ltxx andbF.
- by rewrite (@curve_left_jump_retracted R [the metricType R of real_line_metric R] g a b b (ltW hab)) hab lexx /=; exact: hj.2.
Qed.

(** Source for [continuous_curve_zero_jump_formula_regression]:
    regression reducing the corrected formula of Federer 2.10.14,
    p. 177, to the length identity of 2.10.13, p. 177.
    Every one-sided jump is zero for a continuous curve, even
    when its variation and upper multiplicity integral are infinite. *)
Example continuous_curve_zero_jump_formula_regression (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : continuous (g : real_line_metric R -> Y) -> (a<b)%R ->
  curve_interval_jump_budget g a b=0 /\
    curve_variation g a b=curve_upper_multiplicity_integral g a b.
Proof.
move=> hc hab.
have hz : curve_interval_jump_budget g a b=0.
  rewrite /curve_interval_jump_budget !curve_jump_measure_sum.
  have hr : nonnegative_sum (`[a,b[ : set (real_line_metric R)) (curve_one_sided_jump g true)=0.
    apply: nonnegative_sum_zero=> x hx; exact: curve_continuous_one_sided_jump_zero (hc x).
  have hl : nonnegative_sum (`]a,b] : set (real_line_metric R)) (curve_one_sided_jump g false)=0.
    apply: nonnegative_sum_zero=> x hx; exact: curve_continuous_one_sided_jump_zero (hc x).
  by rewrite hr hl add0e.
split=> //; by rewrite (@metric_curve_variation_jump_formula R Y g a b hab) hz adde0.
Qed.

(** Source for [empty_projection_multiplicity_integral_regression]:
    empty-set regression for g(p) in Federer 2.10.15, p. 178.
    The actual integral is zero for every projection, including
    the supporting zero-dimensional empty-product convention. *)
Example empty_projection_multiplicity_integral_regression (R : realType) (n m : nat)
    (p : orthogonal_projection_metric_space R n m) :
  projection_multiplicity_integral set0 p=0.
Proof.
have hA : borel_set (@set0 (inner_metric_space (@euclidean_inner_productP R n))).
  exact: open_borel_set open0.
have hi := projection_multiplicity_integral_specification p hA.
have hi0 : is_measure_integral (@euclidean_lebesgue_measure R m)
    (projection_multiplicity_integrand set0 p) 0.
  apply: (measure_almost_zero_integral (@euclidean_lebesgue_is_measure R m)).
  apply: (@measure_almost_everywhere_mono R
    [the choiceType of (inner_metric_space (@euclidean_inner_productP R m) : Type)]
    _ (@euclidean_lebesgue_is_measure R m) setT _ _
    (measure_almost_everywhere_true (@euclidean_lebesgue_is_measure R m)))=> y _.
  exact: mapping_multiplicity_empty.
exact: measure_integral_unique hi hi0.
Qed.

(** Source for [empty_integral_geometric_multiplicity_infinity_regression]:
    empty-set and infinity-exponent regression for Federer 2.10.15,
    p. 178. Both the actual multiplicity-integral infinity norm
    and the integral-geometric measure vanish. The theorem also
    supplies the measurability needed by the norm specification. *)
Example empty_integral_geometric_multiplicity_infinity_regression
    (R : realType) (n m : nat) (hmn : (m<=n)%N) : (0<m)%N ->
  nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
    (projection_multiplicity_integral (m:=m)
      (@set0 (inner_metric_space (@euclidean_inner_productP R n)))) +oo=0 /\
  @integral_geometric_measure R n m hmn +oo set0=0.
Proof.
move=> hmpos.
have hA : borel_set (@set0 (inner_metric_space (@euclidean_inner_productP R n))).
  exact: open_borel_set open0.
have hc := @federer_2_10_15 R n m hmn set0 hmpos hA.
have hn := @nonnegative_extended_norm_zero_iff R
  (orthogonal_projection_metric_space R n m) _ (@theta_star_is_measure R n m hmn)
  (projection_multiplicity_integral (m:=m) (@set0 (inner_metric_space (@euclidean_inner_productP R n))))
  +oo (fun p => projection_multiplicity_integral_nonnegative p hA) (leey 1) hc.2.1.1.
split.
- apply: hn.2; apply: (@measure_almost_everywhere_mono R
    (orthogonal_projection_metric_space R n m) _ (@theta_star_is_measure R n m hmn)
    setT _ _ (measure_almost_everywhere_true (@theta_star_is_measure R n m hmn)))=> p _.
  exact: empty_projection_multiplicity_integral_regression.
- exact: measure_empty (@integral_geometric_measure_is_measure R n m hmn +oo (leey 1)).
Qed.


(** Source for [empty_affine_slice_count_regression]: empty-set
    regression for the first affine formula of Federer
    2.10.16, p. 178. Every actual affine slice has zero
    points; zero-dimensional planes are included. *)
Example empty_affine_slice_count_regression (R : realType) (n d : nat)
    (W : affine_subspace_carrier (R_n R n) d) : affine_slice_count set0 W=0.
Proof.
rewrite /affine_slice_count set0I.
exact: measure_empty (counting_measure_is_measure R _).
Qed.

(** Source for [empty_affine_geometric_slice_regression]: empty-set
    regression for the middle formula of Federer 2.10.16,
    p. 178. The actual ambient slice measure vanishes,
    including the supporting zero-degree convention. *)
Example empty_affine_geometric_slice_regression (R : realType) (n d r : nat)
    (hrn : (r<=n)%N) (W : affine_subspace_carrier (R_n R n) d) :
  affine_integral_geometric_slice hrn set0 W=0.
Proof.
rewrite /affine_integral_geometric_slice set0I.
exact: measure_empty (@integral_geometric_measure_is_measure R n r hrn 1 (lexx _)).
Qed.

(** Source for [zero_degree_projection_normal_jacobian_regression]:
    empty-normal-block regression for the coordinate proof
    of Federer 2.10.16, p. 178. The degree-zero top
    exterior norm is one, consistent with the empty product. *)
Example zero_degree_projection_normal_jacobian_regression (R : realType) n
    (p : orthogonal_projection_metric_space R n 0) :
  euclidean_normal_jacobian (euclidean_projection_linear p)= 1%R.
Proof. exact: euclidean_projection_normal_jacobian_unit. Qed.

(** Source for [singular_infinite_multiplicity_regression]: singular-
    map and infinite-integral regression for the middle formula
    of Federer 2.10.16, p. 178. A singular postcomposition
    has zero count integral even when the original integral
    is infinite, by the null-image law of 2.7.16, p. 135. *)
Example singular_infinite_multiplicity_regression (R : realType) (X : metricType R) m
    (f : X -> inner_metric_space (@euclidean_inner_productP R m))
    (K : {linear R_n R m -> R_n R m}) (A : set X) :
  is_complete_metric_space X -> (exists D : set X, countable D /\ dense D) ->
  continuous f -> borel_set A -> euclidean_det K=0%R ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y => (@mapping_multiplicity R X _ f A y : extended_real_line R))) +oo ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y => (@mapping_multiplicity R X _ (fun x => K (f x)) A y : extended_real_line R))) 0.
Proof.
move=> hX hsep hf hA hK hi.
have hh := @linear_postcomposition_multiplicity_integral R X m f K A +oo hX hsep hf hA hi.
by rewrite hK normr0 mul0e in hh.
Qed.


(** Source for [density_quotient_boundary_regression]: zero- denominator and
    infinite-pair regression for the correction to Federer 2.10.17(2)–(3),
    p. 179 The original partial division and the infinity/infinity domain
    remain unchanged. *)
Example density_quotient_boundary_regression (R : realType) :
  caratheodory_density_divide (0 : \bar R) 0=Some 0 /\
  caratheodory_density_divide (1 : \bar R) 0=Some +oo /\
  caratheodory_density_divide (+oo : \bar R) +oo=None /\
  extended_divide (0 : \bar R) 0 = None.
Proof.
split; first exact: caratheodory_density_divide_zero_zero.
split; first by apply: caratheodory_density_divide_positive_zero; rewrite lte_fin ltr01.
split; [exact: caratheodory_density_divide_infinities|exact: extended_divide_zero].
Qed.

(** Source for [density_partial_counterexample_regression]: local
    counterexample regression for the printed partial-quotient 2.10.17(2),
    p. 179. The original density is one and the corrected density is
    infinity; the printed measure bound fails. *)
Example density_partial_counterexample_regression (R : realType) :
  @covering_upper_limit R [the metricType R of real_line_metric R] (fun x S => S x)
    (subsingleton_point_ratio R (0%R : R)) (0%R : R)= 1 /\
  @covering_upper_limit R [the metricType R of real_line_metric R] (fun x S => S x)
    (caratheodory_density_function (point_mass R (0%R : R))
      (@subsingleton_cover_cost R R) [set (0%R : R)]) (0%R : R) = +oo /\
  (2 : R)%:E*@subsingleton_cover_measure R [the metricType R of real_line_metric R] [set (0%R : R)]<
    point_mass R (0%R : R) [set (0%R : R)].
Proof.
split; first exact: subsingleton_point_ratio_real_upper_one.
split; first exact: corrected_subsingleton_point_density_infinite.
exact: (printed_caratheodory_density_bound_false R).2.2.2.2.2.2.
Qed.

(** Source for [infinite_self_contraction_regression]: finiteness regression
    for the null-set argument of Federer 2.10.17(3), p. 179 A positive
    factor below one still leaves infinity unchanged, so the
    finite-approximation hypothesis cannot be dropped from this step. *)
Example infinite_self_contraction_regression (R : realType) :
  (0<(1/2 : R)<1)%R /\
  ((+oo : \bar R)<=(1/2 : R)%:E * +oo) /\ (+oo : \bar R)!=0.
Proof.
have hh : (0<(1/2 : R))%R by lra.
split; first by apply/andP; split; lra.
split; last by [].
have hhE : 0<(1/2 : R)%:E by rewrite lte_fin.
by rewrite (gt0_muley hhE).
Qed.

(** Source for [diameter_enlargement_empty_regression]: empty-set
    boundary for the displayed enlargement in Federer
    2.10.18, p. 180. No set meets the empty set,
    even though its diameter is zero. *)
Example diameter_enlargement_empty_regression (R : realType) (X : metricType R)
    (F : set (set X)) : diameter_enlargement F set0=set0.
Proof.
apply/seteqP; split=> [x [T [hT [hmeet hdiam]] hx]|x []].
exfalso; apply: hmeet; exact: setI0.
Qed.

(** Source for [diameter_enlargement_singleton_regression]: zero-
    diameter nonempty boundary for the enlargement of
    2.10.18, p. 180. The selection proof permits
    zero diameter and only excludes empty members. *)
Example diameter_enlargement_singleton_regression (R : realType) (X : metricType R) (a : X) :
  diameter_enlargement [set S : set X | S=[set a]] [set a]=[set a] /\
  extended_metric_diameter [set a]=0.
Proof.
split; last exact: extended_metric_diameter_singleton.
apply/seteqP; split.
- by move=> x [T [-> [_ _]] hx].
- move=> x hx; exact: (@diameter_enlargement_contains R X [set S : set X | S=[set a]]
    [set a] erefl x hx).
Qed.

(** Source for [strict_growth_original_division_regression]: original-
    quotient boundary for 2.10.18, p. 180. Its strict growth excludes zero
    costs, making a zero numerator have an actual defined value zero *)
Example strict_growth_original_division_regression (R : realType) (a b : \bar R) (eta : R) :
  0<=a -> 0<=b -> b<eta%:E*a -> eta%:E*a < +oo ->
  extended_divide 0 a=Some 0.
Proof.
move=> ha hb hs hf.
have [_ [hp hfin]] := strict_enlargement_positive_finite_cost ha hb hs hf.
have hn : a \is a fin_num by rewrite (ge0_fin_numE (ltW hp)).
by rewrite /extended_divide (gt_eqF hp) hn orbT mul0e.
Qed.

(** Source for [infinite_self_expansion_regression]: finiteness boundary for
    the cancellation in 2.10.18(3), p. 181 Infinity survives a factor
    greater than one. *)
Example infinite_self_expansion_regression (R : realType) :
  (2 : R)%:E*(+oo : \bar R)=+oo /\ (+oo : \bar R)!=0.
Proof.
split; last by [].
have hp : 0<(2 : R)%:E by rewrite lte_fin ltr0n.
exact: gt0_muley hp.
Qed.

(** Source for [zero_measure_metric_density_regression]: zero- measure
    boundary for the upper and lower metric densities in Federer 2.10.19, p.
    181 Only positive radii affect either limit, in every integer degree. *)
Example zero_measure_metric_density_regression (R : realType) (X : metricType R) m (x : X) :
  upper_metric_density m (fun _ : set X => (0 : \bar R)) x=0 /\
  lower_metric_density m (fun _ : set X => (0 : \bar R)) x=0.
Proof.
have hf r : (0<r)%R -> metric_ball_density m (fun _ : set X => (0 : \bar R)) x r=0.
  by move=> _; rewrite /metric_ball_density mul0e.
have he := @positive_radius_limits_congr R (metric_ball_density m (fun _ : set X => (0 : \bar R)) x)
  (fun _ : R => (0 : \bar R)) hf.
have hc := @positive_radius_limits_constant R 0.
split; [exact: eq_trans he.1 hc.1|exact: eq_trans he.2 hc.2].
Qed.

(** Source for [point_mass_zero_degree_density_regression]: degree- zero
    normalization alpha(0)= 1 and actual common density in 2.10.19, p. 181
    Every positive centred ball contains the atom, so both densities are
    exactly one. *)
Example point_mass_zero_degree_density_regression (R : realType) (X : metricType R) (a : X) :
  partial_function_graph (metric_density 0 (point_mass R a)) a 1.
Proof.
have hf r : (0<r)%R -> metric_ball_density 0 (point_mass R a) a r= 1.
  move=> hr; rewrite metric_ball_density_zero_degree; apply: point_mass_in.
  by rewrite /metric_closed_ball /= mdistxx; exact: ltW hr.
have he := @positive_radius_limits_congr R (metric_ball_density 0 (point_mass R a) a)
  (fun _ : R => (1 : \bar R)) hf.
have hc := @positive_radius_limits_constant R 1.
rewrite /metric_density /=; split; [exact: eq_trans he.1 hc.1|exact: eq_trans he.2 hc.2].
Qed.

(** Source for [zero_diameter_spherical_enlargement_regression]: diameter-
    zero boundary for the containing-ball repair used in Federer
    2.10.19(3)–(5), p. 181 The sealed witness retains a positive-radius ball
    and zero positive-degree cost, without computing through its chosen
    centre or radius. *)
Example zero_diameter_spherical_enlargement_regression (R : realType) (X : metricType R)
    m (S : set X) : is_positive_metric_closed_ball S -> extended_metric_diameter S=0 ->
  is_positive_metric_closed_ball (@spherical_enlargement R X m.+1 S) /\
  extended_metric_diameter (@spherical_enlargement R X m.+1 S)=0 /\
  hausdorff_diameter_cost m.+1 (@spherical_enlargement R X m.+1 S)=0.
Proof.
move=> hS hd.
have hE := @spherical_enlargement_specification R X m.+1.
have hmem := @weak_enlargement_member R X (@is_positive_metric_closed_ball R X)
  (@hausdorff_diameter_cost R X m.+1) (@spherical_enlargement R X m.+1)
  (spherical_enlargement_control R m.+1) hE S hS.
have hb := @weak_enlargement_diameter R X (@is_positive_metric_closed_ball R X)
  (@hausdorff_diameter_cost R X m.+1) (@spherical_enlargement R X m.+1)
  (spherical_enlargement_control R m.+1) hE S hS.
rewrite hd mule0 in hb.
have he : extended_metric_diameter (@spherical_enlargement R X m.+1 S)=0.
  apply/eqP; by rewrite eq_le hb (metric_diameter_nonnegative (extended_metric_diameter_specification _)).
split=> //; split=> //.
by rewrite /hausdorff_diameter_cost he hausdorff_power_cost_finite exprS mul0r mulr0.
Qed.

(** Source for [empty_completed_hausdorff_zero_degree_regression]: empty-
    cover boundary for the proof of 2.10.19(2),
    p. 181. The degree-zero empty generator has
    auxiliary cost one but its actual scale measure
    is still zero, at every cutoff including zero. *)
Example empty_completed_hausdorff_zero_degree_regression (R : realType) (X : metricType R) delta :
  @hausdorff_diameter_cost R X 0 set0= 1 /\
  metric_scale_envelope (fun j : all_sets_hausdorff_generators X => val j)
    (fun j => hausdorff_diameter_cost 0 (val j)) delta set0=0.
Proof.
split; first exact: hausdorff_diameter_cost_zero_degree.
have hc (j : all_sets_hausdorff_generators X) : 0<=hausdorff_diameter_cost 0 (val j).
  exact: hausdorff_diameter_cost_nonnegative.
have hm := @metric_scale_envelope_measure R X (@all_sets_hausdorff_generators R X)
  (fun j => val j) (fun j => hausdorff_diameter_cost 0 (val j)) delta hc.
exact: measure_empty hm.
Qed.

(** Source for [zero_cost_spherical_ball_ratio_regression]: zero- cost
    covering-quotient boundary in the repair of Federer 2.10.19(3)–(5), p.
    181 A positive-radius ball can have zero diameter. *)
Example zero_cost_spherical_ball_ratio_regression (R : realType) (X : metricType R)
    m (a : X) (r : R) : (0<r)%R -> extended_metric_diameter (metric_closed_ball a r)=0 ->
  extended_divide (point_mass R a (metric_closed_ball a r))
    (hausdorff_diameter_cost m.+1 (metric_closed_ball a r))=None /\
  caratheodory_density_divide (point_mass R a (metric_closed_ball a r))
    (hausdorff_diameter_cost m.+1 (metric_closed_ball a r))=Some +oo.
Proof.
move=> hr hd.
have hc : hausdorff_diameter_cost m.+1 (metric_closed_ball a r)=0.
  by rewrite /hausdorff_diameter_cost hd hausdorff_power_cost_finite exprS mul0r mulr0.
have ha : metric_closed_ball a r a by rewrite /metric_closed_ball /= mdistxx; exact: ltW hr.
rewrite (point_mass_in R ha) hc; split; first exact: extended_divide_zero.
apply: caratheodory_density_divide_positive_zero; by rewrite lte_fin ltr01.
Qed.

(** Source for [empty_radial_mass_regression]: empty-target
    boundary in Federer 2.10.20, pp. 181–182.
    The radius limit is zero for any measure, without
    requiring measurability of other targets or finite
    mass on the ambient space. *)
Example empty_radial_mass_regression (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (a : X) : is_measure mu ->
  unbounded_radius_order_limit (fun r => mu (set0 `&` metric_closed_ball a r)) 0.
Proof.
move=> hm.
have hle := @radial_mass_supremum_le_total R X mu a set0 hm.
rewrite (measure_empty hm) in hle.
have hge := @radial_mass_le_supremum R X mu a set0 0%R.
rewrite set0I (measure_empty hm) in hge.
have he : radial_mass_supremum mu a set0=0 by apply/eqP; rewrite eq_le hle hge.
have hl := @radial_mass_has_supremum_limit R X mu a set0 hm.
by rewrite he in hl.
Qed.

(** Source for [infinite_radial_mass_regression]: infinite-
    value boundary in Federer 2.10.20, p. 182.
    The measure assigning infinity to every nonempty
    set has measurable closed balls and infinite mass
    already in every positive-radius centred ball.
    The exhaustion needs no finite-total-mass hypothesis. *)
Example infinite_radial_mass_regression (R : realType) (X : metricType R) (a : X) :
  unbounded_radius_order_limit (fun r => infinite_discrete_measure R (metric_closed_ball a r)) +oo.
Proof.
have hm := @infinite_discrete_measure_is_measure R X.
have hBall (r : R) : measure_measurable (@infinite_discrete_measure R X) (metric_closed_ball a r).
  exact: infinite_discrete_measure_measurable.
have hl := @measurable_ball_radial_continuity R X (@infinite_discrete_measure R X) a setT hm hBall.
have htotal : infinite_discrete_measure R (@setT X)=+oo.
  apply: infinite_discrete_measure_nonempty; by exists a.
have hfun : (fun r : R => infinite_discrete_measure R (setT `&` metric_closed_ball a r))=
    (fun r : R => infinite_discrete_measure R (metric_closed_ball a r)).
  by apply: funext=> r; rewrite setTI.
by rewrite hfun htotal in hl.
Qed.

(** Source for [radial_shell_closed_endpoints_regression]: endpoint
    convention of B_j in the proof of 2.10.20,
    p. 181. Adjacent shells share a sphere; only
    the separate same-parity subfamilies are separated. *)
Example radial_shell_closed_endpoints_regression (R : realType) :
  @metric_radial_shell R [the metricType R of real_line_metric R] (0%R : R) 1%R 0%N (1%R : R) /\
  @metric_radial_shell R [the metricType R of real_line_metric R] (0%R : R) 1%R 1%N (1%R : R).
Proof.
split; rewrite /metric_radial_shell /= real_line_metric_distanceE sub0r normrN normr1 !mulr1.
- by rewrite ler01 lexx.
- by rewrite lexx ler1n.
Qed.

(** Source for [compact_empty_intersection_neighborhood_regression]: empty-
    intersection boundary for the compact-neighbourhood
    step of 2.10.20, p. 182. A nonempty compact
    first term followed by empty terms eventually lies
    in the empty open neighbourhood of the intersection. *)
Example compact_empty_intersection_neighborhood_regression (R : realType) (X : metricType R) (a : X) :
  exists N, forall n : nat, (N<=n)%N -> (if n is 0%N then [set a] else set0)=set0.
Proof.
pose C (n : nat) : set X := if n is 0%N then [set a] else set0.
have hC0 : compact (C 0%N) := @compact_set1 X a.
have hCa : closed [set a] := compact_closed (@metric_hausdorff R X) (@compact_set1 X a).
have hclosed n : closed (C n) by case: n=> [|n]; [exact hCa|exact: closed0].
have hdec n m (hnm : (n<=m)%N) : C m `<=` C n.
  case: m hnm=> [|m] hnm.
  - have hn0 : n=0%N by apply/eqP; rewrite -leqn0.
    by rewrite hn0.
  - by move=> x [].
have hK : (\bigcap_n C n) `<=` set0 by move=> x hx; exact: hx 1%N I.
have [N hN] := @compact_decreasing_eventually_in_open X C set0 hC0 hclosed hdec open0 hK.
exists N=> n hn; apply/seteqP; split=> [x hx|x []]; exact: hN n hn x hx.
Qed.

(** Source for [zero_lipschitz_anchored_compact_regression]: zero-
    bound and zero-radius boundary of the anchored
    compactness assertion in Federer 2.10.21, p. 183.
    The domain is any metric space with its given point;
    no bounded compactness of the domain is required. *)
Example zero_lipschitz_anchored_compact_regression (R : realType) (X : metricType R)
    (a : X) (b : R) :
  compact (@anchored_lipschitz_functions R X [the metricType R of real_line_metric R] 0%R a b 0%R).
Proof.
exact: (@anchored_lipschitz_functions_compact R X [the metricType R of real_line_metric R]
  0%R a b 0%R (@real_line_boundedly_compact R) (lexx 0%R) (lexx 0%R)).
Qed.

(** Source for [zero_radius_hyperspace_compact_regression]: zero-
    radius extension of the compact hyperspace assertion
    in Federer 2.10.21, p. 183. Compact sets
    are still nonempty; no empty-set profile is introduced. *)
Example zero_radius_hyperspace_compact_regression (R : realType) (X : metricType R) (a : X) :
  metric_boundedly_compact X ->
  compact [set C : compact_hausdorff_space X | compact_sets_in_ball a 0%R C].
Proof. move=> hX; exact: (@compact_hausdorff_ball_compact R X a 0%R hX (lexx 0%R)). Qed.

(** Source for [singleton_compact_diameter_regression]: singleton
    boundary of the real-valued diameter map in
    Federer 2.10.21, p. 183. Taking the
    finite part preserves the actual diameter zero. *)
Example singleton_compact_diameter_regression (R : realType) (X : metricType R) (a : X) :
  let C : compact_metric_set X := exist _ [set a]
    (mem_set (conj (@compact_set1 X a) (ex_intro _ a erefl))) in
  compact_metric_diameter C=0%R.
Proof.
move=> C; rewrite /compact_metric_diameter /= extended_metric_diameter_singleton; by [].
Qed.

(** Source for [zero_error_finite_net_regression]: zero-
    error boundary of the hit-set Hausdorff estimate
    in Federer 2.10.21, p. 183. A finite
    compact set is its own zero-error hit approximation. *)
Example zero_error_finite_net_regression (R : realType) (X : metricType R)
    (C : compact_metric_set X) : finite_set (val C) ->
  exists D : compact_metric_set X, val D=val C /\ hausdorff_distance C D=0%R.
Proof.
move=> hfin.
have hcover : val C `<=` \bigcup_(z in val C) metric_closed_ball z 0%R.
  move=> x hx; exists x=> //; by rewrite /metric_closed_ball /= mdistxx.
have [D [hD hdist]] := hausdorff_finite_net_hit_bound hfin (lexx 0%R) hcover.
have he : finite_net_hit_set (val C) (val C) 0%R=val C.
  apply/seteqP; split=> x hx; first exact hx.1.
  split=> //; exists x; split=> //; by rewrite /metric_closed_ball /= mdistxx.
exists D; split; first by rewrite hD he.
apply/eqP; by rewrite eq_le hdist (hausdorff_distance_nonnegative_law
  (@hausdorff_distance_specification R X) C D).
Qed.

(** Source for [compact_diameter_cost_hypotheses_regression]:
    regression of the cost hypotheses in Federer
    2.10.22, p. 184, using diameter itself.
    Its continuity is 2.10.21, p. 183,
    and zero-diameter costs remain permitted. *)
Example compact_diameter_cost_hypotheses_regression (R : realType) (X : metricType R) :
  is_continuous_positive_compact_cost (@compact_metric_diameter R X).
Proof.
constructor.
- move=> C; have hh := metric_diameter_nonnegative (extended_metric_diameter_specification (val C)).
  by rewrite compact_metric_diameter_finite_value lee_fin in hh.
- exact: compact_diameter_map_continuous.
- by move=> C hC.
Qed.

(** Source for [positive_constant_compact_cost_regression]:
    regression of the precise hypotheses in Federer
    2.10.22, p. 184. A positive constant
    cost is permitted, including positive singleton costs;
    the formal specification must not require their vanishing. *)
Example positive_constant_compact_cost_regression (R : realType) (X : metricType R) :
  is_continuous_positive_compact_cost (fun _ : compact_metric_set X=>(1%R : R)).
Proof.
constructor.
- move=> C; exact: ler01.
- move=> C; exact: (@cvg_cst [the topologicalType of real_line_metric R] 1%R
    [the topologicalType of compact_hausdorff_space X] (nbhs C) (nbhs_filter C)).
- move=> C hC; exact: ltr01.
Qed.

(** Source for [zero_cutoff_singleton_cost_regression]: supporting
    null-generator boundary of Federer 2.10.22,
    pp. 184–185. The printed theorem uses a
    positive cutoff; its zero-cost removal lemma also
    covers cutoff zero, without artificial padding costs. *)
Example zero_cutoff_singleton_cost_regression (R : realType) (X : metricType R) (a : X) :
  let C : compact_metric_set X := exist _ [set a]
    (mem_set (conj (@compact_set1 X a) (ex_intro _ a erefl))) in
  metric_scale_envelope (fun D : compact_metric_set X=>val D)
    (fun D=>(compact_metric_diameter D)%:E) 0 (val C)=0.
Proof.
move=> C.
apply: (@compact_zero_cost_scale_null R X (@compact_metric_diameter R X)
  (@compact_diameter_cost_hypotheses_regression R X) 0 _ C (lexx 0)
  (metric_scale_envelope_specification _ _ _)).
exact: singleton_compact_diameter_regression.
Qed.

(** Source for [singleton_compact_cost_continuity_regression]:
    boundary instance of Federer 2.10.22,
    pp. 184–186, on the real line with
    diameter cost and a stationary singleton target.
    The actual cutoff measures increase to zero;
    finite zero-cost covers are included in the theorem. *)
Example singleton_compact_cost_continuity_regression (R : realType) (a delta : R) :
  (0<delta)%R ->
  extended_increases_to (fun _ : nat=>metric_scale_envelope
    (fun C : compact_metric_set [the metricType R of real_line_metric R]=>val C)
    (fun C=>(compact_metric_diameter C)%:E) delta%:E [set a]) 0.
Proof.
move=> hd.
pose X := [the metricType R of real_line_metric R].
pose cost := @compact_metric_diameter R X.
pose nu := metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>(cost C)%:E) delta%:E.
have hlim := @federer_2_10_22 R X cost (@compact_diameter_cost_hypotheses_regression R X) delta nu
  (fun _ : nat=>[set a]) (@real_line_boundedly_compact R) hd
  (metric_scale_envelope_specification _ _ _) (fun i j hij x hx=>hx).
have heq : (\bigcup_(_ : nat) [set a])=[set a].
  apply/seteqP; split; [by move=> x [j _ hx]|by move=> x hx; exists 0%N].
pose C : compact_metric_set X := exist _ [set a]
  (mem_set (conj (@compact_set1 X a) (ex_intro _ a erefl))).
have hdelta : 0<=delta%:E by rewrite lee_fin; exact: ltW hd.
have hzero := @compact_zero_cost_scale_null R X cost (@compact_diameter_cost_hypotheses_regression R X)
  delta%:E nu C hdelta (metric_scale_envelope_specification _ _ _)
  (@singleton_compact_diameter_regression R X a).
rewrite heq in hlim; change (nu [set a]=0) in hzero.
rewrite -hzero; exact hlim.
Qed.

(** Source for [empty_compact_mass_values_regression]: empty
    target boundary of Federer 2.10.23, p. 186.
    Compact subsets in its supremum include the empty
    set, although the generating family excludes it;
    the mass-value family is therefore the singleton zero. *)
Example empty_compact_mass_values_regression (R : realType) (X : topologicalType)
    (psi : set X -> \bar R) (hm : is_measure psi) :
  compact_subset_mass_values psi set0=[set 0].
Proof.
apply/seteqP; split.
- move=> b [C [hC [hCS ->]]].
  have heq : C=set0 by apply/seteqP; split=> [x hx|x []]; exact: hCS x hx.
  change (psi C=0); by rewrite heq (measure_empty hm).
- move=> b hb; have heq : b=0 := hb; rewrite heq.
  exists set0; split; first exact: compact0.
  split; first by move=> x [].
  exact: esym (measure_empty hm).
Qed.

(** Source for [positive_singleton_suslin_compact_regression]:
    singleton boundary of Federer 2.10.23,
    p. 186, for an actual final measure with
    positive constant compact costs. Singleton costs
    remain positive, and no final-mass finiteness or
    cutoff-measure regularity hypothesis is supplied. *)
Example positive_singleton_suslin_compact_regression (R : realType) (X : metricType R) (a : X) :
  metric_boundedly_compact X ->
  let psi := caratheodory_measure (fun C : compact_metric_set X=>val C)
    (fun _=>(1%R : R)%:E) in
  psi [set a]=extended_real_sup (compact_subset_mass_values psi [set a]).
Proof.
move=> hX psi.
have hS : is_suslin_set R [set a].
  apply: metric_borel_suslin; apply: closed_borel_set.
  exact: compact_closed (@metric_hausdorff R X) (@compact_set1 X a).
exact: (@federer_2_10_23 R X (fun _=>(1%R : R))
  (@positive_constant_compact_cost_regression R X) psi [set a] hX
  (caratheodory_measure_specification _ _) hS).
Qed.

(** Source for [zero_weighted_limit_regression]: zero-function
    and empty-cover boundary of 2.10.24, p. 187.
    The generator type may be empty and no positivity
    or existence of a nonempty covering family is assumed. *)
Example zero_weighted_limit_regression (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) :
  is_measure psi -> weighted_metric_limit S c psi (fun _=>0)=0.
Proof.
move=> hm; exact: weighted_metric_limit_zero hm (weighted_metric_limit_specification S c psi).
Qed.

(** Source for [single_generator_finite_weight_regression]:
    finite-real weight condition in 2.10.24, p. 186.
    A single generator contributes exactly its finite weight,
    so an infinite pointwise value is never supplied by
    silently allowing an infinite coefficient. *)
Example single_generator_finite_weight_regression (R : realType) (X : choiceType) (a : R) x :
  (0<=a)%R -> weighted_generator_sum (fun _ : unit=>@setT X) setT (fun _=>a) x=a%:E.
Proof.
move=> ha.
have he : [set j : unit | setT j /\ setT x]=[set tt].
  apply/seteqP; split=> [[] _|[] _]; by [].
rewrite /weighted_generator_sum he nonnegative_sum_singleton //; by rewrite lee_fin.
Qed.

(** Source for [infinite_null_weighted_limit_regression]:
    infinite-valued, almost-everywhere-zero boundary of
    2.10.24, pp. 186–187. Infinite f on a null
    set still has weighted limit zero via the empty
    weighted cover; every actual weight remains finite. *)
Example infinite_null_weighted_limit_regression (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (N : set X) :
  is_measure psi -> psi N=0 ->
  weighted_metric_limit S c psi (fun x=>if x \in N then +oo else 0)=0.
Proof.
move=> hm hN; pose f x := (if x \in N then +oo else 0 : \bar R).
have hdom : measure_almost_everywhere psi [set x | f x<=weighted_generator_sum S set0 (fun _=>0%R) x].
  apply: (@measure_null_subset R X psi hm _ N _ hN)=> x hx.
  apply: contrapT=> hxN; apply: hx.
  have hnx : x \notin N by apply/negP=> /set_mem hn; exact: hxN hn.
  change (is_true (f x<=weighted_generator_sum S set0 (fun _=>0%R) x)).
  rewrite /f (negbTE hnx); exact: nonnegative_sum_nonnegative.
have hcover delta : is_weighted_metric_cover S psi delta f set0 (fun _=>0%R).
  constructor; [exact: countable0|by move=> j []|by move=> j []|exact hdom].
have hL := weighted_metric_limit_specification S c psi.
apply/eqP; rewrite eq_le (weighted_metric_limit_nonnegative hL) andbT.
apply: (weighted_metric_limit_least hL)=> delta lambda hd hl.
have hh := weighted_metric_envelope_lower hl (hcover delta).
by rewrite /weighted_generator_cost nonnegative_sum_empty in hh.
Qed.

(** Source for [spherical_zero_degree_weighted_point_regression]:
    positive singleton-cost boundary of the repaired spherical
    application in 2.10.24, p. 188, with the degree-zero
    convention from 2.10.2(2), p. 171. Only bounded
    compactness is supplied to the equality theorem; the
    singleton characteristic function has weighted limit one. *)
Example spherical_zero_degree_weighted_point_regression (R : realType) (X : metricType R) (a : X) :
  metric_boundedly_compact X ->
  weighted_metric_limit (fun j : @positive_closed_metric_balls R X=>val j)
    (fun j=>hausdorff_diameter_cost 0 (val j)) (@spherical_measure R X 0)
    (fun x=>(@CharacteristicFunction.value R X [set a] x)%:E)= 1.
Proof.
move=> hX; pose psi := @spherical_measure R X 0.
pose s := @CharacteristicFunction.value R X [set a].
have hs := @CharacteristicFunction.laws R X [set a].
have hm := @spherical_measure_is_measure R X 0.
have hA : measure_measurable psi [set a].
  exact: (@borel_regular_borel_measurable R X psi hm (@spherical_measure_borel_regular R X 0) _
    (closed_borel_set (compact_closed (@metric_hausdorff R X) (@compact_set1 X a)))).
have hi := @measure_total_characteristic_integral R X psi hm [set a] s hs hA.
have he := @measure_upper_integral_unique R X psi (partial_function_total (fun x=>(s x)%:E)) _ _
  (measure_upper_integral_specification psi _) hi.2.1.
have hf x : 0<=(s x)%:E := @characteristic_extended_nonnegative R X [set a] s hs x.
rewrite (@spherical_weighted_proper_equality R X 0 _ hX hf) he.
rewrite /psi spherical_zero_counting_measure; exact: counting_singleton.
Qed.

(** Source for [weighted_restriction_opaque_regression]: interface
    regression for the auxiliary measure supporting 2.10.24,
    p. 188. Evaluation follows from its abstract supremum
    specification; reflexivity cannot compute through the opaque
    witness. This checks the project's encapsulation requirement,
    not an additional mathematical claim attributed to Federer. *)
Example weighted_restriction_opaque_regression (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> \bar R) A :
  weighted_restriction_measure S c psi f A=
    weighted_metric_limit S c psi (weighted_function_restriction f A).
Proof.
Fail reflexivity.
exact: weighted_restriction_measureE.
Qed.

(** Source for [gross_zero_dimensional_zero_input_regression]:
    zero-dimensional and zero-degree boundary of the final
    Gross application in 2.10.24, p. 188, under the
    existing empty-product convention for 2.10.4(1), p. 172.
    The actual equality theorem and zero integral recover
    weighted limit zero without a positive-dimensional premise. *)
Example gross_zero_dimensional_zero_input_regression (R : realType) :
  weighted_metric_limit
    (fun j : @borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R 0))=>val j)
    (fun j=>projected_volume_gauge 0 (val j)) (@gross_measure R 0 0)
    (fun _=>(0 : extended_real_line R))=0.
Proof.
pose X := inner_metric_space (@euclidean_inner_productP R 0).
pose mu := @gross_measure R 0 0.
have hm : is_measure mu := @gross_measure_is_measure R 0 0 (leqnn 0).
have heq := @gross_weighted_integral_equality R 0 0 (fun _=>(0 : extended_real_line R))
  (leqnn 0) (fun _=>lexx _).
rewrite heq.
have hae : measure_almost_everywhere mu [set x | partial_function_graph
    (partial_function_total (fun _ : X=>(0 : extended_real_line R))) x 0].
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=> x _; reflexivity.
have hi := @measure_almost_zero_integral R X mu hm
  (partial_function_total (fun _ : X=>(0 : extended_real_line R))) hae.
exact: (@measure_upper_integral_unique R X mu _ _ 0
  (measure_upper_integral_specification mu _) hi.2.1).
Qed.

(** Source for [integral_geometric_infinite_exponent_null_integral_regression]:
    infinity-exponent and infinite-input boundary of the final
    integral-geometric application in 2.10.24, p. 188.
    An arbitrary original-measure null set may carry an
    infinite input; the upper integral is still zero.
    No Borel hypothesis on that set is added. *)
Example integral_geometric_infinite_exponent_null_integral_regression (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (N : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @integral_geometric_measure R n m hmn +oo N=0 ->
  measure_upper_integral (@integral_geometric_measure R n m hmn +oo)
    (partial_function_total (fun x=>(if x \in N then +oo else 0 : extended_real_line R)))=0.
Proof.
move=> hN.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @integral_geometric_measure R n m hmn +oo.
pose f (x : X) := (if x \in N then +oo else 0 : extended_real_line R).
have hp : (1 : \bar R)<=+oo := leey _.
have hm : is_measure mu := @integral_geometric_measure_is_measure R n m hmn +oo hp.
have hf0 x : 0<=f x by rewrite /f; case: ifP=> _; [exact: leey|exact: lexx].
have heq := @integral_geometric_weighted_integral_equality R n m hmn +oo f hp hf0.
change (measure_upper_integral mu (partial_function_total f)=0).
have heq' : weighted_metric_limit
    (fun j : @borel_metric_sets R X=>val j) (fun j=>@integral_geometric_gauge R n m hmn +oo (val j))
    mu f=measure_upper_integral mu (partial_function_total f) := heq.
rewrite -heq'.
exact: (@infinite_null_weighted_limit_regression R X (@borel_metric_sets R X)
  (fun j=>val j) (fun j=>@integral_geometric_gauge R n m hmn +oo (val j)) mu N hm hN).
Qed.

(** Source for [infinite_grouped_weight_finite_cover_regression]:
    repeated-image boundary in the proof of 2.10.25,
    p. 189. Countably many unit source weights all
    map to the same target singleton. Their aggregate
    is infinite, but the target cost and Hausdorff
    one-dimensional measure are zero. The proved assembly
    still supplies a cover with finite real coefficients. *)
Example infinite_grouped_weight_finite_cover_regression (R : realType) (Y : metricType R) (y : Y) :
  nonnegative_sum (@setT nat) (fun _=>(1 : R)%:E)=+oo /\
  exists (H : set unit) (u : unit -> R),
    is_weighted_metric_cover (fun _ : unit=>[set y]) (@hausdorff_measure R Y 1) 1
      (fun z=>(if z \in [set y] then +oo else 0)) H u /\
    weighted_generator_cost (fun _ : unit=>(0 : \bar R)) H u=0.
Proof.
split; first exact: nonnegative_sum_infinite_constant ltr01 infinite_nat.
pose T (_ : unit) := [set y].
pose g (z : Y) := (if z \in [set y] then +oo else 0 : \bar R).
have hm := @hausdorff_measure_is_measure R Y 1.
have hdom : measure_almost_everywhere (@hausdorff_measure R Y 1)
    [set z | g z<=weighted_generator_sum (fun _ : nat=>T tt) setT (fun _=>1%R) z].
  apply: (@measure_almost_everywhere_mono R Y _ hm setT _ _
    (measure_almost_everywhere_true hm))=> z _.
  change (is_true (g z<=weighted_generator_sum (fun _ : nat=>T tt) setT (fun _=>1%R) z)).
  rewrite /g /weighted_generator_sum; case: ifP=> hz.
  - have he : [set i : nat | setT i /\ T tt z]=setT.
      apply/seteqP; split=> [i _|i _] //; split=> //; exact: (set_mem hz).
    rewrite he; rewrite (@nonnegative_sum_infinite_constant R [the choiceType of (nat : Type)]
      setT 1%R ltr01 infinite_nat); exact: lexx.
  - exact: nonnegative_sum_nonnegative.
have hzero : nonnegative_sum (@setT nat) (fun _=>(1 : R)%:E*(0 : \bar R))=0.
  apply: nonnegative_sum_zero=> i _; exact: mule0.
have hdiam (i : nat) (_ : setT i) : extended_metric_diameter (T tt)<=1.
  by rewrite /T extended_metric_diameter_singleton lee_fin ler01.
have hnull (t : unit) (_ : ((fun _ : nat=>tt) @` setT) t) (_ : (0 : \bar R)=0) :
    @hausdorff_measure R Y 1 (T t)=0.
  exact: hausdorff_positive_degree_singleton_zero (ltn0Sn 0).
have hfin : nonnegative_sum (@setT nat) (fun _=>(1 : R)%:E*(0 : \bar R))< +oo.
  rewrite hzero; exact: ltry.
have [H [u [hc hcost]]] := @weighted_generator_image_assembly R Y
  [the choiceType of (nat : Type)] [the choiceType of (Datatypes.unit : Type)] T (fun _=>0)
  (@hausdorff_measure R Y 1) setT (fun _=>tt) (fun _=>1%R) 1 g hm
  (fun _=>lexx _) (countableP _) (fun _ _=>ler01)
  hdiam hnull hfin hdom.
exists H,u; split=> //; apply/eqP.
rewrite hzero in hcost.
rewrite eq_le hcost /= /weighted_generator_cost; exact: nonnegative_sum_nonnegative.
Qed.

(** Source for [zero_lipschitz_infinite_source_fibre_regression]:
    zero-bound and infinite-source-mass boundary of 2.10.25,
    pp. 188–189. The null-image proof needs neither
    a finite source measure nor measurable fibre masses. *)
Example zero_lipschitz_infinite_source_fibre_regression (R : realType) (X Y : metricType R)
    (f : X -> Y) A k m :
  is_metric_lipschitz_bound setT f 0%R ->
  @hausdorff_measure R X (k+m.+1) A=+oo ->
  measure_upper_integral (@hausdorff_measure R Y m.+1)
    (partial_function_total (hausdorff_fibre_mass f A k))=0.
Proof.
move=> hf _; exact: zero_lipschitz_positive_degree_fibre_integral_zero hf (ltn0Sn m).
Qed.

(** Source for [zero_target_degree_fibre_bound_regression]:
    target-degree-zero boundary of 2.10.25, p. 188,
    with 0^0=1 for a zero Lipschitz bound. No
    finiteness or measurability condition on A is added. *)
Example zero_target_degree_fibre_bound_regression (R : realType) (X Y : metricType R)
    (f : X -> Y) A k :
  is_metric_lipschitz_bound setT f 0%R ->
  hausdorff_fibre_integral_condition f A k 0 ->
  measure_upper_integral (@hausdorff_measure R Y 0)
    (partial_function_total (hausdorff_fibre_mass f A k))<=
    (hausdorff_fibre_bound_constant k 0 1%R)%:E* @hausdorff_measure R X (k+0) A.
Proof.
move=> hf hc.
have hh := hausdorff_lipschitz_fibre_integral_bound hf hc.
by rewrite /hausdorff_fibre_bound_constant !expr0 in hh *.
Qed.

(** Source for [zero_budget_empty_fibre_cover_regression]:
    strict finite-cover budget in 2.10.26, p. 190.
    Even an empty fibre has no cover of cost
    strictly below zero. Thus the printed t+1/j
    slack cannot be dropped at the zero threshold. *)
Example zero_budget_empty_fibre_cover_regression (R : realType) (X Y : metricType R)
    (f : X -> Y) k (delta : \bar R) :
  fibre_open_cover_locus f set0 k delta 0=set0.
Proof.
apply/seteqP; split=> [y [G [_ [_ [_ hcost]]]]|y []].
have hh := le_lt_trans (nonnegative_sum_nonnegative G (fun S=>hausdorff_diameter_cost k S)) hcost.
by rewrite ltxx in hh.
Qed.

(** Source for [empty_compact_fibre_zero_threshold_regression]:
    zero threshold and degree-zero boundary of the
    sublevel formula in 2.10.26, p. 190.
    The genuine t+1/j budgets retain every point
    of the target when A is empty. *)
Example empty_compact_fibre_zero_threshold_regression (R : realType) (X Y : metricType R)
    (f : X -> Y) : continuous f ->
  (\bigcap_n fibre_open_cover_locus f set0 0 ((n.+1%:R : R)^-1)%R%:E
    ((n.+1%:R : R)^-1)%R%:E)=setT.
Proof.
move=> hf.
have he := @compact_fibre_mass_closed_level_formula R X Y f set0 0 0%R hf (@compact0 X).
apply/seteqP; split=> y // _.
have hle : hausdorff_fibre_mass f set0 0 y<=0.
  by rewrite /hausdorff_fibre_mass set0I (measure_empty (@hausdorff_measure_is_measure R X 0)).
have hbel : [set y | hausdorff_fibre_mass f set0 0 y<=0%:E] y := hle.
rewrite he in hbel.
move=> n _; have hh := hbel n Logic.I.
by rewrite add0r in hh.
Qed.

(** Source for [nonmeasurable_inclusion_fibre_regression]: direct
    inclusion counterexample of 2.10.26, p. 189,
    with a nonmeasurable real subset proved to exist
    using 2.2.4, p. 62. The map has Lipschitz
    bound one and the target measure is actual H^1. *)
Example nonmeasurable_inclusion_fibre_regression (R : realType) :
  exists A : set (real_line_metric R),
    is_metric_lipschitz_bound setT (fun x : metric_subset A=>(val x : real_line_metric R)) 1%R /\
    ~ is_measure_measurable_function (@hausdorff_measure R [the metricType R of real_line_metric R] 1)
      (partial_function_total
        (hausdorff_fibre_mass (fun x : metric_subset A=>(val x : real_line_metric R)) setT 0)).
Proof.
have [A [_ hA]] := real_nonmeasurable_inclusion_exists R; by exists A.
Qed.

(** Source for [zero_degree_empty_fibre_measurability_regression]:
    empty-source-set and both-degree-zero boundary of
    the actual theorem in 2.10.26, pp. 189–190.
    The target is arbitrary, and the theorem retains
    its stated source properness hypothesis. *)
Example zero_degree_empty_fibre_measurability_regression (R : realType) (X Y : metricType R)
    (f : X -> Y) (hf : is_metric_lipschitz setT f) :
  metric_boundedly_compact X ->
  is_measure_measurable_function (@hausdorff_measure R Y 0)
    (partial_function_total (hausdorff_fibre_mass f set0 0)) /\
  measure_almost_everywhere (@hausdorff_measure R Y 0)
    [set y | measure_measurable (@hausdorff_measure R X 0) (set0 `&` f @^-1` [set y])].
Proof.
move=> hX.
apply: (@federer_2_10_26 R X Y f hf set0 0 0 hX).
- exact: measure_measurable_empty (@hausdorff_measure_is_measure R X 0).
- rewrite (measure_empty (@hausdorff_measure_is_measure R X 0)); exact: ltry.
Qed.

(** Source for [zero_degree_tangent_profile_regression]:
    boundary regression for the closed-ball section
    costs in Federer 2.10.27, p. 191.
    A tangent section has radius zero but retains
    cost one at degree zero; the printed open
    projection would omit this boundary section. *)
Example zero_degree_tangent_profile_regression (R : realType) m
    (u y : inner_metric_space (@euclidean_inner_productP R m)) (r : R) (hr : (0<=r)%R) :
  mdist u y=r -> @euclidean_ball_section_profile R m 0 u r hr y = 1.
Proof.
move=> hy.
have hle : (mdist u y<=r)%R by rewrite hy.
rewrite (@ball_section_profile_inside R m 0 u r _
  (@euclidean_ball_section_profile_specification R m 0 u r hr) y hle)
  expr0 euclidean_unit_ball_volume0 mulr1; reflexivity.
Qed.

(** Source for [positive_degree_tangent_cutoff_regression]:
    radius-zero regression for the spherical cutoff
    majorant in Federer 2.10.27, p. 191.
    Only positive-radius generators are permitted;
    arbitrarily small enlargements still force a
    point's positive-degree cutoff mass to zero. *)
Example positive_degree_tangent_cutoff_regression (R : realType) (X : metricType R)
    (a : X) k (d : R) (nu : set X -> \bar R) :
  (0<d)%R ->
  is_metric_scale_envelope (fun j : @positive_closed_metric_balls R X=>val j)
    (fun j=>hausdorff_diameter_cost k.+1 (val j)) d%:E nu ->
  nu (metric_closed_ball a 0%R)=0.
Proof.
move=> hd hn.
have hmargin : (0%R+0<d)%R by rewrite add0r.
have hh := @spherical_scale_closed_ball_bound R X k.+1 a 0%R d nu hn (lexx 0%R) hmargin.
rewrite exprS mul0r mulr0 in hh.
apply/eqP; rewrite eq_le hh /=.
exact (@measure_nonnegative R X nu (metric_scale_envelope_is_measure hn
  (fun j=>hausdorff_diameter_cost_nonnegative k.+1 (val j))) (metric_closed_ball a 0%R)).
Qed.

(** Source for [empty_zero_dimensional_spherical_section_regression]:
    empty-set and empty-product regression for
    Federer 2.10.27, pp. 190–191.
    The full section upper integral equals zero
    at degree zero under the project's R^0
    unit-mass convention. *)
Example empty_zero_dimensional_spherical_section_regression (R : realType) :
  measure_upper_integral (@euclidean_lebesgue_measure R 0)
    (partial_function_total (fun y=>(@spherical_measure R (inner_metric_space (@euclidean_inner_productP R 0)) 0
      (metric_product_section (fun a b=>@euclidean_block_join R 0 0 (a,b)) set0 y) : extended_real_line R)))=0.
Proof.
have hi := @zero_dimensional_spherical_section_integral R 0 set0.
have he := measure_upper_integral_unique (measure_upper_integral_specification _ _) hi.2.1.
by rewrite he (measure_empty (@spherical_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R 0)) 0)).
Qed.

(** Source for [zero_degree_metric_product_regression]:
    degree-zero regression for the final product
    inequality in Federer 2.10.27, p. 191.
    Both normalizing factors reduce to one;
    the Cartesian metric remains abstract. *)
Example zero_degree_metric_product_regression (R : realType) (P Y Z : metricType R)
    (pair : Y -> Z -> P) (first : P -> Y) (second : P -> Z)
    (hp : is_metric_cartesian_product pair first second) :
  metric_boundedly_compact Y ->
  @hausdorff_measure R Y 0 setT* @hausdorff_measure R Z 0 setT<=
    @hausdorff_measure R P 0 setT.
Proof.
move=> hY.
have hh := @federer_2_10_27_product_lower_bound R P Y Z pair first second hp 0 0 (or_intror hY).
by rewrite addn0 !euclidean_unit_ball_volume0 mulr1 divr1 mul1e in hh.
Qed.

From mathcomp Require Import finmap.
From Federer Require Import RealPower RealCurveDerivativeUP.

(** Source for [degenerate_parent_phi_regression]: local counterexample to
    the unrestricted parent in Federer 2.10.28(4), p. 192. A point interval
    cannot satisfy the positive-radius family laws. *)
Example degenerate_parent_phi_regression (R : realType) (h : R -> R)
    (J : compact_real_intervals R) n F (x : R) :
  val J=(`[x,x] : set (real_line_metric R)) ->
  ~is_equal_cost_interval_family h J n F.
Proof.
move=> hJ hPhi; have hh := equal_cost_interval_parent_nondegenerate hPhi.
by rewrite hJ (extended_metric_diameter_segment (lexx x)) subrr /= ltxx in hh.
Qed.

(** Source for [zero_cost_dead_branch_regression]: empty-limit
    regression for Federer 2.10.28(3), p. 192,
    with the corrected single root (erratum
    p. 4, book p. 192 line 4).
    A point root has zero cost and can
    have no descendants. The lower-bound proof
    must not select a point of A in it. *)
Example zero_cost_dead_branch_regression (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J : compact_real_intervals R) (x : R) :
  val J=(`[x,x] : set (real_line_metric R)) -> exists H,
    is_special_interval_tree h H /\ H 0%N=([fset J])%fset /\ is_special_interval_tree_limit H set0.
Proof.
move=> hJ; apply: (@zero_cost_root_empty_limit_exists R h hg J).
by rewrite hJ (concave_interval_cost_segment h (lexx x)) subrr (interval_gauge_zero hg).
Qed.

(** Source for [classical_middle_third_parameters_regression]: classical
    Cantor regression for the final sentence of Federer 2.10.28, p. 193 The
    unit parent has child length 1/3 and spacing 2/3 under the
    logarithm-ratio exponent. *)
Example classical_middle_third_parameters_regression (R : realType) :
  let m := @classical_cantor_exponent R in
  let hg := @power_concave_interval_gauge R 1 m (@ltr01 R)
    (classical_cantor_exponent_bounds R).1 (classical_cantor_exponent_bounds R).2 in
  @cantor_split_radius R (fun t=>(1*real_power t m)%R) hg 1 2 (@ltr01 R) (leqnn 2)=(1/3)%R /\
  cantor_split_spacing (1 : R) 2 (1/3)%R=(2/3)%R.
Proof.
move=> m hg.
have hh := @classical_cantor_split_parameters R 1 1 (@ltr01 R) (@ltr01 R).
rewrite mulr1 in hh.
exact hh.
Qed.

(** Source for [fractional_cantor_distribution_regression]:
    nontrivial exponent and normalisation regression
    for Federer 2.10.28, p. 193, using
    c=2 and m=1/2. The image on A has
    total range [0,2], and the actual derivative
    is zero Lebesgue almost everywhere. The
    interval-generated measure keeps c explicit. *)
Example fractional_cantor_distribution_regression (R : realType) :
  exists (A : set (real_line_metric R)) (f : R -> R),
    is_power_cantor_pair 2 (1/2)%R (fun _=>2%N) A f /\
    f @` A=(`[0%R,2%R] : set R) /\
    measure_almost_everywhere (@lebesgue_scalar_measure R) [set x | has_real_curve_derivative f x 0%R].
Proof.
have hc : (0<2 :> R)%R by lra.
have hm : (0<1/2 :> R)%R by lra.
have hm1 : (1/2<1 :> R)%R by lra.
have [A [f hpair]] := @power_cantor_pair_exists R 2 (1/2)%R (fun _=>2%N) hc hm hm1 (fun _=>leqnn 2).
have hp := @power_cantor_pair_properties R 2 (1/2)%R (fun _=>2%N) A f hc hm hm1 hpair.
exists A,f; split=> //; split.
- exact hp.2.2.2.2.2.1.
- exact hp.2.2.2.2.2.2.2.2.2.
Qed.

(** Source for [real_power_degree_zero_infinite_diameter_regression]:
    degree-zero convention regression for 2.10.2(1),
    p. 171, used in the degree-zero conclusion
    of 2.10.29, p. 195: infinity^0= 1,
    so the positive coefficient is retained. *)
Example real_power_degree_zero_infinite_diameter_regression (R : realType) :
  @metric_real_power_cost R 3%R 0%R +oo=3%R%:E.
Proof. exact: metric_real_power_cost_degree_zero. Qed.

(** Source for [interleaved_cantor_point_product_regression]:
    diameter-zero regression for the local product
    estimate of 2.10.29, p. 194. The
    actual competing measure assigns zero mass
    to each point even though degree-zero
    covering costs are positive. *)
Example interleaved_cantor_point_product_regression (R : realType) (P : metricType R)
    (pair : real_line_metric R -> real_line_metric R -> P)
    (first second : P -> real_line_metric R)
    (hp : is_metric_cartesian_product pair first second)
    (c m : R) (hc : (0<=c)%R) n l A B f g (p : P) :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  is_power_cantor_pair c m n A f -> is_power_cantor_pair c m l B g ->
  @power_cantor_product_measure R P pair c m hc A B [set p]=0.
Proof.
move=> hcp hm hm1 hA hB.
exact (@power_cantor_product_zero_diameter R P pair first second hp c m hc n l A B f g
  hcp hm hm1 hA hB [set p] (extended_metric_diameter_singleton p)).
Qed.

(** Source for [fractional_interleaved_product_length_regression]:
    nontrivial m= 1/2 regression for 2.10.29,
    p. 194. Both actual factor power masses
    equal one, while the actual Euclidean
    mixed product has infinite Hausdorff length.
    No Gamma normalisation is needed at degree one. *)
Example fractional_interleaved_product_length_regression (R : realType) :
  exists (D : interleaved_cantor_scale_data R) (A B : set (real_line_metric R)) (f g : R -> R),
    is_interleaved_cantor_scales (fun t=>(1*real_power t (1/2))%R) D /\
    is_power_cantor_pair 1 (1/2)%R (cantor_left_subdivision D) A f /\
    is_power_cantor_pair 1 (1/2)%R (cantor_right_subdivision D) B g /\
    @metric_real_power_measure R [the metricType R of real_line_metric R] 1%R (1/2)%R A= 1 /\
    @metric_real_power_measure R [the metricType R of real_line_metric R] 1%R (1/2)%R B= 1 /\
    @hausdorff_length R [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
      (euclidean_cantor_product A B)=+oo.
Proof.
have hm : (0<1/2 :> R)%R by lra.
have hm1 : (1/2<1 :> R)%R by lra.
have [D [A [B [f [g [hD [hA hB]]]]]]] := @interleaved_power_cantor_pairs_exist R 1 (1/2)%R ltr01 hm hm1.
exists D,A,B,f,g; split=> //; split=> //; split=> //; split.
- exact: (power_cantor_pair_real_power_mass ltr01 hm hm1 hA).1.
split; first exact: (power_cantor_pair_real_power_mass ltr01 hm hm1 hB).1.
exact (@euclidean_interleaved_cantor_product_infinite_length R 1 (1/2)%R D A B f g ltr01 hm hm1 hD hA hB).
Qed.

(** Source for [interleaved_cantor_zero_degree_regression]:
    actual degree-zero Hausdorff regression for
    the final 0<=k bound of 2.10.29,
    p. 195. The separately specified real
    power measure agrees with the existing
    degree-zero measure at coefficient one. *)
Example interleaved_cantor_zero_degree_regression (R : realType) (c m : R) D A B f g :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  is_interleaved_cantor_scales (fun t=>(c*real_power t m)%R) D ->
  is_power_cantor_pair c m (cantor_left_subdivision D) A f ->
  is_power_cantor_pair c m (cantor_right_subdivision D) B g ->
  @hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
    0 (euclidean_cantor_product A B)=+oo.
Proof.
move=> hc hm hm1 hD hA hB.
have hgap : (0<m+1)%R by lra.
have hh := @euclidean_interleaved_cantor_product_infinite R c m D A B f g hc hm hm1 hD hA hB
  1%R 0%R ltr01 (lexx 0%R) hgap.
by rewrite metric_real_power_measure_zero_agreement in hh.
Qed.

From Federer Require Import PowerCantorSelfProduct.

(** Source for [half_degree_cantor_self_product_regression]:
    degree-2m=1 regression for the finite self-product
    bound of 2.10.29, p. 193. For m=1/2,
    the existing Hausdorff length of the actual
    Euclidean self-product is at most 2^(1/2).
    The mixed interleaved product above instead
    has infinite length. *)
Example half_degree_cantor_self_product_regression (R : realType) (c : R) n A f :
  (0<c)%R -> is_power_cantor_pair c (1/2)%R n A f ->
  @hausdorff_length R [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
    (euclidean_cantor_product A A)<=(real_power 2 (1/2)%R)%:E.
Proof.
move=> hc hA.
have hm : (0<1/2 :> R)%R by lra.
have hm1 : (1/2<1 :> R)%R by lra.
have hdeg : (2*(1/2)= 1 :> R)%R by lra.
have hh := @power_cantor_self_product_bound R c (1/2)%R 1 n A f hc hm hm1 ler01 hA.
by rewrite hdeg metric_real_power_measure_length_agreement mul1r in hh.
Qed.

(** Source for [third_degree_cantor_cube_length_regression]:
    q=3 and m=1/3 regression for the
    positive finite Cartesian-power assertion of
    2.10.29, p. 195. The actual Euclidean
    cube has finite existing Hausdorff length,
    with the explicit bound three. *)
Example third_degree_cantor_cube_length_regression (R : realType) (c : R) n A f :
  (0<c)%R -> is_power_cantor_pair c (1/3)%R n A f ->
  @hausdorff_length R [the metricType R of inner_metric_space (@euclidean_inner_productP R 3)]
    (euclidean_set_power 3 A)<=3%R%:E.
Proof.
move=> hc hA.
have hm : (0<1/3 :> R)%R by lra.
have hm1 : (1/3<1 :> R)%R by lra.
have hdeg : (3*(1/3)= 1 :> R)%R by lra.
have hh := @power_cantor_positive_cartesian_power_bound R c (1/3)%R 1 n A f 2 hc hm hm1 ler01 hA.
by rewrite hdeg metric_real_power_measure_length_agreement real_power_one_exponent ?ler0n // mul1r in hh.
Qed.

(** Source for [empty_coordinate_interval_box_regression]:
    empty-product geometry regression for the
    cube covers supporting 2.10.29, p. 195.
    The R^0 box has diameter zero; the
    main Cartesian-power theorem requires q>0. *)
Example empty_coordinate_interval_box_regression (R : realType) (F : 'I_0 -> compact_real_intervals R) :
  @extended_metric_diameter R [the metricType R of inner_metric_space (@euclidean_inner_productP R 0)]
    (@euclidean_interval_box R 0 F)=0.
Proof.
have hwidth i : (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val (F i)))<=0)%R.
  have hi := valP i; by move: hi; rewrite ltn0.
have hh := @euclidean_interval_box_diameter_bound R 0 F 0 (lexx 0%R) hwidth.
rewrite mul0r in hh; apply/eqP; rewrite eq_le hh.
exact: metric_diameter_nonnegative (extended_metric_diameter_specification (@euclidean_interval_box R 0 F)).
Qed.

(** Source for [twofold_interleaved_product_length_regression]:
    q=2 regression for the higher mixed-power
    infinity assertion of 2.10.29, p. 195.
    The actual R^4 power of the interleaved
    planar product has infinite existing Hausdorff
    length; the two scalar factors have
    exponent m=1/2 and positive mass. *)
Example twofold_interleaved_product_length_regression (R : realType) (c : R) D A B f g :
  (0<c)%R ->
  is_interleaved_cantor_scales (fun t=>(c*real_power t (1/2))%R) D ->
  is_power_cantor_pair c (1/2)%R (cantor_left_subdivision D) A f ->
  is_power_cantor_pair c (1/2)%R (cantor_right_subdivision D) B g ->
  @hausdorff_length R [the metricType R of inner_metric_space (@euclidean_inner_productP R 4)]
    (@euclidean_block_set_power R 2 (euclidean_cantor_product A B) 1)=+oo.
Proof.
move=> hc hD hA hB.
have hm : (0<1/2 :> R)%R by lra.
have hm1 : (1/2<1 :> R)%R by lra.
have hgap : (1<2*(1/2+1) :> R)%R by lra.
have hh := @interleaved_cantor_positive_power_infinite R c (1/2)%R D A B f g hc hm hm1 hD hA hB
  1 1%R 1%R ltr01 ler01 hgap.
by rewrite metric_real_power_measure_length_agreement in hh.
Qed.

(** Source for [twofold_grouped_cantor_product_length_regression]:
    q=2 regression for the final form of
    2.10.29, p. 195. The actual R^4
    product A^2*B^2 has infinite existing
    Hausdorff length, after the proved orthogonal
    transfer from the power of planar pairs. *)
Example twofold_grouped_cantor_product_length_regression (R : realType) (c : R) D A B f g :
  (0<c)%R ->
  is_interleaved_cantor_scales (fun t=>(c*real_power t (1/2))%R) D ->
  is_power_cantor_pair c (1/2)%R (cantor_left_subdivision D) A f ->
  is_power_cantor_pair c (1/2)%R (cantor_right_subdivision D) B g ->
  @hausdorff_length R [the metricType R of inner_metric_space (@euclidean_inner_productP R 4)]
    (@euclidean_power_product R 2 A B)=+oo.
Proof.
move=> hc hD hA hB.
have hm : (0<1/2 :> R)%R by lra.
have hm1 : (1/2<1 :> R)%R by lra.
have hgap : (1<2*(1/2+1) :> R)%R by lra.
have hh := @interleaved_cantor_power_product_infinite R c (1/2)%R D A B f g hc hm hm1 hD hA hB
  1 1%R 1%R ltr01 ler01 hgap.
by rewrite metric_real_power_measure_length_agreement in hh.
Qed.

(** Source for [zero_degree_regrouped_product_measure_regression]:
    degree-zero regression for the orthogonal
    identification in 2.10.29, p. 195.
    The existing degree-zero Hausdorff measures
    agree on both actual Euclidean presentations,
    for arbitrary scalar factor sets. *)
Example zero_degree_regrouped_product_measure_regression (R : realType) q (A B : set (real_line_metric R)) :
  @hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R (q.+1+q.+1))]
    0 (@euclidean_power_product R q.+1 A B)=
  @hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R (euclidean_power_dimension 2 q))]
    0 (@euclidean_block_set_power R 2 (euclidean_cantor_product A B) q).
Proof.
have hh := @euclidean_power_product_measure R q 1%R 0%R A B ler01 (lexx 0%R).
by rewrite !metric_real_power_measure_zero_agreement in hh.
Qed.

(** Source for [centered_empty_section_regression]: empty normal sections in
    Federer 2.10.30, p. 195, stay empty *)
Example centered_empty_section_regression (R : realType)
    (hb : metric_set_bounded (@set0 [the metricType R of real_line_metric R])) :
  centered_section hb=set0.
Proof. exact ((centered_section_empty (centered_section_specification hb)).1 erefl). Qed.

(** Source for [centered_singleton_section_regression]: a
    nonempty null section becomes the centre point
    in 2.10.30, p. 195. This distinguishes
    it from the preceding empty-section regression. *)
Example centered_singleton_section_regression (R : realType) (a : R)
    (hb : metric_set_bounded ([set a] : set [the metricType R of real_line_metric R])) :
  centered_section hb=[set 0%R].
Proof.
apply: centered_nonempty_null_section (centered_section_specification hb) _ _.
- by exists a.
- exact: lebesgue_scalar_singleton.
Qed.

(** Source for [steiner_empty_source_regression]: empty
    source regression for the bounded-set operation
    in 2.10.30, p. 195. It uses only
    the opaque operation and its section laws. *)
Example steiner_empty_source_regression (R : realType) n
    (u : inner_metric_space (@euclidean_inner_productP R n))
    (hu : euclidean_inner_product u u= 1%R)
    (hb : metric_set_bounded (@set0 [the metricType R of inner_metric_space (@euclidean_inner_productP R n)])) :
  steiner_symmetrisation (@euclidean_inner_productP R n) hu hb=set0.
Proof.
have hz : is_steiner_symmetrisation (@euclidean_inner_productP R n) u set0 set0.
  constructor=> // y hy.
  constructor; [by split=> [[t []]|[t []]]|by move=> [t []]|by []].
exact (steiner_symmetrisation_unique
  (steiner_symmetrisation_specification (@euclidean_inner_productP R n) hu hb) hz).
Qed.

(** Source for [steiner_reflection_line_regression]: direct
    scalar sign reversal for rho_u in 2.10.30,
    p. 195, checked on the actual Euclidean
    one-dimensional carrier. *)
Example steiner_reflection_line_regression (R : realType) (t : R) :
  normal_reflection (@euclidean_inner_productP R 1) (@coordinate_basis R 1 ord0)
    (euclidean_one_embed t)=euclidean_one_embed (-t).
Proof.
apply/ffunP=> i; rewrite (ord1 i) /normal_reflection
  OrthonormalFamilies.inner_coordinateE CoordinateProjection.euclidean_inner_basis
  /euclidean_one_embed /coordinate_basis !ffunE eqxx.
change ((t-(2*t)*1= -t)%R); ring.
Qed.

(** Source for [zero_dimensional_steiner_normal_impossible_regression]:
    zero-dimensional boundary case for 2.10.30,
    p. 195. A unit normal cannot exist in
    R^0, so no fictitious codimension-one direction
    is introduced by the general volume theorem. *)
Example zero_dimensional_steiner_normal_impossible_regression (R : realType) :
  ~exists u : inner_metric_space (@euclidean_inner_productP R 0),
    euclidean_inner_product u u= 1%R.
Proof.
move=> [u hu]; rewrite /euclidean_inner_product big_ord0 in hu.
have hh : (0 != 1 :> R)%R by rewrite eq_sym oner_eq0.
by move/eqP: hu; rewrite (negbTE hh).
Qed.

(** Source for [steiner_zero_radius_collapse_regression]:
    radius-zero containing-ball regression for 2.10.30,
    p. 195. Either the source is empty or
    it consists of the origin; its symmetrisation
    cannot acquire another point. *)
Example steiner_zero_radius_collapse_regression (R : realType) n
    (u : inner_metric_space (@euclidean_inner_productP R n))
    (S T : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_steiner_symmetrisation (@euclidean_inner_productP R n) u S T ->
  S `<=` [set 0%R] -> T `<=` [set 0%R].
Proof.
move=> hT hS.
have hbound z : S z -> (inner_norm (@euclidean_inner_productP R n) z<=0)%R.
  by move=> hz; have -> := hS z hz; rewrite inner_norm0.
move=> x hx.
have hh := steiner_preserves_centered_ball hT (lexx 0%R) hbound hx.
have he : inner_norm (@euclidean_inner_productP R n) x=0%R.
  apply/eqP; by rewrite eq_le hh inner_norm_nonnegative.
apply/eqP; by rewrite -(inner_norm_eq0 (@euclidean_inner_productP R n)) he eqxx.
Qed.

(** Source for [normal_line_singleton_length_regression]:
    nonempty zero-length line section regression for
    2.10.30, p. 195. Ambient Hausdorff length
    is zero at a point on an arbitrary normal
    line, by the actual scalar-to-line measure law. *)
Example normal_line_singleton_length_regression (R : realType) n
    (u y : inner_metric_space (@euclidean_inner_productP R n))
    (hu : euclidean_inner_product u u= 1%R)
    (hy : OrthonormalFamilies.inner_coordinate (@euclidean_inner_productP R n) u y=0%R) (a : R) :
  @hausdorff_length R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
    ((fun t : R=>(y+t*:u)%R) @` [set a])=0%:E.
Proof.
rewrite (@normal_line_hausdorff_length R (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) u y hu hy).
exact: lebesgue_scalar_singleton.
Qed.

(** Source for [steiner_reversed_normal_operation_regression]:
    reversing the unit normal does not change the
    actual sealed operation in 2.10.30, p. 195.
    The two normal-proof witnesses may differ. *)
Example steiner_reversed_normal_operation_regression (R : realType) n
    (u : inner_metric_space (@euclidean_inner_productP R n))
    (hu : euclidean_inner_product u u= 1%R)
    (hv : euclidean_inner_product (-u) (-u)= 1%R)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (hb : metric_set_bounded S) :
  steiner_symmetrisation (@euclidean_inner_productP R n) hu hb=
    steiner_symmetrisation (@euclidean_inner_productP R n) hv hb.
Proof.
exact (steiner_symmetrisation_unique
  (steiner_reverse_normal (steiner_symmetrisation_specification (@euclidean_inner_productP R n) hu hb))
  (steiner_symmetrisation_specification (@euclidean_inner_productP R n) hv hb)).
Qed.

Local Close Scope ereal_scope.

(** Source for [compact_two_endpoints_length_gap_regression]:
    strict line-length step in 2.10.31, p. 196.
    Both interval endpoints can be present while an
    interior hole still makes the length strictly smaller.
    This guards against replacing compactness plus full
    length by mere endpoint inclusion. *)
Example compact_two_endpoints_length_gap_regression (R : realType) :
  (lebesgue_scalar_measure ([set (-1 : R)%R] `|` [set (1 : R)%R])<((1+1)%R)%:E)%E.
Proof.
apply: (@compact_scalar_missing_interior_length R ([set -1] `|` [set 1]) 1 0).
- apply: compactU; exact: (@compact_set1 (real_line_metric R)).
- move=> x [->|->]; by rewrite ?normrN normr1.
- by rewrite ltrN10.
- exact: ltr01.
- move=> [h|h]; have hh : (0 : R)!= 1 by rewrite eq_sym oner_eq0.
  + have hz : (0 : R)= 1 by rewrite -[1]opprK -h oppr0.
    by move/eqP: hz; rewrite (negbTE hh).
  + by move/eqP: h; rewrite (negbTE hh).
Qed.

(** Source for [compact_noncentral_singleton_radius_regression]:
    least enclosing radius supporting 2.10.31,
    pp. 195–196. A scalar singleton at 5
    has radius 3 about centre 2; this checks
    that the abstract radius does not fix its centre
    implicitly to zero. *)
Example compact_noncentral_singleton_radius_regression (R : realType)
    (C : compact_metric_set (real_line_metric R)) :
  val C=[set (5 : R)] -> compact_enclosing_radius (2 : real_line_metric R) C=3.
Proof.
move=> hC; rewrite (compact_enclosing_radius_singleton (2 : real_line_metric R) hC)
  real_line_metric_distanceE.
have he : (2-5 : R)= -3 by ring.
by rewrite he normrN normr_nat.
Qed.

(** Source for [zero_dimensional_compact_radius_regression]:
    radius-zero alternative of 2.10.31, p. 195.
    Every nonempty compact subset of R^0 is
    the origin singleton, independently of any
    vacuous unit-normal stability hypothesis. *)
Example zero_dimensional_compact_radius_regression (R : realType)
    (C : compact_metric_set (inner_metric_space (@euclidean_inner_productP R 0))) :
  compact_enclosing_radius (0 : inner_metric_space (@euclidean_inner_productP R 0)) C=0 /\
    val C=[set (0 : inner_metric_space (@euclidean_inner_productP R 0))].
Proof.
have hz (x : inner_metric_space (@euclidean_inner_productP R 0)) : x=0.
  apply/ffunP=> i; have hi := ltn_ord i; by rewrite ltn0 in hi.
have he : val C=[set (0 : inner_metric_space (@euclidean_inner_productP R 0))].
  apply/seteqP; split=> x hx; first exact: hz.
  have [y hy] := (set_valP C).2; by rewrite (hz x) -(hz y).
split=> //; rewrite (compact_enclosing_radius_singleton (0 : inner_metric_space (@euclidean_inner_productP R 0)) he).
exact: mdistxx.
Qed.

(** Source for [positive_radius_centre_correction_regression]:
    local correction to the B(a,s) inference in
    2.10.31, p. 196. Extract the checked
    unit-distance obstruction for the origin singleton.
    It concerns an intermediate printed proof step,
    not the conclusion of the compact-class theorem. *)
Example positive_radius_centre_correction_regression (R : realType) :
  exists a : inner_metric_space (@euclidean_inner_productP R 1),
    mdist (0 : inner_metric_space (@euclidean_inner_productP R 1)) a= 1 /\
    forall s : R, s<1 -> ~(([set 0] : set (inner_metric_space (@euclidean_inner_productP R 1))) `<=`
      metric_closed_ball a s).
Proof.
have [a [ha [_ [_ [_ [_ hbad]]]]]] := shrinking_ball_wrong_center_counterexample R.
by exists a.
Qed.

From Federer Require Import ExteriorMeasureGauge ExteriorDiameterUP ExteriorDiameterLaws ExteriorDiameter EuclideanBallExteriorCost SteinerVolumeCostFamilyUP SteinerVolumeCostComparison EuclideanExteriorVolumeTheorem.
Local Close Scope ereal_scope.

From Federer Require Import InnerConvex.

(** Source for [zero_dimensional_exterior_ball_cost_regression]:
    empty-product boundary of the centred-ball
    equality in 2.10.32, p. 197. In R^0
    the radius-zero ball has both volume and
    exterior cost one, rather than zero. *)
Example zero_dimensional_exterior_ball_cost_regression (R : realType) :
  exterior_diameter_cost 0 (metric_closed_ball
    (0 : inner_metric_space (@euclidean_inner_productP R 0)) 0)= 1%E.
Proof.
by rewrite (@euclidean_closed_ball_exterior_cost R 0 0 (lexx 0))
  euclidean_unit_ball_volume0 expr0 mul1r.
Qed.

(** Source for [positive_dimensional_zero_ball_cost_regression]:
    positive-dimensional radius-zero boundary of
    the ball equality in 2.10.32, p. 197.
    It has cost zero, distinguishing it from
    the zero-dimensional empty-product case. *)
Example positive_dimensional_zero_ball_cost_regression (R : realType) (n : nat) :
  exterior_diameter_cost n.+1 (metric_closed_ball
    (0 : inner_metric_space (@euclidean_inner_productP R n.+1)) 0)=0%E.
Proof.
by rewrite (@euclidean_closed_ball_exterior_cost R n.+1 0 (lexx 0)) exprS mul0r mulr0.
Qed.

(** Source for [positive_volume_zero_cost_family_empty_regression]:
    zero-cost threshold of the class argument in
    2.10.32, pp. 196–197. A compact convex
    member cannot have volume at least one and
    exterior cost zero, in any dimension. *)
Example positive_volume_zero_cost_family_empty_regression (R : realType) (n : nat) :
  @steiner_volume_cost_family R n 1 0=set0.
Proof.
apply/seteqP; split=> K hK; last by case: hK.
have hne : @steiner_volume_cost_family R n 1 0 !=set0 by exists K.
have hh := @steiner_volume_cost_threshold_comparison R n 1 0 (lexx 0) hne.
by move: hh; rewrite ler10.
Qed.

(** Source for [nonconvex_endpoint_set_volume_regression]:
    arbitrary-set scope of 2.10.32, pp. 196–197.
    The two opposite unit points of R^1 form
    a nonconvex source, but their volume still
    satisfies the bound by the unit-ball cost two.
    This checks the closed-convex-hull reduction. *)
Example nonconvex_endpoint_set_volume_regression (R : realType) :
  let E := inner_metric_space (@euclidean_inner_productP R 1) in
  let u : E := euclidean_one_embed 1 in
  let S : set E := [set -u] `|` [set u] in
  ~is_inner_convex S /\ (euclidean_lebesgue_measure 1 S<= 2)%E.
Proof.
move=> E u S.
have hun : `|u|= 1.
  by rewrite euclidean_norm_one /u /euclidean_one_embed ffunE normr1.
have hnot : ~S 0.
  move=> [hz|hz]; have hh := congr1 (fun z : E=>`|z|) hz;
    rewrite normr0 ?normrN hun in hh; lra.
split.
- move=> hconv.
  have hn : S (-u) by left.
  have hp : S u by right.
  have hh := inner_convex_midpoint hconv hn hp.
  rewrite addNr scaler0 in hh; exact: hnot hh.
- have hne : S !=set0 by exists u; right.
  have hsub : S `<=` metric_closed_ball (0 : E) 1.
    move=> z [->|->]; by rewrite /metric_closed_ball /= inner_metric_normE subr0 ?normrN hun.
  have hc := @exterior_diameter_cost_mono R 1 1 S (metric_closed_ball (0 : E) 1) hsub.
  have hb : exterior_diameter_cost 1 (metric_closed_ball (0 : E) 1)= 2%E.
    by rewrite (@euclidean_closed_ball_exterior_cost R 1 1 (@ler01 R))
      euclidean_unit_ball_volume1 expr1 mulr1.
  rewrite hb in hc.
  exact (le_trans (@lebesgue_top_exterior_cost_bound R 1 S hne) hc).
Qed.

(** Source for [unbounded_line_exterior_volume_bound_regression]:
    unbounded-source scope of 2.10.32,
    pp. 196–197. The full real line is
    accepted without a compactness, boundedness
    or finite-cost premise. *)
Example unbounded_line_exterior_volume_bound_regression (R : realType) :
  (euclidean_lebesgue_measure 1
    (@setT (inner_metric_space (@euclidean_inner_productP R 1)))<=
    exterior_diameter_cost 1 (@setT (inner_metric_space (@euclidean_inner_productP R 1))))%E.
Proof.
apply: (@federer_2_10_32 R 1 setT).
by exists (0 : inner_metric_space (@euclidean_inner_productP R 1)).
Qed.

(** Source for [positive_dimensional_singleton_exterior_volume_regression]:
    zero-cost source in 2.10.32, pp. 196–197.
    An arbitrary singleton in positive dimension
    has volume zero by the new arbitrary-set
    bound and its previously proved zero cost. *)
Example positive_dimensional_singleton_exterior_volume_regression (R : realType) (n : nat)
    (x : inner_metric_space (@euclidean_inner_productP R n.+1)) :
  euclidean_lebesgue_measure n.+1 [set x]=0%E.
Proof.
have hne : [set x] !=set0 by exists x.
have hh := @lebesgue_top_exterior_cost_bound R n.+1 [set x] hne.
rewrite (@exterior_diameter_cost_singleton R n.+1 n.+1 x (ltn0Sn n)) in hh.
have h0 := measure_nonnegative (euclidean_lebesgue_is_measure R n.+1) [set x].
apply/eqP; by rewrite eq_le hh h0.
Qed.

(** Source for [diameter_power_counterexample_regression]: Regression
    supporting Federer 2.10.32–2.10.33, pp. 196–197: in the planar closed
    unit ball, diameter is at most two but opposite coordinate endpoints
    give exterior norm four. The comparison requires the dimension-th power
    of diameter. *)
Example diameter_power_counterexample_regression (R : realType) :
  let E := inner_metric_space (@euclidean_inner_productP R 2) in
  let S : set E := metric_closed_ball (0 : E) 1 in
  (extended_metric_diameter S<=2)%E /\ (4<=extended_exterior_diameter 2 S)%E.
Proof.
move=> E S.
split.
- apply: (metric_diameter_least (extended_metric_diameter_specification S)).
  + by rewrite lee_fin ler0n.
  + move=> x y hx hy; rewrite lee_fin.
    exact: metric_closed_ball_diameter_bound hx hy.
- pose hB := @euclidean_inner_productP R 2.
  have ho : orthonormal_family (@euclidean_inner_product R 2) (@coordinate_basis R 2).
    by move=> i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
  have hn i : inner_norm hB (@coordinate_basis R 2 i)= 1 := InnerNormalization.orthonormal_norm1 hB ho i.
  pose p (i : 'I_2) := @coordinate_basis R 2 i.
  pose q (i : 'I_2) := -(@coordinate_basis R 2 i).
  have hp i : S (p i).
    by rewrite /S /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN /p hn.
  have hq i : S (q i).
    by rewrite /S /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN /q inner_normN hn.
  have he : (fun i=>p i-q i)=(fun i=>(1+1 : R)*:(@coordinate_basis R 2 i)).
    by apply: funext=> i; rewrite /p /q opprK scalerDl !scale1r.
  have hnorm : exterior_difference_norm p q=(4 : R).
    rewrite /exterior_difference_norm /exterior_difference_product he
      ExteriorProductFactors.exterior_product_scaled_family prodr_const card_ord
      ExteriorNorm.exterior_norm_scale normrX ger0_norm ?addr_ge0 //.
    rewrite (@ExteriorNorm.orthonormal_product_unit_norm R (real_exterior_two_nonzero R) (R_n R 2)
      (@euclidean_inner_product R 2) hB 2 (@coordinate_basis R 2) ho) mulr1 expr2.
    ring.
  have hh := exterior_diameter_endpoint_upper (extended_exterior_diameter_specification 2 S) hp hq.
  by rewrite hnorm in hh.
Qed.

From Federer Require Import EuclideanIsodiametric HausdorffDiameterCost EuclideanBallExteriorCost.

(** Source for [zero_dimensional_isodiametric_regression]:
    dimension-zero boundary of 2.10.33, p. 197.
    The singleton has zero diameter, but the
    empty-power convention makes the sharp upper
    bound one, agreeing with its actual volume. *)
Example zero_dimensional_isodiametric_regression (R : realType) :
  let S := [set (0 : inner_metric_space (@euclidean_inner_productP R 0))] in
  (extended_metric_diameter S= 0%E /\
    hausdorff_diameter_cost 0 S= 1%E /\
    euclidean_lebesgue_measure 0 S= 1%E).
Proof.
move=> S; split; first exact: extended_metric_diameter_singleton.
split; first exact: hausdorff_diameter_cost_zero_degree.
have he : S=metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R 0)) 0.
  apply/seteqP; split=> x hx; first by rewrite hx /metric_closed_ball /= mdistxx.
  apply/ffunP=> i; have hi:=ltn_ord i; by rewrite ltn0 in hi.
rewrite he -(@euclidean_closed_ball_exterior_volume R 0 0 (lexx 0)).
by rewrite (@euclidean_closed_ball_exterior_cost R 0 0 (lexx 0))
  euclidean_unit_ball_volume0 expr0 mul1r.
Qed.

(** Source for [zero_diameter_positive_volume_null_regression]:
    zero-diameter boundary of 2.10.33, p. 197.
    A nonempty zero-diameter source has zero
    Lebesgue outer measure in positive dimension,
    with no measurability assumption. *)
Example zero_diameter_positive_volume_null_regression (R : realType) (n : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n.+1))) :
  S !=set0 -> extended_metric_diameter S= 0%E -> euclidean_lebesgue_measure n.+1 S= 0%E.
Proof.
move=> hS hd; have hh := @lebesgue_isodiametric_bound R n.+1 S hS.
rewrite /hausdorff_diameter_cost /hausdorff_power_cost hd expeS mul0e mule0 in hh.
by apply/eqP; rewrite eq_le hh (measure_nonnegative (euclidean_lebesgue_is_measure R n.+1)).
Qed.

(** Source for [unit_line_ball_isodiametric_sharp_regression]:
    sharpness regression for the coefficient in
    2.10.33, p. 197. The unit closed
    ball in R has actual volume two,
    exactly its normalised diameter cost. *)
Example unit_line_ball_isodiametric_sharp_regression (R : realType) :
  let S := metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R 1)) 1 in
  euclidean_lebesgue_measure 1 S= 2%E /\ hausdorff_diameter_cost 1 S= 2%E.
Proof.
move=> S.
have hv : euclidean_lebesgue_measure 1 S= 2%E.
  rewrite /S -(@euclidean_closed_ball_exterior_volume R 1 1 (ler01))
    (@euclidean_closed_ball_exterior_cost R 1 1 (ler01)).
  by rewrite euclidean_unit_ball_volume1 expr1 mulr1.
split=> //.
apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite hausdorff_diameter_cost_one_degree.
  apply: (metric_diameter_least (extended_metric_diameter_specification S)).
  + by rewrite lee_fin ler0n.
  + move=> x y hx hy; rewrite lee_fin.
    exact: metric_closed_ball_diameter_bound hx hy.
- rewrite -hv; apply: lebesgue_isodiametric_bound.
  exists (0 : inner_metric_space (@euclidean_inner_productP R 1)).
  by rewrite /S /metric_closed_ball /= mdistxx ler01.
Qed.

From Federer Require Import GrossExteriorComparison ProjectionMeasure ExteriorMeasure ExteriorDegenerateGauges
  ExteriorProjectionDiameter ProjectedExteriorGaugeBound ExteriorMeasureGauge.

(** Source for [gross_positive_countable_null_regression]:
    countable-target boundary of 2.10.34,
    p. 197. The comparison with T^m
    and its previously proved positive-degree
    countable nullity force actual Gross nullity. *)
Example gross_positive_countable_null_regression (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (0<m)%N -> (m<=n)%N -> countable A -> @gross_measure R n m A= 0%E.
Proof.
move=> hm hmn hA; have hh := @federer_2_10_34 R n m hmn A.
rewrite (@exterior_measure_positive_countable_zero R n m A hm hA) in hh.
by apply/eqP; rewrite eq_le hh (measure_nonnegative (@gross_measure_is_measure R n m hmn)).
Qed.

(** Source for [zero_dimensional_gross_comparison_empty_regression]:
    empty-target and dimension-zero boundary of
    2.10.34, p. 197. Both actual
    measures vanish on the empty set,
    despite the degree-zero nonempty-generator cost. *)
Example zero_dimensional_gross_comparison_empty_regression (R : realType) :
  @gross_measure R 0 0 set0= 0%E /\ @exterior_diameter_measure R 0 0 set0= 0%E.
Proof.
split.
- exact: measure_empty (@gross_measure_is_measure R 0 0 (leqnn 0)).
- exact: measure_empty (@exterior_diameter_measure_is_measure R 0 0).
Qed.

(** Source for [projection_zero_degree_nonempty_cost_regression]:
    degree-zero boundary of the projection-cost
    step in 2.10.34, p. 197.
    The empty exterior product has cost
    one on both a nonempty source
    ball and its zero-dimensional projection. *)
Example projection_zero_degree_nonempty_cost_regression (R : realType)
    (p : {linear R_n R 0 -> R_n R 0}) : O_star p ->
  let S := metric_closed_ball (0 : inner_metric_space (@euclidean_inner_productP R 0)) 0 in
  exterior_diameter_cost 0 (p @` S)= 1%E /\ exterior_diameter_cost 0 S= 1%E.
Proof.
move=> hp S.
have he : p @` S=S.
  apply/seteqP; split=> x hx.
  - have [y hy <-] := hx; change (S (p y)).
    have hz : p y= 0 by apply/ffunP=> i; have hi:=ltn_ord i; by rewrite ltn0 in hi.
    by rewrite hz /S /metric_closed_ball /= mdistxx.
  - exists (0 : R_n R 0).
    + by rewrite /S /metric_closed_ball /= mdistxx.
    + have hz : x= 0 by apply/ffunP=> i; have hi:=ltn_ord i; by rewrite ltn0 in hi.
      by rewrite hz linear0.
rewrite he; split; exact: zero_dimensional_exterior_ball_cost_regression.
Qed.

From Federer Require Import EuclideanMeasureEqualities EuclideanIntegralGeometricLebesgue
  NonnegativeExtendedProbabilityConstant OrthogonalProjectionProbability
  NonnegativeExtendedExponentNorm EuclideanClosedBallVolume.

(** Source for [zero_dimensional_all_measures_point_regression]:
    dimension-zero boundary of the seven-measure
    equality in 2.10.35, p. 197.
    Each actual measure gives one to
    the sole point, including at infinite exponent. *)
Example zero_dimensional_all_measures_point_regression (R : realType) :
  let X := inner_metric_space (@euclidean_inner_productP R 0) in
  let A := [set (0 : X)] in
  @spherical_measure R X 0 A= 1%E /\ @hausdorff_measure R X 0 A= 1%E /\
  @exterior_diameter_measure R 0 0 A= 1%E /\
  @convex_integral_geometric_measure R 0 0 (leqnn 0) +oo%E A= 1%E /\
  @integral_geometric_measure R 0 0 (leqnn 0) +oo%E A= 1%E /\ @gross_measure R 0 0 A= 1%E.
Proof.
move=> X A.
have [_ [_ hv]] := zero_dimensional_isodiametric_regression R.
have hh := @federer_2_10_35 R 0 (leqnn 0) +oo%E (leey 1%E) A.
by rewrite hv in hh.
Qed.

(** Source for [positive_singleton_all_measures_null_regression]:
    positive-dimensional singleton boundary of
    2.10.35, p. 197. All six
    comparison measures vanish, including both
    integral-geometric measures at exponent one. *)
Example positive_singleton_all_measures_null_regression (R : realType) (n : nat)
    (x : inner_metric_space (@euclidean_inner_productP R n.+1)) :
  let A := [set x] in
  @spherical_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) n.+1 A= 0%E /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) n.+1 A= 0%E /\
  @exterior_diameter_measure R n.+1 n.+1 A= 0%E /\
  @convex_integral_geometric_measure R n.+1 n.+1 (leqnn n.+1) 1%E A= 0%E /\
  @integral_geometric_measure R n.+1 n.+1 (leqnn n.+1) 1%E A= 0%E /\ @gross_measure R n.+1 n.+1 A= 0%E.
Proof.
move=> A.
have hh := @federer_2_10_35 R n.+1 (leqnn n.+1) 1%E (lexx 1%E) A.
by rewrite (positive_dimensional_singleton_exterior_volume_regression x) in hh.
Qed.

(** Source for [unbounded_line_integral_geometric_infinite_regression]:
    infinite-mass and infinite-exponent boundary
    of 2.10.35, p. 197. The
    whole Euclidean line has infinite actual
    Lebesgue volume, hence infinite I_infinity
    and Q_infinity measure. Closed balls
    supply the unbounded lower volume estimates. *)
Example unbounded_line_integral_geometric_infinite_regression (R : realType) :
  @integral_geometric_measure R 1 1 (leqnn 1) +oo%E setT=+oo%E /\
  @convex_integral_geometric_measure R 1 1 (leqnn 1) +oo%E setT=+oo%E.
Proof.
pose X := inner_metric_space (@euclidean_inner_productP R 1).
have hv : euclidean_lebesgue_measure 1 (@setT X)=+oo%E.
  have hnon := measure_nonnegative (euclidean_lebesgue_is_measure R 1) (@setT X).
  case he: (euclidean_lebesgue_measure 1 (@setT X)) hnon=> [a| |] hnon; last by rewrite leeNy_eq in hnon.
  - have ha : (0<=a)%R by move: hnon; rewrite lee_fin.
    have hr : (0<=a+1)%R by rewrite addr_ge0.
    have hh := @measure_mono R X (@euclidean_lebesgue_measure R 1)
      (euclidean_lebesgue_is_measure R 1) (metric_closed_ball (0 : X) (a+1)) setT (fun _ _=>I).
    rewrite (euclidean_closed_ball_normalized_volume (0 : X) hr) he
      euclidean_unit_ball_volume1 expr1 lee_fin in hh.
    exfalso; clear he hnon; lra.
  - by [].
split.
- by rewrite (@euclidean_integral_geometric_lebesgue R 1 (leqnn 1) +oo%E (leey 1%E) setT) hv.
- by rewrite (@euclidean_convex_integral_geometric_lebesgue R 1 (leqnn 1) +oo%E (leey 1%E) setT) hv.
Qed.

(** Source for [projection_probability_infinite_constant_norm_regression]:
    infinite-input boundary of the constant
    probability calculation supporting 2.10.35,
    p. 197. For the actual zero-dimensional
    projection probability, the norm of the
    constant infinity input is infinity at
    exponent one and at infinity. *)
Example projection_probability_infinite_constant_norm_regression (R : realType) :
  let mu := @orthogonal_projection_probability R 0 0 (leqnn 0) in
  nonnegative_extended_exponent_norm mu (fun _=>+oo%E) 1%E=+oo%E /\
  nonnegative_extended_exponent_norm mu (fun _=>+oo%E) +oo%E=+oo%E.
Proof.
move=> mu; have hm := @theta_star_is_measure R 0 0 (leqnn 0).
have ht := @theta_star_total R 0 0 (leqnn 0).
split.
- exact: (@probability_nonnegative_extended_constant_norm R _ mu hm +oo%E 1%E
    ht (leey 0%E) (lexx 1%E)).
- exact: (@probability_nonnegative_extended_constant_norm R _ mu hm +oo%E +oo%E
    ht (leey 0%E) (leey 1%E)).
Qed.

(** Source for [zero_dimensional_endpoint_volume_regression]:
    auxiliary empty-product boundary of 2.10.36,
    p. 198. The product has norm one,
    and the nonempty zero-dimensional source has
    unit Lebesgue mass. This is an explicit
    convention extending the positive-dimensional book theorem. *)
Example zero_dimensional_endpoint_volume_regression (R : realType) :
  let v := fun _ : 'I_0 => (0 : R_n R 0) in
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R 0)
    (e_lambda v (ord_tuple 0))= 1%R /\
  ((exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R 0)
    (e_lambda (fun i => v i-v i) (ord_tuple 0)))%:E <=
    (0`!)%:R%:E*euclidean_lebesgue_measure 0 setT)%E.
Proof.
move=> v; split.
- apply: orthonormal_product_unit_norm=> i j.
  have hi := ltn_ord i; by rewrite ltn0 in hi.
- apply: (@convex_endpoint_volume_bound R 0 setT v v).
  + by move=> x y hx hy t ht0 ht1.
  + by exists (0 : inner_metric_space (@euclidean_inner_productP R 0)).
  + by move=> i.
  + by move=> i.
Qed.

(** Source for [empty_degree_zero_endpoint_counterexample]:
    regression for the nonempty-source convention in
    the degree-zero extension of 2.10.36,
    p. 198. On an empty source the
    endpoint families are vacuous, but norm one
    cannot be bounded by zero mass. This
    is a local convention check, not a
    counterexample to the positive-dimensional book statement. *)
Example empty_degree_zero_endpoint_counterexample (R : realType) :
  let v := fun _ : 'I_0 => (0 : R_n R 0) in
  ~ ((exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R 0)
    (e_lambda v (ord_tuple 0)))%:E <=
    (0`!)%:R%:E*euclidean_lebesgue_measure 0 set0)%E.
Proof.
move=> v.
have [hnorm _] := zero_dimensional_endpoint_volume_regression R.
rewrite hnorm (measure_empty (euclidean_lebesgue_is_measure R 0)) mule0 lee_fin.
by rewrite ler10.
Qed.

(** Source for [convex_null_endpoint_product_regression]:
    zero-volume boundary of 2.10.36,
    p. 198. Any full-degree endpoint product
    in a convex Lebesgue-null set vanishes.
    This derived regression retains arbitrary convex
    sources and the printed positive degree. *)
Example convex_null_endpoint_product_regression (R : realType) (n : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (a b : 'I_n -> inner_metric_space (@euclidean_inner_productP R n)) :
  (0<n)%N -> is_inner_convex S ->
  (forall i, S (a i)) -> (forall i, S (b i)) ->
  euclidean_lebesgue_measure n S= 0%E ->
  e_lambda (fun i => a i-b i) (ord_tuple n)=0.
Proof.
move=> hn hS ha hb hz.
have hh := @federer_2_10_36 R n S a b hn hS ha hb.
rewrite hz mule0 lee_fin in hh.
apply/eqP; rewrite -(exterior_norm_eq0 (euclidean_two_nonzero R) (@euclidean_inner_productP R n)).
apply/eqP; apply: le_anti; apply/andP; split=> //.
exact: exterior_norm_nonnegative.
Qed.

(** Source for [zero_simple_projection_norm_regression]:
    zero-vector boundary of the norm identity
    in the proof of 2.10.37, p. 198,
    from 2.7.16(6), p. 140. A zero
    simple vector in positive degree has zero
    actual projection exponent norm, including infinity. *)
Example zero_simple_projection_norm_regression (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :
  (0<m)%N -> (1<=t)%E ->
  nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
    (fun p : orthogonal_projection_metric_space R n m =>
      (projection_norm (real_exterior_two_nonzero R) (0 : exterior_power (R_n R n) m) p)%:E) t= 0%E.
Proof.
move=> hm ht.
have hz : e_lambda (fun _ : 'I_m=>(0 : R_n R n)) (ord_tuple m)=0.
  apply: (@exterior_product_zero_entry R [the choiceType of 'I_m] (R_n R n)
    (fun _=>0) m (ord_tuple m) (Ordinal hm)); [exact: mem_enum|reflexivity].
have hs : simple (0 : exterior_power (R_n R n) m).
  rewrite -hz; exact: product_simple.
have hn := @simple_projection_extended_exponent_norm R n m hmn 0 t hs ht.
by rewrite exterior_norm_zero mulr0 in hn.
Qed.

(** Source for [empty_product_projection_norm_regression]:
    auxiliary degree-zero boundary of the projection
    norm identity used in 2.10.37, p. 198.
    In the zero-dimensional ambient space, the
    empty product has norm one and the
    actual projection exponent norm is one
    for every admissible exponent. *)
Example empty_product_projection_norm_regression (R : realType) (t : \bar R) :
  (1<=t)%E ->
  let xi := e_lambda (fun _ : 'I_0=>(0 : R_n R 0)) (ord_tuple 0) in
  nonnegative_extended_exponent_norm (@orthogonal_projection_probability R 0 0 (leqnn 0))
    (fun p : orthogonal_projection_metric_space R 0 0 =>
      (projection_norm (real_exterior_two_nonzero R) xi p)%:E) t= 1%E.
Proof.
move=> ht xi.
have hs : simple xi := product_simple _.
have hu : exterior_norm (real_exterior_two_nonzero R) (@euclidean_inner_productP R 0) xi= 1%R.
  apply: orthonormal_product_unit_norm=> i j.
  have hi := ltn_ord i; by rewrite ltn0 in hi.
have hn := @simple_projection_extended_exponent_norm R 0 0 (leqnn 0) xi t hs ht.
by rewrite (@equal_dimension_projection_beta R 0 (leqnn 0) t ht) hu mulr1 in hn.
Qed.

(** Source for [degree_one_exterior_convex_integral_regression]:
    degree-one boundary of 2.10.37, p. 198.
    The actual coefficient alpha(1) 2^(-1) 1!
    is one because alpha(1)=2 in
    2.7.16(1), p. 135. Thus T^1<=Q_t^1
    on arbitrary targets in every positive ambient
    dimension and for every admissible exponent. *)
Example degree_one_exterior_convex_integral_regression (R : realType) (n : nat)
    (h1n : (1<=n)%N) (t : \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (1<=t)%E -> (@exterior_diameter_measure R n 1 A <=
    @convex_integral_geometric_measure R n 1 h1n t A)%E.
Proof.
move=> ht.
have hc : ((hausdorff_normalisation R 1)*(1`!)%:R)%R= 1%R.
  by rewrite /hausdorff_normalisation euclidean_unit_ball_volume1 expr1 /= mulr1 divff // pnatr_eq0.
have hh := @exterior_convex_integral_geometric_bound R n 1 h1n t (ltn0Sn 0) ht A.
by rewrite hc mul1e in hh.
Qed.

(** Source for [convex_integral_null_exterior_regression]:
    zero-target-mass consequence of 2.10.37,
    p. 198. A Q_t^m-null set is
    T^m-null without any measurability hypothesis
    on the target. Infinite exponents are allowed. *)
Example convex_integral_null_exterior_regression (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (0<m)%N -> (1<=t)%E ->
  @convex_integral_geometric_measure R n m hmn t A= 0%E ->
  @exterior_diameter_measure R n m A= 0%E.
Proof.
move=> hm ht hz.
have hh := @federer_2_10_37 R n m hmn t hm ht A.
rewrite hz mule0 in hh.
apply/eqP; rewrite eq_le hh /=.
exact: measure_nonnegative (exterior_diameter_measure_is_measure R n m) A.
Qed.

Local Open Scope ring_scope.

(** Source for [empty_compact_box_endpoint_regression]: local
    nonempty-source correction to 2.10.38, p. 198.
    Already in the real line an empty compact set cannot
    supply the required endpoint families. *)
Example empty_compact_box_endpoint_regression (R : realType) :
  compact (@set0 (inner_metric_space (@euclidean_inner_productP R 1))) /\
  ~ exists a b : 'I_1 -> inner_metric_space (@euclidean_inner_productP R 1),
    forall i, set0 (a i) /\ set0 (b i).
Proof. exact: empty_compact_enclosing_box_endpoint_counterexample. Qed.

(** Source for [singleton_box_zero_widths_regression]: zero-
    diameter boundary of 2.10.38, p. 199.
    The sealed maximal-chord frame exists for a singleton
    in every dimension and every one of its widths is zero. *)
Example singleton_box_zero_widths_regression (R : realType) n
    (p : inner_metric_space (@euclidean_inner_productP R n)) :
  exists D : greedy_chord_frame_data R n,
    is_greedy_chord_frame [set p] D /\ forall i, greedy_chord_length D i=0%R.
Proof.
have hc := @compact_set1 (inner_metric_space (@euclidean_inner_productP R n)) p.
have hne : [set p] !=set0 by exists p.
pose D := @compact_greedy_chord_frame R n [set p] hc hne.
have hD := @compact_greedy_chord_frame_specification R n [set p] hc hne.
exists D; split=> //; exact: greedy_chord_singleton_width hD.
Qed.

(** Source for [zero_dimensional_box_volume_regression]: empty-
    coordinate boundary of 2.10.38, pp. 198–199,
    with the rectangular-box volume convention of 2.7.16,
    p. 136. The box is the whole singleton space
    and its actual zero-dimensional Lebesgue mass is one. *)
Example zero_dimensional_box_volume_regression (R : realType) origin e c Q :
  @is_euclidean_rectangular_box R 0 origin e c Q ->
  Q=setT /\ @euclidean_lebesgue_measure R 0 Q= 1%E.
Proof.
move=> hQ; split; first exact: euclidean_box_dimension_zero hQ.
by rewrite (euclidean_box_volume hQ) big_ord0.
Qed.

(** Source for [empty_prefix_chord_norm_regression]: empty
    initial product boundary of 2.10.38, pp. 198–199.
    Its norm is one for any specified frame, even
    when all positive-degree widths are zero. *)
Example empty_prefix_chord_norm_regression (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (D : greedy_chord_frame_data R n) (hD : is_greedy_chord_frame S D) :
  exterior_difference_norm (family_prefix (leq0n n) (greedy_chord_first D))
    (family_prefix (leq0n n) (greedy_chord_second D))= 1%R.
Proof. by rewrite (greedy_chord_prefix_norm hD) big_ord0. Qed.

(** Source for [nonconvex_two_point_enclosing_box_regression]:
    arbitrary-compact-source requirement in 2.10.38, p. 198.
    A two-point subset of the real line is nonconvex
    but still admits the specified enclosing rectangular box.
    This guards against adding a convexity premise. *)
Example nonconvex_two_point_enclosing_box_regression (R : realType) :
  let E := inner_metric_space (@euclidean_inner_productP R 1) in
  let C : set E := [set 0%R] `|` [set @coordinate_basis R 1 ord0] in
  ~ is_inner_convex C /\ exists origin e c Q,
    is_euclidean_rectangular_box origin e c Q /\ C `<=` Q.
Proof.
move=> E C.
pose u : E := @coordinate_basis R 1 ord0.
have h0 : C 0%R by left.
have hu : C u by right.
have hhalf0 : (2:R)^-1!=0%R by rewrite invr_eq0 pnatr_eq0.
have hhalf1 : (2:R)^-1<1%R by rewrite invf_lt1 ?ltr1n // ltr0n.
have hn : ~ is_inner_convex C.
  move=> hC.
  have hh := inner_convex_midpoint hC h0 hu.
  rewrite add0r in hh.
  have [hh0|hh1] := hh.
  - have he := congr1 (fun x : E=>x ord0) hh0.
    rewrite /u /coordinate_basis !ffunE eqxx in he.
    change ((2:R)^-1*1=0%R) in he.
    by rewrite mulr1 in he; move: hhalf0; rewrite he eqxx.
  - have he := congr1 (fun x : E=>x ord0) hh1.
    rewrite /u /coordinate_basis !ffunE eqxx in he.
    change ((2:R)^-1*1= 1%R) in he.
    by rewrite mulr1 in he; move: hhalf1; rewrite he ltxx.
split=> //.
have hc : compact C by apply: compactU; exact: compact_set1.
have hne : C !=set0 by exists 0%R.
have [a [b [e [c [origin [Q [_ [hQ [hCQ _]]]]]]]]] :=
  @federer_2_10_38 R 1 C hc hne.
by exists origin,e,c,Q.
Qed.

(** Source for [closed_interval_upper_endpoint_grid_regression]:
    endpoint boundary of the subdivision used in 2.10.39,
    p. 199. A one-cell closed side covers its upper
    endpoint within half its length of the chosen midpoint. *)
Example closed_interval_upper_endpoint_grid_regression (R : realType) (c : R) (hc : 0<=c) :
  let node := @equal_interval_partition R c 1 hc (ltnSn 0) in
  `|c-(node 0+node 1)/2|<=c/2.
Proof.
cbv zeta.
have hP := @equal_interval_partition_specification R c 1 hc (ltnSn 0).
rewrite (equal_interval_initial_law hP) (equal_interval_final_law hP) add0r ler_norml.
apply/andP; split; lra.
Qed.

(** Source for [empty_rectangular_grid_regression]: empty-
    coordinate product boundary of the finite counting
    argument in 2.10.39, p. 199. The grid
    contains exactly one empty choice of cell indices. *)
Example empty_rectangular_grid_regression (count : 'I_0 -> nat) :
  #|rectangular_grid_indices count|= 1%N.
Proof. by rewrite rectangular_grid_cardinality big_ord0. Qed.

(** Source for [zero_dimensional_positive_spherical_regression]:
    zero-dimensional ambient boundary of 2.10.39,
    p. 199. Positive-degree spherical measure vanishes
    on every subset, by the above-dimension argument. *)
Example zero_dimensional_positive_spherical_regression (R : realType) m
    (A : set (inner_metric_space (@euclidean_inner_productP R 0))) :
  (0<m)%N -> @spherical_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 0)] m A= 0%E.
Proof. exact: euclidean_spherical_above_dimension_zero. Qed.

(** Source for [line_degree_two_spherical_regression]: above-
    ambient degree allowed in 2.10.39, p. 199,
    since 2.10.3, pp. 171–172, has no m<=n
    restriction. Every subset of the line has zero
    two-dimensional spherical measure. *)
Example line_degree_two_spherical_regression (R : realType)
    (A : set (inner_metric_space (@euclidean_inner_productP R 1))) :
  @spherical_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)] 2 A= 0%E.
Proof. exact: euclidean_spherical_above_dimension_zero. Qed.

(** Source for [line_spherical_exterior_coefficient_regression]:
    n=m=1 coefficient in 2.10.39, p. 199.
    The printed factor is exactly one; the target
    need not be measurable or have finite mass. *)
Example line_spherical_exterior_coefficient_regression (R : realType)
    (A : set (inner_metric_space (@euclidean_inner_productP R 1))) :
  (@spherical_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)] 1 A<=
    @exterior_diameter_measure R 1 1 A)%E.
Proof.
have hh := @federer_2_10_39 R 1 1 A (ltnSn 0).
by rewrite sqrtr1 expr1n expr0 mulr1 mul1e in hh.
Qed.

(** Source for [degenerate_plane_box_cutoff_regression]: zero-
    width box boundary of the subdivision argument in
    2.10.39, p. 199. A planar rectangle with
    second width zero has zero two-dimensional spherical
    cutoff content at every positive cutoff. *)
Example degenerate_plane_box_cutoff_regression (R : realType) origin axis
    (c : 'I_2 -> R) Q (d : R)
    (nu : set (inner_metric_space (@euclidean_inner_productP R 2)) -> \bar R) :
  @is_euclidean_rectangular_box R 2 origin axis c Q ->
  (forall i j : 'I_2, (i<=j)%N -> c j<=c i) -> c ord_max=0%R -> 0<d ->
  is_metric_scale_envelope
    (fun j : @positive_closed_metric_balls R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)] => val j)
    (fun j=>hausdorff_diameter_cost 2 (val j)) d%:E nu -> nu Q= 0%E.
Proof.
move=> hQ hs hz hd hn.
have hi : (Ordinal (ltnSn 1) : 'I_2)=ord_max by exact: val_inj.
have hcap : Num.sqrt (2:R)*c (Ordinal (ltnSn 1))<d by rewrite hi hz mulr0.
have hh := @rectangular_spherical_cutoff_bound R 2 1 (ltnSn 1) origin axis c Q d nu hQ hs hcap hn.
have hp : (\prod_(i<2) family_prefix (ltnSn 1) c i)=0%R.
  by rewrite (bigD1 ord_max) //= family_prefix_refl hz mul0r.
rewrite hp mulr0 in hh.
have hm := metric_scale_envelope_is_measure hn (fun j=>hausdorff_diameter_cost_nonnegative 2 (val j)).
by apply/eqP; rewrite eq_le hh (measure_nonnegative hm).
Qed.

(** Source for [single_weighted_ball_minimum_regression]:
    singleton parameter-family boundary of 2.10.40,
    pp. 199–200. The opaque chosen minimum of
    one ball of any positive radius has scale zero
    and the prescribed centre, without inspecting its implementation. *)
Example single_weighted_ball_minimum_regression (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n)) (r : R) :
  0<r -> exists D : weighted_ball_minimum_data R n,
    is_weighted_ball_minimum [set (a,r)] D /\
    weighted_minimum_scale D=0 /\ weighted_minimum_centre D=a.
Proof.
move=> hr.
pose P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o) := [set (a,r)].
have hP : compact P by exact: compact_set1.
have hne : P !=set0 by exists (a,r).
have hpos : positive_ball_parameter_family P by move=> p ->.
pose D := @compact_weighted_ball_minimum R n P hP hne hpos.
have hD := @compact_weighted_ball_minimum_specification R n P hP hne hpos.
exists D; split=> //.
apply: (@weighted_ball_common_centre_minimum R n P D a hne hD).
by move=> p ->.
Qed.

(** Source for [zero_dimensional_weighted_minimum_regression]:
    dimension-zero boundary of 2.10.40, pp. 199–200.
    Every nonempty parameter family with the proved
    minimum laws has zero scale and the unique empty vector. *)
Example zero_dimensional_weighted_minimum_regression (R : realType) P D :
  P !=set0 -> @is_weighted_ball_minimum R 0 P D ->
  weighted_minimum_scale D=0 /\ weighted_minimum_centre D=0.
Proof.
move=> hne hD.
apply: (@weighted_ball_common_centre_minimum R 0 P D 0 hne hD).
move=> p hp; exact: coordinate_zero.
Qed.

(** Source for [unequal_radii_common_centre_regression]:
    radius variation allowed by 2.10.40, pp. 199–200.
    Two positive but unequal prescribed radii at the
    same centre still give a zero minimum scale. *)
Example unequal_radii_common_centre_regression (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n)) D :
  @is_weighted_ball_minimum R n ([set (a,(1:R))] `|` [set (a,(2:R))]) D ->
  weighted_minimum_scale D=0 /\ weighted_minimum_centre D=a.
Proof.
move=> hD.
have hne : ([set (a,(1:R))] `|` [set (a,(2:R))]) !=set0.
  exists (a,1); by left.
apply: (@weighted_ball_common_centre_minimum R n _ D a hne hD).
by move=> p [->|->].
Qed.

(** Source for [zero_scale_contact_singleton_regression]:
    contact-set boundary of 2.10.40, pp. 199–200.
    At minimum scale zero every genuine contact centre
    is the minimum centre; the set is not empty. *)
Example zero_scale_contact_singleton_regression (R : realType) n P D :
  P !=set0 -> @is_weighted_ball_minimum R n P D -> weighted_minimum_scale D=0 ->
  weighted_ball_contact_centres P (weighted_minimum_centre D) (weighted_minimum_scale D)=
    [set weighted_minimum_centre D].
Proof.
move=> hne hD hc.
have hb := weighted_minimum_feasible_law hD.
rewrite hc in hb *; exact: weighted_ball_zero_scale_contacts hne hb.
Qed.

(** Source for [empty_weighted_ball_family_regression]:
    nonempty-family hypothesis of 2.10.40, pp. 199–200.
    With no prescribed balls the zero-scale feasible
    set is the whole line, which has distinct points.
    Thus the printed nonemptiness condition is essential. *)
Example empty_weighted_ball_family_regression (R : realType) :
  @weighted_ball_centres R 1 set0 0=setT /\
  @euclidean_one_embed R 0!=euclidean_one_embed 1.
Proof.
split.
- apply/seteqP; split=> y _; first exact I.
  by move=> p [].
- apply/eqP=> he.
  have hh := congr1 (@euclidean_one_project R) he.
  rewrite !euclidean_one_embedK in hh.
  have h01 : (0:R)<1 := ltr01.
  by rewrite hh ltxx in h01.
Qed.

(** Source for [jung_line_factor_regression]: sharp
    one-dimensional coefficient in 2.10.41, p. 200.
    Jung's diameter bound reduces exactly to d on the line. *)
Example jung_line_factor_regression (R : realType) (d : R) :
  @jung_factor R 1*d=d.
Proof. by rewrite jung_factor_line mul1r. Qed.

(** Source for [zero_ambient_jung_minimum_regression]:
    dimension-zero boundary of the auxiliary nonnegative-
    diameter form of 2.10.41, p. 200. Every
    nonempty source has minimum radius zero and the
    unique empty-vector centre. *)
Example zero_ambient_jung_minimum_regression (R : realType)
    (S : set (inner_metric_space (@euclidean_inner_productP R 0))) :
  S !=set0 -> exists b r, is_minimum_enclosing_ball S b r /\ b=0 /\ r=0.
Proof.
move=> hne.
have hdiam : (extended_metric_diameter S<=0)%E by rewrite euclidean_zero_dimensional_diameter.
have [b [r [hmin [hbound _]]]] := @bounded_jung_minimum_ball R 0 S 0 hne (lexx 0) hdiam.
have hr := minimum_ball_radius_nonnegative_law hmin.
rewrite mulr0 in hbound.
have hr0 : r=0 by lra.
exists b,r; split=> //; split=> //; exact: coordinate_zero.
Qed.

(** Source for [self_closed_ball_minimum_regression]:
    actual-diameter meaning of the minimum in 2.10.41,
    p. 200. In positive ambient dimension, a
    closed ball is a minimum enclosing ball of itself,
    including radius zero, by monotonicity of actual diameter. *)
Example self_closed_ball_minimum_regression (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n.+1)) (r : R) :
  0<=r -> is_minimum_enclosing_ball (metric_closed_ball a r) a r.
Proof.
move=> hr; constructor=> // z t ht hcover.
have hh := @extended_metric_diameter_mono R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n.+1)]
  (metric_closed_ball a r) (metric_closed_ball z t) hcover.
rewrite !euclidean_closed_ball_diameter // lee_fin in hh; lra.
Qed.

(** Source for [open_ball_jung_minimum_regression]: nonclosed
    source allowed by 2.10.41, p. 200. The
    complete theorem applies to an open Euclidean ball
    of any positive radius using its actual diameter,
    without a compactness premise on that source. *)
Example open_ball_jung_minimum_regression (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n.+1)) (r : R) :
  0<r -> exists b t,
    is_minimum_enclosing_ball [set x | mdist a x<r] b t /\
    (extended_metric_diameter (metric_closed_ball b t)<=(@jung_factor R n.+1*(r+r))%:E)%E.
Proof.
move=> hr.
have hd : 0<r+r := addr_gt0 hr hr.
have hdiam := @euclidean_open_ball_diameter R n a r hr.
have [b [t [hmin [hbound _]]]] := @federer_2_10_41 R n.+1 _ (r+r) hd hdiam.
by exists b,t.
Qed.

(** Source for [zero_dimensional_convex_support_regression]: finite contact
    representation used in 2.10.41, p. 200 In dimension zero the at-most-n+1
    representation uses exactly one point, so the construction never returns
    an empty convex combination. *)
Example zero_dimensional_convex_support_regression (R : realType)
    (A : set (R_n R 0)) (b : R_n R 0) :
  A !=set0 -> convex_hull A b -> exists a, A a /\ b=a.
Proof.
move=> hne hb.
have [k [u [w [/andP [hk hk1] [hu [hw [hsum hvalue]]]]]]] :=
  @convex_hull_finite_support R (R_n R 0) 0 (@coordinate_basis R 0) A b
    (@coordinate_basisP R 0) hne hb.
have hk0 : k= 1%N by apply/eqP; rewrite eqn_leq hk1 hk.
subst k.
have hw1 : w ord0= 1.
  move: hsum; rewrite big_ord_recr big_ord0.
  change (0+w ord_max= 1 -> w ord0= 1).
  by rewrite add0r (ord1 ord_max).
exists (u ord0); split; first exact: hu.
move: hvalue; rewrite big_ord_recr big_ord0.
change (b=0+w ord_max*:u ord_max -> b=u ord0).
by rewrite add0r (ord1 ord_max) hw1 scale1r.
Qed.

(** Source for [degree_zero_jung_comparison_regression]: empty-
    power boundary of 2.10.42, p. 201. The
    coefficient is one and spherical and Hausdorff
    degree-zero measures agree for every Euclidean target. *)
Example degree_zero_jung_comparison_regression (R : realType) n
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @spherical_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] 0 A=
  @hausdorff_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] 0 A.
Proof.
have hh := @federer_2_10_42 R n 0 A.
rewrite expr0 mul1e in hh.
apply/eqP; rewrite eq_le hh; exact: hausdorff_measure_le_spherical_measure.
Qed.

(** Source for [line_jung_measure_equality_regression]: exact
    one-dimensional coefficient of 2.10.42, p. 201.
    All natural-degree spherical and Hausdorff measures
    agree on every subset of the line, without
    measurability or finite-mass assumptions. *)
Example line_jung_measure_equality_regression (R : realType) m
    (A : set (inner_metric_space (@euclidean_inner_productP R 1))) :
  @spherical_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)] m A=
  @hausdorff_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)] m A.
Proof.
have hh := @federer_2_10_42 R 1 m A.
rewrite jung_factor_line expr1n mul1e in hh.
apply/eqP; rewrite eq_le hh; exact: hausdorff_measure_le_spherical_measure.
Qed.

(** Source for [zero_radius_spherical_cutoff_regression]: zero-
    radius boundary of the containing-ball replacement
    in 2.10.42, p. 201. At every positive
    cutoff, a singleton has zero degree-one content,
    using only strictly positive-radius spherical generators. *)
Example zero_radius_spherical_cutoff_regression (R : realType) (X : metricType R)
    (a : X) (t : R) (nu : set X -> \bar R) :
  0<t -> is_metric_scale_envelope (fun j : @positive_closed_metric_balls R X=>val j)
    (fun j=>hausdorff_diameter_cost 1 (val j)) t%:E nu -> (nu [set a]<=0)%E.
Proof.
move=> ht hn.
have hcover : [set a] `<=` metric_closed_ball a 0.
  move=> x hx; change (is_true (mdist a x<=0)).
  have he : x=a := hx; by rewrite he mdistxx.
have hcap : 0+0<t by rewrite add0r.
have hh := @spherical_cutoff_containing_ball_bound R X 1 nu [set a] a 0 t
  hn hcover (lexx 0) hcap.
by rewrite add0r hausdorff_power_cost_finite expr1 mulr0 in hh.
Qed.

(** Source for [zero_ambient_degree_zero_jung_regression]:
    simultaneous ambient-zero and degree-zero boundary of
    2.10.42, p. 201. The spherical mass of
    the unique point is one, with coefficient 0^0=1. *)
Example zero_ambient_degree_zero_jung_regression (R : realType) :
  @spherical_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 0)] 0 [set 0]= 1%E.
Proof.
rewrite degree_zero_jung_comparison_regression; exact: hausdorff_zero_singleton.
Qed.

(** Source for [empty_source_kirszbraun_regression]: empty-
    source and zero-bound boundary of 2.10.43,
    p. 201. The opaque extension has constant
    value globally; the specification does not expose
    which constant its private witness selected. *)
Example empty_source_kirszbraun_regression (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) :
  exists g, is_kirszbraun_extension set0 f g 0 /\ forall x, g x=g 0.
Proof.
have hf : is_metric_lipschitz_bound set0 f 0.
  split; first exact: lexx.
  by move=> x y [].
pose g := @euclidean_lipschitz_extension R m n set0 f 0 hf.
have hg := @euclidean_lipschitz_extension_specification R m n set0 f 0 hf.
exists g; split=> // x.
have hh := (kirszbraun_extension_bound_law hg).2 x 0 I I.
rewrite mul0r in hh.
have hz : mdist (g x) (g 0)=0 by apply/eqP; rewrite eq_le hh (mdist_ge0 _ _).
exact: mdist_positivity hz.
Qed.

(** Source for [singleton_source_kirszbraun_regression]: singleton-
    source boundary of 2.10.43, p. 201. At
    bound zero the opaque extension is everywhere
    equal to the original value at the prescribed point. *)
Example singleton_source_kirszbraun_regression (R : realType) m n
    (a : inner_metric_space (@euclidean_inner_productP R m))
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) :
  exists g, is_kirszbraun_extension [set a] f g 0 /\ forall x, g x=f a.
Proof.
have hf : is_metric_lipschitz_bound [set a] f 0.
  split; first exact: lexx.
  move=> x y hx hy; have hxa : x=a := hx; have hya : y=a := hy.
  by rewrite hxa hya mdistxx mul0r.
pose g := @euclidean_lipschitz_extension R m n [set a] f 0 hf.
have hg := @euclidean_lipschitz_extension_specification R m n [set a] f 0 hf.
exists g; split=> // x.
have hh := (kirszbraun_extension_bound_law hg).2 x a I I.
rewrite mul0r in hh.
have hz : mdist (g x) (g a)=0 by apply/eqP; rewrite eq_le hh (mdist_ge0 _ _).
have he : g x=g a := @mdist_positivity R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] (g x) (g a) hz.
rewrite he; exact (@kirszbraun_extension_agreement_law R m n [set a] f g 0 hg a erefl).
Qed.

(** Source for [zero_target_kirszbraun_regression]: target-
    dimension-zero boundary of 2.10.43, p. 201.
    Every original map has bound zero and the
    opaque global extension takes the unique empty-vector value. *)
Example zero_target_kirszbraun_regression (R : realType) m S
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R 0)) :
  exists g, is_kirszbraun_extension S f g 0 /\ forall x, g x=0.
Proof.
have hf : is_metric_lipschitz_bound S f 0.
  split; first exact: lexx.
  move=> x y hx hy.
  have hx0 : f x=0 by exact: coordinate_zero.
  have hy0 : f y=0 by exact: coordinate_zero.
  by rewrite hx0 hy0 mdistxx mul0r.
pose g := @euclidean_lipschitz_extension R m 0 S f 0 hf.
exists g; split; first exact: euclidean_lipschitz_extension_specification.
move=> x; exact: coordinate_zero.
Qed.

(** Source for [zero_source_dimension_kirszbraun_regression]:
    source-dimension-zero boundary of 2.10.43, p. 201.
    An arbitrary map on any subset of the one-point
    source has a global extension at bound zero. *)
Example zero_source_dimension_kirszbraun_regression (R : realType) n S
    (f : inner_metric_space (@euclidean_inner_productP R 0) ->
      inner_metric_space (@euclidean_inner_productP R n)) :
  exists g, is_kirszbraun_extension S f g 0.
Proof.
have hf : is_metric_lipschitz_bound S f 0.
  split; first exact: lexx.
  move=> x y hx hy.
  have hx0 : x=0 by exact: coordinate_zero.
  have hy0 : y=0 by exact: coordinate_zero.
  by rewrite hx0 hy0 mdistxx mul0r.
exists (@euclidean_lipschitz_extension R 0 n S f 0 hf).
exact: euclidean_lipschitz_extension_specification.
Qed.

(** Source for [identity_kirszbraun_optimal_regression]: exact
    optimal-constant conclusion of 2.10.43, p. 201,
    on the entire positive-dimensional Euclidean source.
    The extension is the identity and its least
    Lipschitz constant is exactly one. *)
Example identity_kirszbraun_optimal_regression (R : realType) n :
  exists g : inner_metric_space (@euclidean_inner_productP R n.+1) ->
      inner_metric_space (@euclidean_inner_productP R n.+1),
    exists hg : is_metric_lipschitz setT g,
      (forall x, g x=x) /\ metric_lipschitz_constant hg= 1.
Proof.
pose E := inner_metric_space (@euclidean_inner_productP R n.+1).
have hId : is_metric_lipschitz_bound setT (fun x : E=>x) 1.
  split; first exact: ler01.
  by move=> x y _ _; rewrite mul1r.
have hLip : is_metric_lipschitz setT (fun x : E=>x) := metric_lipschitz_of_bound hId.
have hL1 : metric_lipschitz_constant hLip= 1.
  have hup := metric_lipschitz_constant_minimal hLip hId.
  pose e : E := @coordinate_basis R n.+1 ord0.
  have hd : mdist (0 : E) e= 1.
    by rewrite inner_metric_distanceE sub0r inner_normN /e euclidean_coordinate_unit_norm.
  have hlow := @metric_lipschitz_constant_attained R [the metricType R of E]
    [the metricType R of E] setT (fun x : E=>x) hLip 0 e I I.
  rewrite hd mulr1 in hlow.
  by apply/eqP; rewrite eq_le hup hlow.
have [g [hg [hag heq]]] := @federer_2_10_43 R n.+1 n.+1 setT (fun x : E=>x) hLip.
exists g,hg; split; first by move=> x; exact: hag x I.
by rewrite heq hL1.
Qed.

(** Source for [scaled_identity_kirszbraun_regression]: arbitrary-
    scale normalisation in 2.10.43, p. 201.
    On the whole source, the opaque extension of
    L times the identity agrees everywhere with
    that map, for every nonnegative L including zero. *)
Example scaled_identity_kirszbraun_regression (R : realType) n (L : R) :
  0<=L -> exists g : inner_metric_space (@euclidean_inner_productP R n) ->
      inner_metric_space (@euclidean_inner_productP R n),
    is_kirszbraun_extension setT (fun x=>L*:x) g L /\ forall x, g x=L*:x.
Proof.
move=> hL.
pose E := inner_metric_space (@euclidean_inner_productP R n).
have hId : is_metric_lipschitz_bound setT (fun x : E=>x) 1.
  split; first exact: ler01.
  by move=> x y _ _; rewrite mul1r.
have hf : is_metric_lipschitz_bound setT (fun x : E=>L*:x) L.
  have hh := @euclidean_scaled_lipschitz_bound R n n setT (fun x : E=>x) 1 L hId.
  by rewrite (ger0_norm hL) mulr1 in hh.
pose g := @euclidean_lipschitz_extension R n n setT (fun x : E=>L*:x) L hf.
have hg := @euclidean_lipschitz_extension_specification R n n setT (fun x : E=>L*:x) L hf.
exists g; split=> // x.
exact (@kirszbraun_extension_agreement_law R n n setT (fun x : E=>L*:x) g L hg x I).
Qed.

Local Open Scope ring_scope.

(** Source for [supremum_norm_noninner_regression]: the
    non-inner-product source norm of 2.10.44,
    p. 202. This rules out recovering the
    counterexample from an accidentally Euclidean source metric. *)
Example supremum_norm_noninner_regression (R : realType) :
  is_real_norm (@plane_supremum_norm R) /\
  ~ exists B : R_n R 2 -> R_n R 2 -> R,
    exists hB : is_inner_product B, forall x, inner_norm hB x=plane_supremum_norm x.
Proof. split; [exact: plane_supremum_normP|exact: plane_supremum_norm_not_inner]. Qed.

(** Source for [corner_diagonal_correction_regression]: local
    distinct-point qualification of the distance-two
    sentence in 2.10.44, p. 202. *)
Example corner_diagonal_correction_regression (R : realType) :
  kirszbraun_corner_source (kirszbraun_corner_first R) /\
  @mdist R [the metricType R of plane_supremum_metric R]
    (kirszbraun_corner_first R) (kirszbraun_corner_first R)= 0.
Proof. split; [exact: (kirszbraun_corner_members R).1|exact: mdistxx]. Qed.

(** Source for [equilateral_unit_balls_regression]: direct
    target obstruction from 2.10.44, p. 202,
    with the actual Euclidean target metric. *)
Example equilateral_unit_balls_regression (R : realType) :
  ~ exists p : inner_metric_space (@euclidean_inner_productP R 2),
    mdist p (kirszbraun_equilateral_first R)<=1 /\
    mdist p (kirszbraun_equilateral_second R)<=1 /\
    mdist p (kirszbraun_equilateral_third R)<=1.
Proof. exact: kirszbraun_three_unit_balls_empty. Qed.

(** Source for [corner_map_nonextension_regression]: full
    printed map counterexample from 2.10.44,
    p. 202, using only its public opaque map. *)
Example corner_map_nonextension_regression (R : realType) :
  exists hLip : is_metric_lipschitz (@kirszbraun_corner_source R) (@kirszbraun_corner_map R),
    metric_lipschitz_constant hLip= 1 /\
    ~ exists g : plane_supremum_metric R -> inner_metric_space (@euclidean_inner_productP R 2),
      (forall x, kirszbraun_corner_source x -> g x=kirszbraun_corner_map x) /\
      is_metric_lipschitz_bound ((@kirszbraun_corner_source R) `|` [set 0]) g 1.
Proof. exact: federer_2_10_44_counterexample. Qed.

(** Source for [empty_scalar_infimum_regression]: local empty-source
    qualification of the formula in 2.10.44, p. 202 The real line contains
    an ambient point. *)
Example empty_scalar_infimum_regression (R : realType) :
  ~ exists g : real_line_metric R -> R,
    is_mcshane_envelope set0 (fun _ : real_line_metric R=>0) 0 g.
Proof.
exact (@empty_source_no_finite_mcshane_envelope R [the metricType R of real_line_metric R]
  (fun _=>0) 0 0).
Qed.

(** Source for [zero_bound_scalar_envelope_regression]: zero-
    bound boundary of the infimum formula in
    2.10.44, p. 202. On any nonempty
    metric source its abstract envelope is globally
    the constant original value, with no boundedness hypothesis. *)
Example zero_bound_scalar_envelope_regression (R : realType) (X : metricType R)
    (S : set X) (f g : X -> R) a :
  S a -> is_metric_lipschitz_bound S (f : X -> real_line_metric R) 0 ->
    is_mcshane_envelope S f 0 g -> forall x, g x=f a.
Proof.
move=> ha hf hg x.
have hb := (@mcshane_envelope_lipschitz R X S f 0 g (lexx 0) hg).2 x a I I.
rewrite mul0r real_line_metric_distanceE in hb.
have hz : `|g x-g a|=0 by apply/eqP; rewrite eq_le hb normr_ge0.
have hxa : g x=g a by apply/eqP; rewrite -subr_eq0 -normr_eq0 hz.
rewrite hxa; exact (@mcshane_envelope_agreement R X S f 0 g hf hg a ha).
Qed.

(** Source for [empty_scalar_extension_regression]: arbitrary-
    source extension assertion in 2.10.44,
    p. 202, including the empty original source,
    whose optimal bound is zero. This remains
    true although the finite infimum formula fails. *)
Example empty_scalar_extension_regression (R : realType) (X : metricType R) (f : X -> R) :
  exists g : X -> R, exists hg : is_metric_lipschitz setT (g : X -> real_line_metric R),
    metric_lipschitz_constant hg=0.
Proof.
have hb : is_metric_lipschitz_bound set0 (f : X -> real_line_metric R) 0.
  split; first exact: lexx.
  by move=> x y [].
have hf := metric_lipschitz_of_bound hb.
have [g [hg [_ heq]]] := @federer_2_10_44_scalar R X set0 f hf.
exists g,hg; rewrite heq.
apply/eqP; rewrite eq_le (metric_lipschitz_constant_minimal hf hb)
  (metric_lipschitz_constant_nonnegative hf); by [].
Qed.

(** Source for [whole_metric_source_scalar_regression]: full-
    source boundary of 2.10.44, p. 202.
    On an arbitrary inhabited metric space the
    infimum extension agrees everywhere with the
    original Lipschitz map and preserves its optimum. *)
Example whole_metric_source_scalar_regression (R : realType) (X : metricType R)
    (f : X -> R) (a : X)
    (hf : is_metric_lipschitz setT (f : X -> real_line_metric R)) :
  exists g : X -> R, exists hg : is_metric_lipschitz setT (g : X -> real_line_metric R),
    (forall x, g x=f x) /\ metric_lipschitz_constant hg=metric_lipschitz_constant hf /\
    forall x, g x=inf (mcshane_costs_at setT f (metric_lipschitz_constant hf) x).
Proof.
have hne : ([set: X] !=set0) by exists a.
have [g [hg [hag [heq hformula]]]] := @federer_2_10_44_scalar_formula R X setT f hf hne.
exists g,hg; split; first by move=> x; exact: hag x I.
by split.
Qed.

(** Source for [hausdorff_product_empty_factor_regression]: empty-second-
    factor boundary of 2.10.45, pp. 202–203. Even an
    arbitrary nonmeasurable or unbounded first factor gives zero. *)
Example hausdorff_product_empty_factor_regression (R : realType) m k (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) U :
  hausdorff_product_slice_measure first second set0 (k+m) U=0%E.
Proof.
apply: (@hausdorff_product_slice_null_factor R m k P Y pair first second hp set0 _ U).
exact: measure_empty (@hausdorff_measure_is_measure R Y k).
Qed.

(** Source for [hausdorff_product_zero_dimension_regression]: zero-
    Euclidean-dimension boundary of 2.10.45, pp. 202–203.
    Both coefficient endpoints force c=1, so the product
    formula retains the unit mass of the zero-dimensional factor. *)
Example hausdorff_product_zero_dimension_regression (R : realType) k (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R 0) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) V :
  (hausdorff_measure k V< +oo)%E -> forall U,
  measure_measurable (@euclidean_lebesgue_measure R 0) U ->
  hausdorff_product_slice_measure first second V k U=
    (euclidean_lebesgue_measure 0 U*hausdorff_measure k V)%E.
Proof.
move=> hV U hU.
have [c [hl [hu he]]] := @hausdorff_euclidean_product_coefficient R 0 k P Y pair first second hp V hV.
rewrite /euclidean_product_lower_coefficient addn0 euclidean_unit_ball_volume0 mulr1 divff in hl;
  last exact: lt0r_neq0 (euclidean_unit_ball_volumeE R k).2.
rewrite euclidean_product_coefficient_zero_first_dimension in hu.
have hc : c= 1 by apply/eqP; rewrite eq_le hu hl.
have hh := he U hU; by rewrite addn0 hc mul1e in hh.
Qed.

(** Source for [zero_diameter_positive_mesh_regression]: zero-
    diameter repair of the positive-mesh covering argument
    in 2.10.45, p. 203. A length cost bounded by
    every positive mesh is zero, even when the initially
    bounded quantity is an extended-real value. *)
Example zero_diameter_positive_mesh_regression (R : realType) (x : \bar R) :
  (forall h : R, 0<h -> h<1 -> (x<=h%:E)%E) -> (x<=0)%E.
Proof.
move=> hb.
have hh : (x<=(1*(hausdorff_normalisation R 1*0^+1))%R%:E)%E.
  apply: (@positive_mesh_cost_limit R 1 0 1 1 x ltr01 (lexx 0) ltr01)=> h hpos _ hlt.
  rewrite hausdorff_normalisation_one expr1 !mul1r; exact: hb h hpos hlt.
by rewrite hausdorff_normalisation_one expr1 mulr0 mul1r in hh.
Qed.

(** Source for [gross_finite_null_first_factor_regression]: regression
    for the finite positive second-factor case of 2.10.46,
    pp. 203–204. A Lebesgue-null first factor gives a
    Gross-null product without a Borel hypothesis on either factor. *)
Example gross_finite_null_first_factor_regression (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) (v : R) :
  (k<=n)%N -> (0<v)%R -> euclidean_lebesgue_measure m.+1 U=0 ->
  @gross_measure R n k V=v%:E ->
  @gross_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)=0.
Proof.
move=> hkn hv hU hV.
have hh := @gross_finite_product_upper_bound R m n k U V 0 v hkn (lexx 0%R) hv hU hV.
rewrite mul0r in hh; apply/eqP; rewrite eq_le hh /=.
apply: (measure_nonnegative (@gross_measure_is_measure R (m.+1+n) (m.+1+k) _)).
by rewrite leq_add2l.
Qed.

(** Source for [ball_product_zero_relative_scale_regression]: regression
    for the diameter-zero second-factor endpoint of the displayed
    generator estimate in 2.10.46, p. 203. The first
    ball may itself have radius zero. *)
Example ball_product_zero_relative_scale_regression (R : realType) m n k
    (a : inner_metric_space (@euclidean_inner_productP R m)) (r : R)
    (T : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> (0<=r)%R -> extended_metric_diameter T=0 ->
  (projected_volume_gauge (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) (metric_closed_ball a r) T)<=
    euclidean_lebesgue_measure m (metric_closed_ball a r)*projected_volume_gauge k T)%E.
Proof.
move=> hkn hr hT.
have hd : (extended_metric_diameter T<=((r+r)*0)%R%:E)%E by rewrite hT mulr0.
have hh := @ball_product_projected_volume_gauge_bound R m n k a r 0 T hkn hr (lexx 0%R) hd.
by rewrite expr0n addr0 sqrtr1 expr1n mule1 in hh.
Qed.

(** Source for [gross_null_second_factor_regression]: regression
    for the proved null endpoint of 2.10.46, p. 204.
    The first set may have infinite Lebesgue volume and may be
    nonmeasurable; zero-dimensional first factors are included. *)
Example gross_null_second_factor_regression (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> @gross_measure R n k V=0%E ->
  @gross_measure R (m+n) (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)=0%E.
Proof. move=> hkn hV; exact (@gross_product_null_second_factor R m n k V hkn hV U). Qed.

(** Source for [convex_null_first_factor_regression]: endpoint
    regression for the Caratheodory product inequality of 2.10.46,
    p. 203. A non-Borel Lebesgue-null first factor is
    permitted when the second Caratheodory mass is finite. *)
Example convex_null_first_factor_regression (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> euclidean_lebesgue_measure m.+1 U=0%E ->
  (@caratheodory_projection_measure R n k V< +oo)%E ->
  @caratheodory_projection_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)=0%E.
Proof.
move=> hkn hU hV.
have hh := @caratheodory_projection_product_upper_finite_second R m n k U V hkn hV.
rewrite hU mul0e in hh; apply/eqP; rewrite eq_le hh /=.
have hdim : (m.+1+k<=m.+1+n)%N by rewrite leq_add2l.
exact (measure_nonnegative (@caratheodory_projection_measure_is_measure R (m.+1+n) (m.+1+k) hdim) _).
Qed.

(** Source for [gross_infinite_second_factor_regression]: endpoint
    regression for the lower Gross inequality in 2.10.46,
    p. 204. Positive finite first volume and infinite
    second mass yield infinite product mass, not the null
    value of an invalid zero-times-infinity simplification. *)
Example gross_infinite_second_factor_regression (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) (u : R) :
  (k<=n)%N -> borel_set U -> borel_set V -> (0<u)%R ->
  euclidean_lebesgue_measure m.+1 U=u%:E -> @gross_measure R n k V=+oo%E ->
  @gross_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)=+oo%E.
Proof.
move=> hkn hU hV hu hvol hinf.
rewrite (@gross_finite_borel_product R m n k U V u hkn hU hV hvol (or_introl hu)) hinf muleC.
by rewrite gt0_mulye // lte_fin.
Qed.

(** Source for [gross_infinite_first_factor_regression]: endpoint
    regression for 2.10.46, p. 204. Infinite first
    outer volume and positive finite second Gross mass force
    infinite product mass without measurability of either factor. *)
Example gross_infinite_first_factor_regression (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> euclidean_lebesgue_measure m U=+oo%E ->
  (0<@gross_measure R n k V)%E -> (@gross_measure R n k V< +oo)%E ->
  @gross_measure R (m+n) (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)=+oo%E.
Proof.
move=> hkn hU hpos hfin.
by rewrite (@gross_product_finite_second R m n k U V hkn hfin) hU gt0_mulye.
Qed.

(** Source for [gross_arbitrary_infinite_factors_regression]:
    infinite-mass endpoint of 2.10.46, p. 204. Both
    factors may be nonmeasurable and have infinite outer mass;
    no countable finite-measure cover of the second set is assumed. *)
Example gross_arbitrary_infinite_factors_regression (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N -> euclidean_lebesgue_measure m U=+oo%E ->
  @gross_measure R n k V=+oo%E ->
  @gross_measure R (m+n) (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)=+oo%E.
Proof.
move=> hkn hU hV; apply: (@gross_arbitrary_product_infinite_second R m n k U V hkn _ hV).
by rewrite hU lt0y.
Qed.

(** Source for [null_scalar_infinite_fibre_regression]: local
    regression supporting 2.10.46, p. 204. The shear
    of a null scalar factor over an infinite transverse fibre
    can have positive scalar multiplicity integral. This guards
    an auxiliary hypothesis, not a correction to Federer. *)
Example null_scalar_infinite_fibre_regression (R : realType) :
  lebesgue_scalar_measure [set (0%R : R)]=0%E /\
  @counting_measure R R `[0%R,1%R]=+oo%E /\
  is_measure_integral (@lebesgue_scalar_measure R) (partial_function_total
    (fun w=>(@mapping_multiplicity R [the choiceType of (R*R)%type] (R*unit)%type
      (fun z=>((z.1+z.2)%R,tt)) ([set 0%R] `*` `[0%R,1%R]) (w,tt) : extended_real_line R))) 1%E.
Proof. exact: null_scalar_infinite_fibre_counterexample. Qed.

(** Source for [projection_kernel_dimension_regression]: endpoint
    regression for the exceptional-set argument supporting 2.10.46,
    p. 204; Freilich (1950), Lemma 4.4, p. 240.
    Positive-dimensional projections annihilate a prescribed nonzero
    vector only on a null set. The zero-dimensional target instead
    gives probability one, so that hypothesis cannot be dropped. *)
Example projection_kernel_dimension_regression (R : realType) n m
    (hmn : (m.+1<=n.+1)%N) (x : R_n R n.+1) : x!=0%R ->
  @orthogonal_projection_probability R n.+1 m.+1 hmn
    [set p | euclidean_projection_linear p x=0%R]=0%E /\
  @orthogonal_projection_probability R n.+1 0 (leq0n n.+1)
    [set p | euclidean_projection_linear p x=0%R]= 1%E.
Proof.
move=> hx; split; first exact (@nonzero_vector_projection_kernel_probability_null R n m hmn x hx).
have he : [set p : orthogonal_projection_metric_space R n.+1 0 |
    euclidean_projection_linear p x=0%R]=setT.
  apply/seteqP; split=> p // _; exact: coordinate_zero.
by rewrite he theta_star_total.
Qed.

(** Source for [hausdorff_zero_compact_subset_regression]:
    degree-zero endpoint of 2.10.47, p. 204.
    No compactness premise on the original set is needed;
    the retained compact subset has counting mass one. *)
Example hausdorff_zero_compact_subset_regression (R : realType) (X : metricType R) (A : set X) :
  (0<@hausdorff_measure R X 0 A)%E ->
  exists B, [/\ compact B, B `<=` A & @hausdorff_measure R X 0 B = 1%E].
Proof. exact: hausdorff_zero_positive_compact_subset. Qed.

(** Source for [dyadic_grid_zero_dimension_regression]:
    ambient-dimension-zero endpoint of the cube construction
    in 2.10.47, p. 204. Every cube is the
    whole singleton space; there are no coordinate boundaries. *)
Example dyadic_grid_zero_dimension_regression (R : realType) j
    (s : dyadic_cube_indices 0 j) :
  @dyadic_cube_grid R 0 0%R j s=setT.
Proof.
apply/seteqP; split=> x hx //.
apply: (proj2 (@dyadic_cube_grid_specification R 0 0%R j s x))=> i.
by have hh := ltn_ord i; rewrite ltn0 in hh.
Qed.

(** Source for [hausdorff_infinite_compact_subset_regression]:
    infinite-source-mass case of 2.10.47, pp. 204–205.
    The conclusion must provide a finite positive subset;
    merely returning the original compact set is insufficient. *)
Example hausdorff_infinite_compact_subset_regression (R : realType)
    (A : set (inner_metric_space (@euclidean_inner_productP R 2))) :
  compact A -> hausdorff_measure 1 A = +oo%E ->
  exists B, [/\ compact B, B `<=` A, (0<hausdorff_measure 1 B)%E & (hausdorff_measure 1 B < +oo)%E].
Proof.
move=> hA hmass.
have hpos : (0<hausdorff_measure 1 A)%E by rewrite hmass lt0y.
exact (@federer_2_10_47 R 2 1 A hA hpos).
Qed.

(** Source for [hausdorff_positive_hyperplane_subset_regression]:
    positive hyperplane-section case of the induction in
    2.10.47, p. 204. The source lies in a
    coordinate hyperplane and has positive length, so the
    temporary null-section hypothesis cannot hold for it. *)
Example hausdorff_positive_hyperplane_subset_regression (R : realType)
    (A : set (inner_metric_space (@euclidean_inner_productP R 2))) :
  compact A -> (forall x, A x -> x ord0=0%R) -> (0<hausdorff_measure 1 A)%E ->
  exists B, [/\ compact B, B `<=` A, (forall x, B x -> x ord0=0%R),
    (0<hausdorff_measure 1 B)%E & (hausdorff_measure 1 B < +oo)%E].
Proof.
move=> hA hline hpos; have [B [hBc hBA hBp hBf]] := @federer_2_10_47 R 2 1 A hA hpos.
exists B; split=> // x hx; apply: hline; exact: hBA.
Qed.

(** Source for [real_power_zero_coefficient_regression]:
    degree-zero boundary of 2.10.47, p. 204,
    for constant gauge coefficient two. A singleton has
    mass two; unit normalisation is not assumed. *)
Example real_power_zero_coefficient_regression (R : realType) (X : metricType R) (x : X) :
  @metric_real_power_measure R X 2%R 0%R [set x] = 2%E.
Proof.
apply: (@real_power_zero_singleton R X 2%R (@metric_real_power_measure R X 2%R 0%R) x).
- exact: metric_real_power_measure_specification.
- by rewrite ler0n.
Qed.


Local Open Scope ereal_scope.
From Federer Require Import HausdorffFiniteCompactInner FiniteCompactMassUP RealPowerSuslinPositiveCompact ExtendedRealBounds.

(** Source for [hausdorff_suslin_infinite_inner_regression]: infinite-mass
    case of 2.10.48, p. 206. Finite compact masses are unbounded;
    the supremum does not require an infinite-mass compact member. *)
Example hausdorff_suslin_infinite_inner_regression (R : realType) n m
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R S -> hausdorff_measure m S = +oo ->
  extended_real_sup (finite_compact_mass_values (hausdorff_measure m) S) = +oo.
Proof. move=> hS hmass; by rewrite -(@federer_2_10_48 R n m S hS). Qed.

(** Source for [hausdorff_zero_dimensional_suslin_inner_regression]:
    both zero endpoints in 2.10.48, p. 206; no positive
    ambient dimension or positive degree is required. *)
Example hausdorff_zero_dimensional_suslin_inner_regression (R : realType)
    (S : set (inner_metric_space (@euclidean_inner_productP R 0))) :
  is_suslin_set R S -> hausdorff_measure 0 S =
    extended_real_sup (finite_compact_mass_values (hausdorff_measure 0) S).
Proof. exact: federer_2_10_48. Qed.

(** Source for [hausdorff_empty_finite_compact_supremum_regression]:
    empty-set case of 2.10.48, p. 206; the family of finite
    compact masses is nonempty because it includes the empty compact. *)
Example hausdorff_empty_finite_compact_supremum_regression (R : realType) n m :
  @extended_real_sup R (finite_compact_mass_values
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) set0) = 0.
Proof.
have hS := @metric_borel_suslin R (inner_metric_space (@euclidean_inner_productP R n)) set0
  (closed_borel_set closed0).
rewrite -(@federer_2_10_48 R n m set0 hS).
exact: measure_empty (hausdorff_measure_is_measure _ _).
Qed.

From Federer Require Import RealHausdorff.

(** Federer 2.10.2, p. 171: actual positive atom and real-degree
    dimension-drop boundary regressions for the Gamma-normalized measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffMeasureLaws
  HausdorffCountingMeasure EuclideanInnerProduct InnerMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section RealHausdorffBoundary.
Variable R:realType.
Local Notation P0:=(inner_metric_space (@euclidean_inner_productP R 0)).

(** Source for [real_hausdorff_zero_atom_regression]: Federer 2.10.2(1),
    p. 171, H^0 equals counting measure. The actual singleton in ambient
    R^0 has positive unit mass with the actual Gamma normalization. *)
Example real_hausdorff_zero_atom_regression (hp:(0<=0:>R)%R):
  @real_hausdorff_measure R P0 0%R hp [set (0%R:P0)] = 1.
Proof.
rewrite -[0%R]/(0%:R:R) real_hausdorff_measure_natural.
exact:hausdorff_zero_singleton.
Qed.

(** Source for [real_hausdorff_half_atom_null_regression]: Federer
    2.10.2(1), p. 171, real-degree dimension drop. That same positive
    H^0 atom has zero measure in the genuinely fractional degree 1/2.
    No rounded degree or additional singleton-null premise is supplied. *)
Example real_hausdorff_half_atom_null_regression (hq:(0<=1/2:>R)%R):
  @real_hausdorff_measure R P0 (1/2)%R hq [set (0%R:P0)] = 0.
Proof.
have h0:(0<=0:>R)%R:=lexx 0%R.
have hpos:(0<1/2:>R)%R by rewrite divr_gt0 // ltr0n.
apply:(@real_hausdorff_finite_higher_degree_zero R P0 0%R (1/2)%R h0 hq
  [set (0%R:P0)] hpos).
rewrite real_hausdorff_zero_atom_regression; exact:ltry.
Qed.
End RealHausdorffBoundary.
