(** Supporting normalization continuity for Federer (1969), 2.10.5, p. 172,
    bounded-set paragraph. Apply the defining projection-norm identity of
    2.7.16(6), pp. 139–140, to a simple unit m-vector. Its projection-norm
    function is bounded by one, so 2.4.17, p. 90, proves continuity of beta,
    including the infinity endpoint. No relevant local erratum entry occurs. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates InnerMetric
  EuclideanProjectionMetric ExteriorDiameterUP ExteriorGrading FiniteExteriorPowers
  ExteriorNorm AssociatedSubspace SimpleElementary OrthonormalFamilies CoordinateProjection
  RealNormUP NormMetric RealMetricBackground NormPowerScalar
  OrthogonalProjectionConstants ProjectionConstantNorms ProjectionBeta
  OrthogonalProjectionProbabilityUP OrthogonalProjectionProbability
  OrthogonalGroupTopology OrthogonalInjectionSpaces EuclideanOrthogonalInvariantMeasures
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages MeasureUP MeasureAlmostBasic
  MeasurableFunctionUP BorelRegularMeasureUP BorelFunctionBasic
  MeasureLpNormUP MeasureLpNorm MeasureEssentialNormUP MeasureEssentialNorm MeasureExponentDomain
  ExtendedRealOrderTopology ExtendedFiniteProjectionBorel BoundedProbabilityExponentNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_simple_unit_vector_exists]:
    supporting simple unit m-vector for the beta
    identity in Federer 2.7.16(6), p. 140,
    used for continuity in 2.10.5, p. 172.
    An orthonormal coordinate product has norm one
    by 1.7.5, p. 32; m<=n permits its choice. *)
Lemma euclidean_simple_unit_vector_exists (R : realType) (n m : nat) :
  (m<=n)%N -> exists xi : exterior_power (R_n R n) m,
    simple xi /\ exterior_norm (real_exterior_two_nonzero R) (@euclidean_inner_productP R n) xi = 1%R.
Proof.
move=> hmn.
pose e (i : 'I_m) : R_n R n := @coordinate_basis R n (widen_ord hmn i).
have hw i j : (widen_ord hmn i==widen_ord hmn j)=(i==j).
  by apply/eqP/eqP=> [h|->] //; apply: val_inj; exact: (congr1 val h).
have he : orthonormal_family (@euclidean_inner_product R n) e.
  move=> i j; rewrite /e euclidean_inner_basis /coordinate_basis ffunE.
  by rewrite hw eq_sym.
exists (e_lambda e (ord_tuple m)); split; first exact: product_simple.
exact: (@orthonormal_product_unit_norm R (real_exterior_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m e he).
Qed.

(** Source for [simple_projection_norm_scalar_measurable]:
    supporting measurable scalar test for the beta
    identity used in Federer 2.10.5, p. 172.
    Its continuity is already proved from 2.7.16(6),
    p. 139, for simple exterior vectors. *)
Lemma simple_projection_norm_scalar_measurable (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (xi : exterior_power (R_n R n) m) :
  simple xi -> is_measure_measurable_function (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (fun p : orthogonal_projection_metric_space R n m =>
      (projection_norm (real_exterior_two_nonzero R) xi p :
        real_norm_metric_space (scalar_absolute_value_norm R)))).
Proof.
move=> hs.
pose P := orthogonal_projection_metric_space R n m.
pose g (p : P) : real_norm_metric_space (scalar_absolute_value_norm R) :=
  projection_norm (real_exterior_two_nonzero R) xi p.
have hc : continuous g.
  move=> p; exact: continuous_comp
    (@projection_norm_continuous R (real_exterior_two_nonzero R) n m xi hs p)
    (@real_scalar_norm_identity_continuous R (g p)).
constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true (@theta_star_is_measure R n m hmn).
- move=> U hU; rewrite partial_function_total_preimage.
  apply: (@borel_regular_borel_measurable R P
    (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
    (@theta_star_borel_regular R n m hmn)).
  exact: (@continuous_borel_function P
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] g hc U hU).
Qed.

(** Source for [projection_beta_scalar_norm_value]:
    supporting specialization of the norm identity
    in Federer 2.7.16(6), p. 140, to a
    simple unit vector. It identifies the actual
    beta with a scalar exponent norm for use in
    2.10.5, p. 172, including t=infinity. *)
Lemma projection_beta_scalar_norm_value (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (xi : exterior_power (R_n R n) m) (t : \bar R) :
  simple xi -> exterior_norm (real_exterior_two_nonzero R) (@euclidean_inner_productP R n) xi = 1%R ->
  1<=t ->
  measure_exponent_norm (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (fun p : orthogonal_projection_metric_space R n m =>
      (projection_norm (real_exterior_two_nonzero R) xi p :
        real_norm_metric_space (scalar_absolute_value_norm R)))) t =
    (@projection_beta R n m hmn t)%:E.
Proof.
move=> hs hunit ht.
have [mulS [invS [eS hS]]] := orthogonal_group_restriction_exists
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have htheta := @orthogonal_projection_probability_specification R n m hmn mulS invS eS hS.
have hb := @projection_beta_specification R n m hmn t ht.
have hn := @projection_norm_seminorm R (real_exterior_two_nonzero R) n m
  mulS invS eS hS t (@projection_beta R n m hmn t)
  (@orthogonal_projection_probability R n m hmn) xi ht hb htheta hs.
rewrite hunit mulr1 in hn.
clear hb; case: t ht hn=> [p| |] ht hn //=.
- have hp : (1<=p)%R := ht.
  exact: measure_lp_norm_unique
    (@measure_lp_norm_specification R _ R^o (fun y : R => `|y|%R)
      (scalar_absolute_value_norm R) (@orthogonal_projection_probability R n m hmn) p _
      (@theta_star_is_measure R n m hmn) hp
      (@simple_projection_norm_scalar_measurable R n m hmn xi hs)) hn.
- have [ha hl] := measure_essential_norm_specification
    (@orthogonal_projection_probability R n m hmn) (fun y : R => `|y|%R)
    (partial_function_total (projection_norm (real_exterior_two_nonzero R) xi)).
  apply/eqP; rewrite eq_le; apply/andP; split.
  - exact: hn.2 _ ha.
  - exact: hl _ hn.1.
Qed.

(** Source for [projection_beta_extended_continuous]:
    supporting continuity of beta_t as an extended
    real function in the bounded-set paragraph of
    Federer 2.10.5, p. 172. A simple unit
    vector identifies it with the bounded probability
    norm family of 2.4.17, p. 90. *)
Theorem projection_beta_extended_continuous (R : realType) (n m : nat)
    (hmn : (m<=n)%N) :
  continuous (fun t : subspace [set t : extended_real_line R | 1<=t] =>
    ((@projection_beta R n m hmn t)%:E : extended_real_line R)).
Proof.
have [xi [hs hunit]] := @euclidean_simple_unit_vector_exists R n m hmn.
pose g (p : orthogonal_projection_metric_space R n m) :
    real_norm_metric_space (scalar_absolute_value_norm R) :=
  projection_norm (real_exterior_two_nonzero R) xi p.
have hbound p : (`|g p|<=1)%R.
  rewrite /g (ger0_norm (projection_norm_nonnegative (real_exterior_two_nonzero R) xi p)).
  by rewrite -hunit; exact: projection_norm_bound.
have hh := @bounded_probability_exponent_norm_continuous R _
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  g 1%R (@theta_star_total R n m hmn) ltr01 hbound
  (@simple_projection_norm_scalar_measurable R n m hmn xi hs).
apply: subspace_eq_continuous _ hh=> t ht.
have ht' : 1<=t by move: ht; rewrite inE.
exact: (@projection_beta_scalar_norm_value R n m hmn xi t hs hunit ht').
Qed.

(** Source for [projection_beta_real_continuous]:
    supporting finite-scalar continuity of the
    positive normalizing divisor in Federer 2.10.5,
    p. 172. The finite-part map is continuous
    at each beta because every beta is a real number. *)
Theorem projection_beta_real_continuous (R : realType) (n m : nat)
    (hmn : (m<=n)%N) :
  continuous (fun t : subspace [set t : extended_real_line R | 1<=t] =>
    (@projection_beta R n m hmn t : real_line_metric R)).
Proof.
move=> t.
have hfinite : (@projection_beta R n m hmn t)%:E \is a fin_num by rewrite fin_numE.
exact: continuous_comp (@projection_beta_extended_continuous R n m hmn t)
  (@extended_finite_projection_continuous_at_real R
    (@projection_beta R n m hmn t)%:E hfinite).
Qed.
