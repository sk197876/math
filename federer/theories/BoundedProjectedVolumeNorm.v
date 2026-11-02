(** Federer (1969), 2.10.5, p. 172, last paragraph, paraphrased: for bounded
    Suslin S, beta_t zeta_t(S) is nondecreasing and continuous in t. First
    prove exact agreement with the scalar norms of 2.4.17, p. 90, after
    proving finite projected volumes. Then apply the probability comparison
    and continuity theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanProjectionMetric ProjectedVolumeMeasurability ProjectedVolumeBounds
  OrthogonalProjectionProbability SuslinSetUP PartialFunctionBasic MeasurableFunctionUP
  NonnegativeExtendedExponentNorm NonnegativeExtendedScalarNorm MeasureExponentDomain
  ProbabilityExponentMonotone BoundedProbabilityExponentNorm ProjectionBeta IntegralGeometricGauge
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projected_volume_scalar]: supporting
    scalar representative for the bounded-set paragraph
    of Federer 2.10.5, p. 172. Agreement with
    actual volumes is used only under the proved
    boundedness and finiteness hypotheses below. *)
Definition projected_volume_scalar (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) :
    real_norm_metric_space (scalar_absolute_value_norm R) := fine (projected_volume_function S p).

(** Source for [projected_volume_scalar_measurable]:
    supporting measurable representative for applying
    2.4.17 in Federer 2.10.5, p. 172.
    This measurability assertion alone makes no
    claim of equality at infinite input values. *)
Lemma projected_volume_scalar_measurable (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R S -> is_measure_measurable_function
    (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (projected_volume_scalar (m:=m) S)).
Proof.
move=> hS; exact: (@measurable_extended_finite_scalar R _
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  (projected_volume_function (m:=m) S) (@theta_star_projected_volume_measurable R n m hmn S hS)).
Qed.

(** Source for [bounded_projected_volume_norm_scalar]:
    supporting exact reduction to the scalar norm
    before the appeal to 2.4.17 in Federer
    2.10.5, p. 172. The explicit source norm
    bound ensures every projected volume is finite. *)
Theorem bounded_projected_volume_norm_scalar (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R)
    (t : \bar R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  is_suslin_set R S -> 1<=t ->
  nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
      (projected_volume_function (m:=m) S) t =
    measure_exponent_norm (@orthogonal_projection_probability R n m hmn)
      (partial_function_total (projected_volume_scalar (m:=m) S)) t.
Proof.
move=> hb hS ht; exact: (@nonnegative_extended_norm_finite_scalar R _
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  (projected_volume_function (m:=m) S) t
  (fun p => projected_volume_function_nonnegative S p)
  (@projected_volume_function_finite R n m S c hb) ht
  (@theta_star_projected_volume_measurable R n m hmn S hS)).
Qed.

(** Source for [projected_volume_scalar_uniform_bound]:
    supporting bounded scalar representative in
    Federer 2.10.5, p. 172. The bound is
    positive even when S is empty or has volume zero. *)
Lemma projected_volume_scalar_uniform_bound (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  exists B : R, (0<B)%R /\ forall p : orthogonal_projection_metric_space R n m,
    (`|projected_volume_scalar S p|<=B)%R.
Proof.
move=> hS; have [b [hb0 hb]] := @projected_volume_function_bounded R n m S c hS.
have hBB : (b<b+1)%R by rewrite ltrDl.
exists (b+1)%R; split; first exact: le_lt_trans hb0 hBB.
move=> p.
have hf := @projected_volume_function_finite R n m S c hS p.
have hp0 : (0<=fine (projected_volume_function S p))%R.
  have h := projected_volume_function_nonnegative S p.
  by rewrite -(fineK hf) lee_fin in h.
have hp : (fine (projected_volume_function S p)<=b)%R.
  have h := hb p; by rewrite -(fineK hf) lee_fin in h.
rewrite /projected_volume_scalar (ger0_norm hp0).
exact: le_trans hp (ltW hBB).
Qed.

(** Source for [bounded_projected_volume_norm_finite]:
    supporting finite numerator at every exponent
    for bounded Suslin S in Federer 2.10.5,
    p. 172. This supplies the hypotheses for
    the subsequent quotient-continuity argument. *)
Lemma bounded_projected_volume_norm_finite (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R)
    (t : \bar R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  is_suslin_set R S -> 1<=t ->
  nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
    (projected_volume_function (m:=m) S) t < +oo.
Proof.
move=> hb hS ht; have [B [hB hgB]] := @projected_volume_scalar_uniform_bound R n m S c hb.
rewrite (@bounded_projected_volume_norm_scalar R n m hmn S c t hb hS ht).
exact: (@bounded_probability_exponent_norm_finite R _
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  (projected_volume_scalar (m:=m) S) B t (@theta_star_total R n m hmn) hB hgB ht
  (@projected_volume_scalar_measurable R n m hmn S hS)).
Qed.

(** Source for [bounded_projected_volume_norm_monotone]:
    direct nondecreasing-numerator assertion for
    bounded Suslin S in Federer 2.10.5, p. 172.
    Infinity and equal exponents are included. *)
Theorem bounded_projected_volume_norm_monotone (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R)
    (s t : \bar R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  is_suslin_set R S -> 1<=s -> s<=t ->
  nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
    (projected_volume_function (m:=m) S) s <=
  nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
    (projected_volume_function (m:=m) S) t.
Proof.
move=> hb hS hs hst; have ht := le_trans hs hst.
rewrite (@bounded_projected_volume_norm_scalar R n m hmn S c s hb hS hs)
  (@bounded_projected_volume_norm_scalar R n m hmn S c t hb hS ht).
exact: (@probability_measure_exponent_norm_monotone R _
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  (partial_function_total (projected_volume_scalar (m:=m) S)) s t
  (@theta_star_total R n m hmn) hs hst (@projected_volume_scalar_measurable R n m hmn S hS)).
Qed.

(** Source for [bounded_projected_volume_norm_continuous]:
    direct numerator continuity for bounded Suslin
    S in Federer 2.10.5, p. 172. The full
    extended exponent interval includes infinity. *)
Theorem bounded_projected_volume_norm_continuous (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R) :
  (forall x, S x -> (inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  is_suslin_set R S ->
  continuous (fun t : subspace [set t : extended_real_line R | 1<=t] =>
    (nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
      (projected_volume_function (m:=m) S) t : extended_real_line R)).
Proof.
move=> hb hS; have [B [hB hgB]] := @projected_volume_scalar_uniform_bound R n m S c hb.
have hh := @bounded_probability_exponent_norm_continuous R _
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  (projected_volume_scalar (m:=m) S) B (@theta_star_total R n m hmn) hB hgB
  (@projected_volume_scalar_measurable R n m hmn S hS).
apply: subspace_eq_continuous _ hh=> t ht.
have ht' : 1<=t by move: ht; rewrite inE.
exact: esym (@bounded_projected_volume_norm_scalar R n m hmn S c t hb hS ht').
Qed.
