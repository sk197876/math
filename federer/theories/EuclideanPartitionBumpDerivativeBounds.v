(** Federer (1969), 3.1.13, p. 225:
    every selected bump satisfies the common pointwise
    bound G_i h(x)^(-i). Bumps outside S_x
    vanish on a whole neighbourhood of x. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RealNormUP ContinuousMultilinearUP ContinuousMultilinearNorm
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialSupport
  InnerSmoothUnitBump UniformFunctionNormUP FedererCoverRadius LipschitzRadiusOverlap
  EuclideanPartitionBallCoverUP EuclideanPartitionBumps EuclideanPartitionFamilyUP
  EuclideanPartitionOverlapNeighborhood EuclideanPartitionDenominatorBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_partition_bump_derivative_bound]:
    ||D^i u_s(x)||<=G_i h(x)^(-i)
    for every selected s and x in U,
    Federer 3.1.13, p. 225.
    Outside the overlap family S_x the
    actual differential is zero, not merely small. *)
Theorem euclidean_partition_bump_derivative_bound (R : realType) m
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m))
      (fun t : R^o=>`|t|) (@ev i) (@ZN i))
    (Phi : set (set (inner_metric_space (@euclidean_inner_productP R m))))
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    k (Dmu : R_n R m->Z k) G :
  (forall T, Phi T -> open T) ->
  is_federer_partition_ball_cover Phi S ->
  (forall x, has_norm_higher_differential
    (inner_norm (@euclidean_inner_productP R m)) ev ZN
    (fun _=>True) (inner_smooth_unit_bump (@euclidean_inner_productP R m)) k x (Dmu x)) ->
  is_uniform_function_norm (fun x=>@ZN k (Dmu x)) G ->
  forall s x (z : Z k), S s -> (\bigcup_(T in Phi) T) x ->
    has_norm_higher_differential (inner_norm (@euclidean_inner_productP R m))
      ev ZN (fun _=>True) (euclidean_partition_bump Phi s) k x z ->
    @ZN k z<=G/(federer_cover_radius Phi x)^+k.
Proof.
move=>ho hS hDmu hG s x z hs hx hz.
pose N := inner_norm (@euclidean_inner_productP R m).
pose hN := inner_norm_real_norm (@euclidean_inner_productP R m).
pose h := federer_cover_radius Phi.
case:(pselect (lipschitz_radius_overlap S h 10 10 x s))=>[hin|hout].
- have hd := @partition_scaled_derivative_value_correct R m Z ev ZN hZ
    Phi S k Dmu hDmu s x hs.
  have he := norm_higher_differential_unique hN (@scalar_absolute_value_norm R) hZ hz hd.
  rewrite he.
  exact: (@partition_scaled_derivative_overlap_bound R m Z ev ZN hZ
    Phi S ho hS k Dmu G hG x s hx hin).
- have [hOx [hOU [hOo hmeet]]] := partition_overlap_neighborhood_laws S ho hx.
  have hzero y (hy : partition_overlap_neighborhood Phi x y) :
      euclidean_partition_bump Phi s y=0.
    apply: (euclidean_partition_bump_zero_off_ball ho hS hs)=>hsy.
    exact: (hout (hmeet s y hs hy hsy)).
  have hd := @norm_higher_differential_locally_zero R (R_n R m) R^o N
    (fun t : R^o=>`|t|) hN (@scalar_absolute_value_norm R) Z ev ZN hZ
    (partition_overlap_neighborhood Phi x) (euclidean_partition_bump Phi s) k x
    hOo hzero hOx.
  have he := norm_higher_differential_unique hN (@scalar_absolute_value_norm R) hZ hz hd.
  have hNk := continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R) (@hZ k).
  rewrite he (real_seminorm_zero hNk.1).
  apply: (divr_ge0 (uniform_function_norm_nonnegative hG)).
  apply: exprn_ge0; exact: federer_cover_radius_nonnegative.
Qed.
