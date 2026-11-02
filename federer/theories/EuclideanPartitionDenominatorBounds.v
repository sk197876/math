(** Federer (1969), 3.1.13, p. 225:
    the denominator has the printed derivative bound
    129^m G_i h(x)^(-i). The exact local
    overlap family is used before differentiation. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals topology lra.
From Federer Require Import RealNormUP Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness ContinuousMultilinearUP ContinuousMultilinearNorm
  NormHigherDifferentialUP NormScaledUnitBump InnerSmoothUnitBump UniformFunctionNormUP
  FedererCoverRadius LipschitzRadiusOverlap EuclideanPartitionBallCoverUP
  EuclideanPartitionOverlapNeighborhood EuclideanPartitionBumps
  EuclideanPartitionFamilyUP NormLocalFiniteSumDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DenominatorBounds.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) R^o.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N
  (fun t : R^o=>`|t|) (@ev i) (@ZN i).
Variables (Phi : set (set X)) (S : set X).
Hypothesis ho : forall T, Phi T -> open T.
Hypothesis hS : is_federer_partition_ball_cover Phi S.
Variables (sigma : X->R) (v : X->X->R).
Hypothesis hfamily : is_euclidean_partition_family ev ZN Phi S sigma v.
Local Notation U := (\bigcup_(T in Phi) T).
Local Notation h := (federer_cover_radius Phi).
Variable k : nat.
Variable Dmu : X->Z k.
Variable G : R.
Hypothesis hDmu : forall x, has_norm_higher_differential N ev ZN
  (fun _=>True) (inner_smooth_unit_bump (@euclidean_inner_productP R m)) k x (Dmu x).
Hypothesis hG : is_uniform_function_norm (fun x=>@ZN k (Dmu x)) G.

(** Source for [partition_scaled_derivative_value]:
    the differential of u_s in the
    local sum for sigma, Federer 3.1.13,
    pp. 224–225. *)
Definition partition_scaled_derivative_value s x : Z k :=
  ((5*h s)^-1)^+k*:Dmu ((5*h s)^-1*:(x-s)).

(** Source for [partition_scaled_derivative_value_correct]:
    the displayed scaled differential is the
    actual differential on all of R^m,
    Federer 3.1.13, pp. 224–225. *)
Lemma partition_scaled_derivative_value_correct s x :
  S s -> has_norm_higher_differential N ev ZN (fun _=>True)
    (euclidean_partition_bump Phi s) k x (partition_scaled_derivative_value s x).
Proof.
move=>hs; exact: (norm_scaled_unit_bump_differential hN s (5*h s) hZ hDmu).
Qed.

(** Source for [partition_scaled_derivative_overlap_bound]:
    for s in S_x, the radius
    comparison yields ||D^i u_s(x)||<=G_i h(x)^(-i),
    Federer 3.1.13, p. 225. *)
Lemma partition_scaled_derivative_overlap_bound x s :
  U x -> lipschitz_radius_overlap S h 10 10 x s ->
  @ZN k (partition_scaled_derivative_value s x)<=G/(h x)^+k.
Proof.
move=>hx hs.
have hp : 0<h x.
  apply: (federer_cover_radius_positive ho); have [T hT hxT] := hx; by exists T.
have hr := euclidean_partition_bump_radius_positive ho hS hs.1.
have hps : 0<h s.
  apply: (federer_cover_radius_positive ho).
  have [T hT hsT] := partition_ball_centers_in_domain hS hs.1; by exists T.
have hratio := (andP (partition_ball_radius_ratios hS hx hs)).2.
rewrite ler_pdivrMr // in hratio.
have hrad : h x<=5*h s by nra.
have hpow : (h x)^+k<=(5*h s)^+k.
  exact: (lerXn2r k (ltW hp) (ltW hr) hrad).
have hG0 := uniform_function_norm_nonnegative hG.
have hbound y : @ZN k (Dmu y)<=G.
  have hh := uniform_function_norm_bound hG y.
  have hNk := continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R) (@hZ k).
  by rewrite (ger0_norm (real_seminorm_nonnegative hNk.1 (Dmu y))) in hh.
apply: (le_trans (norm_scaled_unit_bump_differential_bound s hr hZ hbound x)).
rewrite ler_pdivlMr ?exprn_gt0 // mulrAC ler_pdivrMr ?exprn_gt0 //.
exact: (ler_wpM2l hG0 hpow).
Qed.

(** Source for [euclidean_partition_denominator_derivative_bound]:
    the exact bound ||D^i sigma(x)||<=129^m G_i h(x)^(-i),
    Federer 3.1.13, p. 225.
    It applies to any actual differential
    value of the abstract denominator. *)
Theorem euclidean_partition_denominator_derivative_bound x (z : Z k) :
  U x -> has_norm_higher_differential N ev ZN U sigma k x z ->
  @ZN k z<=129^+m*G/(h x)^+k.
Proof.
move=>hx hz.
have [hOx [hOU [hOo hmeet]]] := partition_overlap_neighborhood_laws S ho hx.
pose K := lipschitz_radius_overlap S h 10 10 x.
have hK : finite_set K := partition_ball_overlap_finite hS hx.
pose F := fset_set K.
have hFI s : s \in F -> S s.
  rewrite /F in_fset_set //; by move/set_mem=>[hs _].
have hzero y (hy : partition_overlap_neighborhood Phi x y) s
    (hs : S s) (hn : s \notin F) : euclidean_partition_bump Phi s y=0.
  apply: (euclidean_partition_bump_zero_off_ball ho hS hs)=>hsy.
  have hin : s \in F.
    rewrite /F in_fset_set //; apply/mem_set; exact: (hmeet s y hs hy hsy).
  by move:hn; rewrite hin.
have hb s (hs : s \in F) :
    @ZN k (partition_scaled_derivative_value s x)<=G/(h x)^+k.
  apply: (partition_scaled_derivative_overlap_bound hx).
  by move:hs; rewrite /F in_fset_set // => /set_mem.
have hl := @norm_local_finite_sum_differential_bound R (R_n R m) R^o X
  N (fun t : R^o=>`|t|) hN (@scalar_absolute_value_norm R) Z ev ZN hZ
  U (partition_overlap_neighborhood Phi x) S
  (euclidean_partition_bump Phi) sigma F k partition_scaled_derivative_value
  (partition_family_denominator_sum hfamily) hFI hOU hOo hzero
  (fun s hs y=>partition_scaled_derivative_value_correct y hs) x z
  (G/(h x)^+k) hOx hz hb.
apply: (le_trans hl).
have hp : 0<h x.
  apply: (federer_cover_radius_positive ho); have [T hT hxT] := hx; by exists T.
have hM : 0<=G/(h x)^+k.
  exact: (divr_ge0 (uniform_function_norm_nonnegative hG) (exprn_ge0 k (ltW hp))).
have hh := ler_wpM2r hM (partition_ball_overlap_bound hS hx).
rewrite !mulrA in hh; by rewrite mulrA.
Qed.
End DenominatorBounds.
