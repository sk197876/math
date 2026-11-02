(** Closedness of C in Federer (1969), 2.10.32, p. 196. Combine the existing
    Hausdorff closedness of convex compact sets with the proved volume
    superlevel and exterior-cost sublevel theorems. The inner-norm and
    real-norm metric wrappers have identical distance data. Identify their
    sealed distance profiles by the infimum laws, then pull back the closed
    convex-profile class through the actual inner-metric Hausdorff profile
    map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric InnerConvex
  RealNormUP NormMetric ConvexFunctionUP ConvexProfileClosed CompactConvexProfiles RealMetricBackground
  MetricSetDistanceUP MetricSetDistanceBasic HausdorffProfileContinuity CompactSetDistanceProfile CompactHausdorffMetric
  EuclideanInnerProduct EuclideanLebesgueDimensions ExteriorMeasureGauge
  HausdorffVolumeBounds HausdorffExteriorBounds SteinerVolumeCostFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_norm_compact_profile_compatibility]: supporting
    compatibility for the closedness claim in
    2.10.32, p. 196, using the unique
    distance-infimum laws in 2.2.10, p. 66,
    and the profiles of 2.10.21, p. 183.
    Equality is derived from the laws; neither
    sealed profile implementation is unfolded. *)
Lemma inner_norm_compact_profile_compatibility (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hN : is_real_norm (inner_norm hB))
    (C : compact_metric_set (inner_metric_space hB)) x :
  @compact_set_distance_profile R (real_norm_metric_space hN) C x=
    @compact_set_distance_profile R (inner_metric_space hB) C x.
Proof.
have hn := @compact_set_distance_profile_specification R (real_norm_metric_space hN) C.
have ht : @is_metric_set_distance R (inner_metric_space hB) (val C)
    (@compact_set_distance_profile R (real_norm_metric_space hN) C).
  constructor.
  - move=> y a ha.
    exact (@metric_set_distance_lower R (real_norm_metric_space hN) (val C)
      (@compact_set_distance_profile R (real_norm_metric_space hN) C) hn y a ha).
  - move=> y r hbound.
    exact (@metric_set_distance_greatest R (real_norm_metric_space hN) (val C)
      (@compact_set_distance_profile R (real_norm_metric_space hN) C) hn y r hbound).
exact (metric_set_distance_unique ht (compact_set_distance_profile_specification C) x).
Qed.

(** Source for [inner_hausdorff_compact_convex_sets_closed]: supporting
    convexity component of the closedness claim
    in 2.10.32, p. 196, from 2.10.21,
    p. 184. Only metric-wrapper compatibility is
    added to the existing project theorem. *)
Lemma inner_hausdorff_compact_convex_sets_closed (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) :
  closed [set K : compact_hausdorff_space (inner_metric_space hB) | is_inner_convex (val K)].
Proof.
have hN : is_real_norm (inner_norm hB).
  split.
  - split; [exact: inner_norm_nonnegative|exact: inner_normZ|exact: inner_norm_triangle].
  - move=> x hx; apply/eqP; by rewrite -(inner_norm_eq0 hB) hx eqxx.
pose H := compact_hausdorff_space (inner_metric_space hB).
pose P := prod_topology (fun _ : V=>real_line_metric R).
pose Q : H -> P := fun C=>compact_set_distance_profile C.
have hprofile (C : H) : is_inner_convex (val C) <->
    @is_real_convex_function_on R V setT (compact_set_distance_profile C).
  have hc := @compact_convex_distance_profile R V (inner_norm hB) hN C.
  have heq : @compact_set_distance_profile R (real_norm_metric_space hN) C=
      @compact_set_distance_profile R (inner_metric_space hB) C.
    apply: funext=> x; exact: inner_norm_compact_profile_compatibility.
  by rewrite heq in hc.
have he : [set C : H | is_inner_convex (val C)]=Q @^-1` (@convex_real_profiles R V).
  apply/seteqP; split=> C hC; [exact: (hprofile C).1 hC|exact: (hprofile C).2 hC].
rewrite he; apply: preimage_closed; last exact: convex_real_profiles_closed.
move=> C _; exact: hausdorff_profile_continuous.
Qed.

(** Source for [steiner_volume_cost_family_closed]: direct
    Hausdorff closedness assertion for C in
    2.10.32, p. 196. Nonnegative mu includes
    the printed positive threshold; no continuity
    of volume beyond its proved upper semicontinuity
    is assumed. *)
Theorem steiner_volume_cost_family_closed (R : realType) (n : nat) (lambda mu : R) :
  0<=mu -> closed (@steiner_volume_cost_family R n lambda mu).
Proof.
move=> hmu.
change (closed ([set K : compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)) |
  is_inner_convex (val K)] `&`
  ([set K | (lambda%:E<=euclidean_lebesgue_measure n (val K))%E] `&`
   [set K | (exterior_diameter_cost n (val K)<=mu%:E)%E]))).
apply: closedI; first exact: inner_hausdorff_compact_convex_sets_closed.
apply: closedI; first exact: hausdorff_euclidean_volume_superlevel_closed.
exact: hausdorff_exterior_cost_sublevel_closed.
Qed.
