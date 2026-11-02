(** Federer (1969), 2.10.15, p. 178: I_t^m(A) is at least the theta-star
    t-norm of the actual projection multiplicity integral g, divided by
    beta_t(n,m), and equality holds at t=1. Follow the printed nested Borel
    partition argument: their projected-volume sums increase to g, Minkowski
    bounds their norms, and 2.10.8, p. 175, identifies the supremum of their
    costs. At exponent one increasing convergence and countable integral
    additivity give the equality with the iterated multiplicity integral. No
    relevant local erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanMetricSeparability
  EuclideanProjectionMetric OrthogonalProjectionProbability ProjectionBeta
  ProjectionIncidenceMeasure IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricCoverCosts
  ProjectionMultiplicityIntegral ProjectionMultiplicityPartitions NonnegativeExtendedNormLimitBound
  NonnegativeExtendedExponentNorm NonnegativeExtendedExponentNormUP
  NonnegativeExtendedNormOrder ExtendedPositivePower PositiveFiniteSupremumScale
  ExtendedRealOrderTopology ExtendedRealBoundsUP ExtendedRealOrderLimit PartialFunctionBasic
  ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic ClosedCoverTreeSealed CoverPartitionTreeSealed
  TopologicalBorel BorelFamilyBasic BorelClosedProjection BorelPartitionCostLimits
  TotalIncreasingIntegralSupremum MeasureUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  NonnegativeSumSupport NonnegativeSumScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_multiplicity_tree_parameter_integral]:
    direct exponent-one limiting calculation in 2.10.15,
    p. 178, using any of the shrinking partition trees
    specified in 2.10.10, p. 176. The resulting integral
    value is beta_1 times I_1(A), including infinity. *)
Theorem projection_multiplicity_tree_parameter_integral (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_closed_cover_tree E -> is_cover_partition_tree E P -> borel_set A ->
  is_measure_integral (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (projection_multiplicity_integral (m:=m) A))
    ((@projection_beta R n m hmn 1)%:E*@integral_geometric_measure R n m hmn 1 A).
Proof.
move=> hE hP hA.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose b := @projection_beta R n m hmn 1.
pose c := @integral_geometric_gauge R n m hmn 1.
pose k := @projected_incidence_measure R n m hmn.
have hb : (0<b)%R := @projection_beta_positive R n m hmn 1 (lexx _).
have hS s : borel_set (A `&` P s).
  apply: (@borel_family_binary_intersection X setT _ (borel_sets_family X))=> //.
  exact: (@cover_partition_borel R X E P hE hP s).
have hecost j : borel_partition_level_cost k P A j=b%:E*borel_partition_level_cost c P A j.
  rewrite /borel_partition_level_cost -nonnegative_sum_scale; last first.
  - move=> s hs; exact: (@integral_geometric_gauge_nonnegative R n m hmn 1 (lexx _) _ (metric_borel_suslin (hS s))).
  - exact: ltW hb.
  apply: nonnegative_sum_ext=> s hs.
  exact: esym (@integral_geometric_one_gauge_incidence R n m hmn _ (metric_borel_suslin (hS s))).
have hsup0 := @borel_partition_cost_supremum R X c
  (@integral_geometric_gauge_borel_cover_cost R n m hmn 1 (lexx _)) E P hE hP A hA.
have hsup : is_extended_real_supremum [set z | exists j, z=borel_partition_level_cost k P A j]
    (b%:E*@integral_geometric_measure R n m hmn 1 A).
  have he : [set z | exists j, z=borel_partition_level_cost k P A j]=
      [set z | exists j, z=b%:E*borel_partition_level_cost c P A j].
    apply/seteqP; split=> z [j ->]; exists j; [exact: hecost|exact: esym (hecost j)].
  rewrite he; exact: positive_finite_scaled_sequence_supremum hb hsup0.
apply: (@total_increasing_integral_supremum R (orthogonal_projection_metric_space R n m)
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  (fun j => projection_partition_volume_sum (m:=m) P A j)
  (projection_multiplicity_integral (m:=m) A)
  (fun j => borel_partition_level_cost k P A j)
  (b%:E*@integral_geometric_measure R n m hmn 1 A)).
- move=> j p; exact: projection_partition_volume_sum_nonnegative.
- move=> p; exact: projection_partition_volume_sum_increases hE hP hA.
- move=> j; exact: projection_partition_volume_sum_integral hE hP hA.
- exact hsup.
Qed.

(** Source for [projection_multiplicity_tree_norm_bound]: direct
    all-exponent inequality before division by beta_t in the
    proof of 2.10.15, p. 178. Actual integrability from the
    exponent-one calculation supplies measurability of g. *)
Theorem projection_multiplicity_tree_norm_bound (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) (t : \bar R) :
  is_closed_cover_tree E -> is_cover_partition_tree E P -> borel_set A -> 1<=t ->
  nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
    (projection_multiplicity_integral (m:=m) A) t<=
    (@projection_beta R n m hmn t)%:E*@integral_geometric_measure R n m hmn t A.
Proof.
move=> hE hP hA ht.
apply: (@nonnegative_extended_norm_pointwise_limit_bound R
  (orthogonal_projection_metric_space R n m) (@orthogonal_projection_probability R n m hmn)
  (fun j => projection_partition_volume_sum (m:=m) P A j)
  (projection_multiplicity_integral (m:=m) A) t _ (@theta_star_is_measure R n m hmn) ht).
- move=> j p; exact: projection_partition_volume_sum_nonnegative.
- move=> p; exact: projection_multiplicity_integral_nonnegative hA.
- move=> j; exact: (@projection_partition_volume_sum_integral R n m hmn E P A j hE hP hA).1.
- exact: (@projection_multiplicity_tree_parameter_integral R n m hmn E P A hE hP hA).1.
- move=> p; exact: (@projection_partition_volume_sum_increases R n m E P A p hE hP hA).2.
- move=> j; exact: projection_partition_volume_sum_norm_bound hE hP hA ht.
Qed.

(** Source for [federer_2_10_15]: direct theorem of 2.10.15,
    p. 178. For Borel A in R^n and n>=m>=1, the
    actual multiplicity-integral function g satisfies I_t(A)>=
    norm_t(g)/beta_t for every t>=1, with equality at one.
    The middle conclusion exhibits the actual outer integral,
    so the final formula is the printed iterated integral. *)
Theorem federer_2_10_15 (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (0<m)%N -> borel_set A ->
  (forall t : \bar R, 1<=t ->
    ((@projection_beta R n m hmn t)^-1)%:E*
      nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
        (projection_multiplicity_integral (m:=m) A) t<=
      @integral_geometric_measure R n m hmn t A) /\
  is_measure_integral (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (projection_multiplicity_integral (m:=m) A))
    ((@projection_beta R n m hmn 1)%:E*@integral_geometric_measure R n m hmn 1 A) /\
  @integral_geometric_measure R n m hmn 1 A=
    ((@projection_beta R n m hmn 1)^-1)%:E*
      measure_lower_integral (@orthogonal_projection_probability R n m hmn)
        (partial_function_total (projection_multiplicity_integral (m:=m) A)).
Proof.
move=> hmpos hA.
pose X := inner_metric_space (@euclidean_inner_productP R n).
have [D [hD hden]] := euclidean_metric_separable R n.
have hX : (@setT X) !=set0 by exists (0%R : X).
pose E := @ClosedCoverTree.value R X D hD hden hX.
pose P := @CoverPartitionTree.value X E.
have hE := @ClosedCoverTree.laws R X D hD hden hX.
have hP := @CoverPartitionTree.laws X E.
have hi := @projection_multiplicity_tree_parameter_integral R n m hmn E P A hE hP hA.
split; last split; last first.
- have hb := @projection_beta_positive R n m hmn 1 (lexx _).
  have hne : @projection_beta R n m hmn 1!=0%R by rewrite gt_eqF.
  have he := measure_lower_integral_unique (measure_lower_integral_specification _ _) hi.2.2.
  by rewrite he muleA -EFinM mulVf // mul1e.
- exact hi.
- move=> t ht.
  have hb := @projection_beta_positive R n m hmn t ht.
  have hne : @projection_beta R n m hmn t!=0%R by rewrite gt_eqF.
  have hi0 : 0<=((@projection_beta R n m hmn t)^-1)%:E.
    by rewrite lee_fin invr_ge0; exact: ltW hb.
  have hh := lee_wpmul2l hi0
    (@projection_multiplicity_tree_norm_bound R n m hmn E P A t hE hP hA ht).
  by rewrite muleA -EFinM mulVf // mul1e in hh.
Qed.

(** Source for [integral_geometric_multiplicity_one_norm_equality]:
    direct assertion that equality holds at t=1 in 2.10.15,
    p. 178. The actual one-norm of the nonnegative function
    g equals its integral, including infinite values. *)
Corollary integral_geometric_multiplicity_one_norm_equality
    (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (0<m)%N -> borel_set A ->
  @integral_geometric_measure R n m hmn 1 A=
    ((@projection_beta R n m hmn 1)^-1)%:E*
      nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
        (projection_multiplicity_integral (m:=m) A) 1.
Proof.
move=> hmpos hA.
pose theta := @orthogonal_projection_probability R n m hmn.
pose g := projection_multiplicity_integral (m:=m) A.
pose b := (@projection_beta R n m hmn 1)%:E*@integral_geometric_measure R n m hmn 1 A.
have hi := (@federer_2_10_15 R n m hmn A hmpos hA).2.1.
have hg0 p : 0<=g p := projection_multiplicity_integral_nonnegative p hA.
have hb0 : 0<=b := @nonnegative_total_integral_value_ge0 R
  (orthogonal_projection_metric_space R n m) theta (@theta_star_is_measure R n m hmn) g b hg0 hi.
have hN : is_nonnegative_extended_exponent_norm theta g 1 b.
  split; first exact: lexx.
  exists b; split; last by rewrite invr1 extended_positive_power_one.
  have he : (fun p => extended_positive_power (g p) 1%R)=g.
    apply/funext=> p; exact: extended_positive_power_one (hg0 p).
  by rewrite he.
have hn := @nonnegative_extended_exponent_norm_unique R
  (orthogonal_projection_metric_space R n m) theta g 1 _ b
  (@nonnegative_extended_exponent_norm_specification R _ theta g 1
    (@theta_star_is_measure R n m hmn) hg0 (lexx _) hi.1) hN.
have hbeta := @projection_beta_positive R n m hmn 1 (lexx _).
have hne : @projection_beta R n m hmn 1!=0%R by rewrite gt_eqF.
by rewrite hn /b muleA -EFinM mulVf // mul1e.
Qed.
