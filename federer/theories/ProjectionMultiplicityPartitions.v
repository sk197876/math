(** Federer (1969), 2.10.15, p. 178, proof: sum the projected volumes of the
    nested Borel partition cells. These sums increase pointwise to the
    actual multiplicity integral g(p), by 2.10.10, p. 176, and 2.4.7, p. 84.
    Minkowski and the disjoint partition-cost bound give their uniform
    theta-star norm bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric EuclideanLebesgueDimensions ProjectedVolumeMeasurability
  OrthogonalProjectionProbability ProjectionBeta ProjectionIncidenceMeasure
  IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricCoverCosts
  NonnegativeExtendedExponentNorm ProbabilityExtendedNormCover
  ProjectionMultiplicityIntegral TotalIncreasingIntegralValues
  ExtendedRealOrderTopology ExtendedRealOrderLimit PartialFunctionBasic
  ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic ShrinkingBorelPartitionLevels
  PartitionHitCounts PartitionCountingLimit PartitionImageIntegral MappingMultiplicity CountingMeasure
  BorelPartitionCostLimits BorelImageCoverCost TopologicalBorel BorelFamilyBasic BorelClosedProjection
  MeasureUP MeasureBasic MeasureIntegralUP TotalCountableNonnegativeIntegral
  NonnegativeSum NonnegativeSumSupport NonnegativeSumScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_partition_volume_sum]: direct sum
    of f_S(p) over the j-th Borel partition in the first
    display of the proof of 2.10.15, p. 178. *)
Definition projection_partition_volume_sum (R : realType) (n m : nat)
    (P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) j
    (p : orthogonal_projection_metric_space R n m) : extended_real_line R :=
  nonnegative_sum [set s | size s=j]
    (fun s => projected_volume_function (m:=m) (A `&` P s) p).

(** Source for [projection_partition_volume_sum_nonnegative]:
    supporting nonnegative inputs for the norm-limit step of
    2.10.15, p. 178, from numerical summation in 2.1.1,
    pp. 51–53. *)
Lemma projection_partition_volume_sum_nonnegative (R : realType) (n m : nat)
    (P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) j
    (p : orthogonal_projection_metric_space R n m) :
  0<=projection_partition_volume_sum P A j p.
Proof. exact: nonnegative_sum_nonnegative. Qed.

(** Source for [projection_partition_volume_sum_integral]:
    supporting countable integral sum in 2.10.15, p. 178,
    using 2.4.8, p. 84. The previously proved Fubini
    formula for each projected volume gives the actual theta-star
    integral, hence measurability of every partition sum. *)
Lemma projection_partition_volume_sum_integral (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) j :
  is_closed_cover_tree E -> is_cover_partition_tree E P -> borel_set A ->
  is_measure_integral (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (projection_partition_volume_sum (m:=m) P A j))
    (borel_partition_level_cost (@projected_incidence_measure R n m hmn) P A j).
Proof.
move=> hE hP hA.
have hS s : borel_set (A `&` P s).
  apply: (@borel_family_binary_intersection _ setT _ (borel_sets_family _))=> //.
  exact: (@cover_partition_borel R (inner_metric_space (@euclidean_inner_productP R n)) E P hE hP s).
apply: (@total_countable_nonnegative_integral R (orthogonal_projection_metric_space R n m)
  [the choiceType of (seq nat : Type)] (@orthogonal_projection_probability R n m hmn)
  (@theta_star_is_measure R n m hmn) [set s | size s=j]
  (fun s => projected_volume_function (m:=m) (A `&` P s))
  (@projected_incidence_measure R n m hmn \o (fun s => A `&` P s))
  (cover_partition_level_countable j)).
- move=> s hs p; exact: projected_volume_function_nonnegative.
- move=> s hs; apply: projected_volume_incidence_integral; exact: metric_borel_suslin (hS s).
Qed.

(** Source for [projection_partition_volume_sum_increases]:
    direct increasing convergence to g(p) in the first proof
    display of 2.10.15, p. 178. Apply 2.4.7, p. 84,
    to the partition fibre counts of 2.10.10, p. 176,
    with their independently proved actual Lebesgue integrals. *)
Theorem projection_partition_volume_sum_increases (R : realType) (n m : nat)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) :
  is_closed_cover_tree E -> is_cover_partition_tree E P -> borel_set A ->
  extended_increases_to (fun j => projection_partition_volume_sum P A j p)
    (projection_multiplicity_integral A p).
Proof.
move=> hE hP hA.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose beta := @euclidean_lebesgue_measure R m.
have hm := @euclidean_lebesgue_is_measure R m.
pose f := euclidean_projection_linear p.
apply: (@total_increasing_integral_values R Y beta hm
  (fun j y => (@partition_hit_count R X P (mapping_fibre f A y) j : extended_real_line R))
  (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R))
  (fun j => projection_partition_volume_sum P A j p) (projection_multiplicity_integral A p)).
- move=> j y; exact: (@measure_nonnegative R [the choiceType of (seq nat : Type)] _
    (counting_measure_is_measure R _) _).
- move=> y; exact: (@partition_hit_count_limit R X E P hE hP (mapping_fibre f A y)).
- move=> j; apply: (@partition_image_count_integral R X Y f beta hm E P hE hP A j _ hA).
  move=> S hS; exact: euclidean_projection_borel_image_measurable hS.
- exact: projection_multiplicity_integral_specification p hA.
Qed.

(** Source for [projection_partition_volume_sum_norm_bound]:
    direct Minkowski and partition-cost estimate in 2.10.15,
    p. 178. The norm of each partition sum is at most
    beta_t times I_t(A); every exponent including infinity
    and infinite measure values is retained. *)
Theorem projection_partition_volume_sum_norm_bound (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) j (t : \bar R) :
  is_closed_cover_tree E -> is_cover_partition_tree E P -> borel_set A -> 1<=t ->
  nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
    (projection_partition_volume_sum (m:=m) P A j) t<=
    (@projection_beta R n m hmn t)%:E*@integral_geometric_measure R n m hmn t A.
Proof.
move=> hE hP hA ht.
pose theta := @orthogonal_projection_probability R n m hmn.
pose c := @integral_geometric_gauge R n m hmn t.
pose b := @projection_beta R n m hmn t.
have hb : (0<=b)%R := ltW (@projection_beta_positive R n m hmn t ht).
have hbE : 0<=b%:E by rewrite lee_fin.
have hS s : borel_set (A `&` P s).
  apply: (@borel_family_binary_intersection _ setT _ (borel_sets_family _))=> //.
  exact: (@cover_partition_borel R (inner_metric_space (@euclidean_inner_productP R n)) E P hE hP s).
have hmeas := (@projection_partition_volume_sum_integral R n m hmn E P A j hE hP hA).1.
have hnorm := @probability_nonnegative_extended_norm_cover R
  (orthogonal_projection_metric_space R n m) [the choiceType of (seq nat : Type)]
  theta (@theta_star_is_measure R n m hmn) t [set s | size s=j]
  (projection_partition_volume_sum (m:=m) P A j)
  (fun s => projected_volume_function (m:=m) (A `&` P s))
  (@theta_star_total R n m hmn) (cover_partition_level_countable j) ht
  (fun p => projection_partition_volume_sum_nonnegative P A j p)
  (fun s p => projected_volume_function_nonnegative (A `&` P s) p) hmeas
  (fun s hs => @theta_star_projected_volume_measurable R n m hmn _ (metric_borel_suslin (hS s)))
  (fun p => lexx _).
have he : nonnegative_sum [set s | size s=j]
    (fun s => nonnegative_extended_exponent_norm theta
      (projected_volume_function (m:=m) (A `&` P s)) t)=
    b%:E*borel_partition_level_cost c P A j.
  rewrite /borel_partition_level_cost -nonnegative_sum_scale //.
  2: move=> s hs; exact: (@integral_geometric_gauge_nonnegative R n m hmn t ht _ (metric_borel_suslin (hS s))).
  apply: nonnegative_sum_ext=> s hs; exact: esym (@integral_geometric_gauge_normalized R n m hmn t ht (A `&` P s)).
rewrite he in hnorm.
have hcost := @borel_partition_level_cost_upper R (inner_metric_space (@euclidean_inner_productP R n))
  c (@integral_geometric_gauge_borel_cover_cost R n m hmn t ht) E P hE hP A j hA.
exact: le_trans hnorm (lee_wpmul2l hbE hcost).
Qed.
