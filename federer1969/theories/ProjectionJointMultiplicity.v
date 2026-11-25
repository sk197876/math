(** Federer (1969), 2.10.16, p. 178, first sentence: N(p restricted to A,y)
    is L^m times theta-star measurable jointly in (y,p). Follow 2.10.10, p.
    176, using the same shrinking Borel partitions as 2.10.15: partition hit
    counts are countable sums of characteristic functions of the joint
    incidence sets from 2.10.5, p. 172. Their increasing limit is the actual
    counting multiplicity. No relevant local erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric EuclideanMetricSeparability EuclideanLebesgueDimensions
  OrthogonalProjectionProbability ProjectedVolumeIncidence ProjectedVolumeMeasurability
  ProjectionIncidenceMeasure ExtendedRealOrderTopology ExtendedRealOrderLimit
  ExtendedIncreasingLimitSupremum PartialFunctionBasic TotalExtendedLowerLimit
  MeasureUP MeasureBasic MeasureIntegralUP MeasurableFunctionUP ProductMeasure
  TopologicalBorel BorelFamilyBasic BorelClosedProjection
  ClosedCoverTreeUP CoverPartitionTreeUP CoverPartitionTreeBasic
  ClosedCoverTreeSealed CoverPartitionTreeSealed ShrinkingBorelPartitionLevels
  PartitionHitCounts PartitionCountingLimit PartitionImageCharacteristicSum MappingMultiplicity
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureExtendedCharacteristicIntegral
  NonnegativeSum NonnegativeSumSupport TotalCountableNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_product_measure]: direct product
    L^m times theta-star in the first sentence of 2.10.16,
    p. 178, composed from the existing abstract product measure. *)
Definition projection_product_measure (R : realType) (n m : nat) (hmn : (m<=n)%N) :=
  product_measure (@euclidean_lebesgue_is_measure R m) (@theta_star_is_measure R n m hmn).

(** Source for [projection_product_measure_is_measure]: supporting
    measure laws for the product in 2.10.16, p. 178,
    from the product theorem 2.6.1, p. 115. *)
Lemma projection_product_measure_is_measure (R : realType) (n m : nat) (hmn : (m<=n)%N) :
  is_measure (@projection_product_measure R n m hmn).
Proof. exact: product_measure_is_measure. Qed.

(** Source for [projection_joint_multiplicity]: direct joint
    counting function N(p restricted to A,y) in 2.10.16,
    p. 178. The pair is ordered (y,p), as in the printed product. *)
Definition projection_joint_multiplicity (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (z : inner_metric_space (@euclidean_inner_productP R m)*orthogonal_projection_metric_space R n m) : extended_real_line R :=
  @mapping_multiplicity R
    [the choiceType of (inner_metric_space (@euclidean_inner_productP R n) : Type)]
    [the choiceType of (inner_metric_space (@euclidean_inner_productP R m) : Type)]
    (euclidean_projection_linear z.2) A z.1.

(** Source for [projection_joint_partition_count]: supporting
    joint partition count in 2.10.16, p. 178, from the
    fibre-count approximation of 2.10.10, p. 176. *)
Definition projection_joint_partition_count (R : realType) (n m : nat)
    (P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) j
    (z : inner_metric_space (@euclidean_inner_productP R m)*orthogonal_projection_metric_space R n m) : extended_real_line R :=
  @partition_hit_count R (inner_metric_space (@euclidean_inner_productP R n)) P
    (mapping_fibre (euclidean_projection_linear z.2) A z.1) j.

(** Source for [projection_joint_partition_characteristic_sum]:
    supporting joint version of the characteristic sum in 2.10.10,
    p. 176, for measurability in 2.10.16, p. 178.
    A fibre meets a cell exactly when (y,p) lies in its
    projection incidence set. No measurability is needed for this identity. *)
Lemma projection_joint_partition_characteristic_sum (R : realType) (n m : nat)
    (P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) j
    (z : inner_metric_space (@euclidean_inner_productP R m)*orthogonal_projection_metric_space R n m) :
  nonnegative_sum [set s | size s=j]
    (fun s => (@CharacteristicFunction.value R _ (projection_incidence (m:=m) (A `&` P s)) z)%:E)=
    projection_joint_partition_count P A j z.
Proof.
case: z=> y p.
have he : nonnegative_sum [set s | size s=j]
    (fun s => (@CharacteristicFunction.value R _ (projection_incidence (m:=m) (A `&` P s)) (y,p))%:E)=
    nonnegative_sum [set s | size s=j]
      (fun s => (@CharacteristicFunction.value R _ (euclidean_projection_linear p @` (A `&` P s)) y)%:E).
  apply: nonnegative_sum_ext=> s hs.
  have hC := @CharacteristicFunction.laws R _ (projection_incidence (m:=m) (A `&` P s)).
  have hI := @CharacteristicFunction.laws R _ (euclidean_projection_linear p @` (A `&` P s)).
  case: (pselect (projection_incidence (m:=m) (A `&` P s) (y,p)))=> hinc.
  - have him : (euclidean_projection_linear p @` (A `&` P s)) y.
      have [x [hx hxy]] := hinc; exists x=> //; exact: esym hxy.
    by rewrite (characteristic_on_set hC hinc) (characteristic_on_set hI him).
  - have him : ~(euclidean_projection_linear p @` (A `&` P s)) y.
      move=> [x hx hxy]; apply: hinc; exists x; split=> //; exact: esym hxy.
    by rewrite (characteristic_off_set hC hinc) (characteristic_off_set hI him).
rewrite he; exact: partition_image_characteristic_sum.
Qed.

(** Source for [projection_joint_partition_count_integral]: supporting
    measurability of every joint count approximation in 2.10.16,
    p. 178. Countable characteristic integration gives its actual
    product integral as the sum of incidence measures of the cells. *)
Lemma projection_joint_partition_count_integral (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) j :
  is_closed_cover_tree E -> is_cover_partition_tree E P -> borel_set A ->
  is_measure_integral (@projection_product_measure R n m hmn)
    (partial_function_total (projection_joint_partition_count (m:=m) P A j))
    (nonnegative_sum [set s | size s=j]
      (fun s => @projected_incidence_measure R n m hmn (A `&` P s))).
Proof.
move=> hE hP hA.
pose Z := (inner_metric_space (@euclidean_inner_productP R m)*orthogonal_projection_metric_space R n m)%type.
pose mu := @projection_product_measure R n m hmn.
pose chi s := @CharacteristicFunction.value R Z (projection_incidence (m:=m) (A `&` P s)).
have hchi s := @CharacteristicFunction.laws R Z (projection_incidence (m:=m) (A `&` P s)).
have hS s : borel_set (A `&` P s).
  apply: (@borel_family_binary_intersection _ setT _ (borel_sets_family _))=> //.
  exact: (@cover_partition_borel R (inner_metric_space (@euclidean_inner_productP R n)) E P hE hP s).
have hinc s : measure_measurable mu (projection_incidence (m:=m) (A `&` P s)).
  exact: (@projection_incidence_product_measurable R n m _ (@theta_star_is_measure R n m hmn)
    _ (@theta_star_borel_regular R n m hmn) (metric_borel_suslin (hS s))).
have hi := @total_countable_nonnegative_integral R [the choiceType of Z]
  [the choiceType of (seq nat : Type)] mu (@projection_product_measure_is_measure R n m hmn)
  [set s | size s=j] (fun s z => ((chi s z)%:E : extended_real_line R))
  (fun s => @projected_incidence_measure R n m hmn (A `&` P s))
  (cover_partition_level_countable j)
  (fun s hs z => characteristic_extended_nonnegative (hchi s) z)
  (fun s hs => @measure_total_characteristic_integral R [the choiceType of Z] mu
    (@projection_product_measure_is_measure R n m hmn) _ (chi s) (hchi s) (hinc s)).
have he : (fun z => nonnegative_sum [set s | size s=j] (fun s => (chi s z)%:E))=
    projection_joint_partition_count (m:=m) P A j.
  apply/funext=> z; exact: projection_joint_partition_characteristic_sum.
by rewrite he in hi.
Qed.

(** Source for [projection_joint_multiplicity_tree_measurable]: direct
    joint-measurability calculation of 2.10.16, p. 178, for
    an abstract shrinking Borel partition tree. Both finite and
    infinite fibre counts are the actual pointwise limit. *)
Theorem projection_joint_multiplicity_tree_measurable (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (E P : seq nat -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_closed_cover_tree E -> is_cover_partition_tree E P -> borel_set A ->
  is_measure_measurable_function (@projection_product_measure R n m hmn)
    (partial_function_total (projection_joint_multiplicity (m:=m) A)).
Proof.
move=> hE hP hA.
pose F j := projection_joint_partition_count (m:=m) P A j.
have hlim z : extended_increases_to (fun j => F j z) (projection_joint_multiplicity A z).
  exact: (@partition_hit_count_limit R (inner_metric_space (@euclidean_inner_productP R n))
    E P hE hP (mapping_fibre (euclidean_projection_linear z.2) A z.1)).
have hmon i j z : (i<=j)%N -> F i z<=F j z := (hlim z).1 i j.
have he : total_extended_lower_limit F=projection_joint_multiplicity (m:=m) A.
  apply/funext=> z; exact: extended_order_limit_unique
    (total_extended_lower_limit_increases hmon z).2 (hlim z).2.
rewrite -he; apply: (total_extended_lower_limit_measurable
  (@projection_product_measure_is_measure R n m hmn))=> j.
exact: (@projection_joint_partition_count_integral R n m hmn E P A j hE hP hA).1.
Qed.

(** Source for [projection_joint_multiplicity_measurable]: direct
    first sentence of 2.10.16, p. 178. The previously sealed
    tree existence supplies the partition without any extra
    hypothesis on the Borel set A. *)
Theorem projection_joint_multiplicity_measurable (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) : borel_set A ->
  is_measure_measurable_function (@projection_product_measure R n m hmn)
    (partial_function_total (projection_joint_multiplicity (m:=m) A)).
Proof.
move=> hA.
pose X := inner_metric_space (@euclidean_inner_productP R n).
have [D [hD hden]] := euclidean_metric_separable R n.
have hX : (@setT X) !=set0 by exists (0%R : X).
pose E := @ClosedCoverTree.value R X D hD hden hX.
pose P := @CoverPartitionTree.value X E.
exact: (@projection_joint_multiplicity_tree_measurable R n m hmn E P A
  (@ClosedCoverTree.laws R X D hD hden hX) (@CoverPartitionTree.laws X E) hA).
Qed.
