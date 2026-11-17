(** The original Gillespie product equality in
    Federer (1969), 3.2.45, p. 280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates EuclideanCartesianMap
  EuclideanLebesgueDimensions IntegralGeometricMeasure ConvexIntegralGeometricSections GillespieProductUpper
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureExtendedCharacteristicIntegral ExtendedRealPartial
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_geometric_euclidean_product_lower_bound]: direct
    lower direction of the product display in Federer
    3.2.45, p. 280. The all-set section inequality
    applies to the actual Cartesian set. Its section
    mass is the original second-factor mass times the
    sealed characteristic function of U. The proved
    extended characteristic integral evaluates its ordinary
    integral for every Lebesgue-measurable U and arbitrary
    V, including infinite masses. This helper also
    gives the trivial totalized lower bound at undefined
    zero-times-infinity endpoints; the equality below
    retains the original partial-product domain. *)
Theorem convex_geometric_euclidean_product_lower_bound (R : realType) m q k (hKQ : (k<=q)%N)
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R q))) :
  measure_measurable (@euclidean_lebesgue_measure R m) U ->
  @euclidean_lebesgue_measure R m U* @convex_integral_geometric_measure R q k hKQ 1 V<=
    @convex_integral_geometric_measure R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1
      (euclidean_cartesian_set U V).
Proof.
move=> hU.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose nu := @convex_integral_geometric_measure R q k hKQ 1.
pose hNu := @convex_integral_geometric_measure_is_measure R q k hKQ 1 (lexx 1).
pose s := @CharacteristicFunction.value R X U.
pose hs := @CharacteristicFunction.laws R X U.
have hFunction : (fun y : X => (nu [set z | euclidean_cartesian_set U V
    (@euclidean_block_join R m q (y,z))] : extended_real_line R))=
    (fun y : X => (nu V*(s y)%:E : extended_real_line R)).
  apply: funext=> y.
  case: (pselect (U y))=> hy.
  - have hOn : s y= 1%R := characteristic_on_set hs hy.
    rewrite hOn mule1.
    congr (nu _); apply/seteqP; split=> z hz.
    + have hPair : U (euclidean_block_split (euclidean_block_join (y,z))).1 /\
          V (euclidean_block_split (euclidean_block_join (y,z))).2 := hz.
      rewrite euclidean_block_joinK /= in hPair; exact hPair.2.
    + change (U (euclidean_block_split (euclidean_block_join (y,z))).1 /\
          V (euclidean_block_split (euclidean_block_join (y,z))).2).
      by rewrite euclidean_block_joinK /=; split.
  - have hOff : s y=0%R := characteristic_off_set hs hy.
    rewrite hOff mule0.
    have hEmpty : [set z | euclidean_cartesian_set U V (@euclidean_block_join R m q (y,z))]=set0.
      apply/seteqP; split=> z; last by [].
      change (~ (U (euclidean_block_split (euclidean_block_join (y,z))).1 /\
        V (euclidean_block_split (euclidean_block_join (y,z))).2)).
      rewrite euclidean_block_joinK /=; by move=> [h _]; case: (hy h).
    have hNuEmpty : nu set0=0 := measure_empty hNu.
    by rewrite hEmpty hNuEmpty.
have hSection := @convex_integral_geometric_section_upper_integral R m q k hKQ
  (euclidean_cartesian_set U V).
rewrite hFunction in hSection.
have hIntegral := @measure_nonnegative_extended_characteristic_integral R X
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m) U s (nu V)
  hs hU (measure_nonnegative hNu V).
have hValue := measure_upper_integral_unique (measure_upper_integral_specification _ _) hIntegral.2.1.
rewrite hValue muleC in hSection; exact hSection.
Qed.

(** Source for [federer_3_2_45_product]: direct original
    product equality on p. 280 of Federer
    3.2.45. The first factor is Lebesgue measurable;
    the second is arbitrary. Retain exactly the
    ordinary defined-product condition of 2.1.1,
    p. 51. No finite mass, positive mass,
    positive dimension or second-factor measurability
    hypothesis is added. *)
Theorem federer_3_2_45_product (R : realType) m q k (hKQ : (k<=q)%N)
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R q))) :
  measure_measurable (@euclidean_lebesgue_measure R m) U ->
  mule_def (@euclidean_lebesgue_measure R m U) (@convex_integral_geometric_measure R q k hKQ 1 V) ->
  @convex_integral_geometric_measure R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1
    (euclidean_cartesian_set U V)=
    @euclidean_lebesgue_measure R m U* @convex_integral_geometric_measure R q k hKQ 1 V.
Proof.
move=> hMeasurable hDomain; apply/eqP; rewrite eq_le.
apply/andP; split.
- exact: gillespie_euclidean_product_upper hDomain.
- exact: convex_geometric_euclidean_product_lower_bound hMeasurable.
Qed.

(** Source for [federer_3_2_45_product_graph]: equivalent
    partial-arithmetic presentation of the product display
    in Federer 3.2.45, p. 280. The original
    scalar product of 2.1.1, p. 51,
    returns precisely the actual Cartesian mass. *)
Theorem federer_3_2_45_product_graph (R : realType) m q k (hKQ : (k<=q)%N)
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R q))) :
  measure_measurable (@euclidean_lebesgue_measure R m) U ->
  mule_def (@euclidean_lebesgue_measure R m U) (@convex_integral_geometric_measure R q k hKQ 1 V) ->
  extended_multiply (@euclidean_lebesgue_measure R m U) (@convex_integral_geometric_measure R q k hKQ 1 V)=
    Some (@convex_integral_geometric_measure R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1
      (euclidean_cartesian_set U V)).
Proof.
move=> hMeasurable hDomain.
rewrite /extended_multiply hDomain.
by rewrite (@federer_3_2_45_product R m q k hKQ U V hMeasurable hDomain).
Qed.
