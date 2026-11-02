(** Federer (1969), 2.10.5, p. 172, opening definition and measurability
    paragraph, paraphrased: f_S(p) is the Lebesgue volume of p(S), and is
    theta* measurable for Suslin S. First prove the stronger supporting
    statement for any finite Borel regular parameter measure. The eventual
    application uses the normalized invariant measure of 2.7.16(6), p. 139.
    Suslin measurability and Fubini are the locally proved 2.2.12 and 2.6.2,
    pp. 68, 115–117. No relevant correction occurs in the local erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueHaar EuclideanProjectionSpace EuclideanProjectionMetric
  ProjectedVolumeIncidence SuslinSetUP SuslinMeasurability TopologicalBorel
  CountableOpenBaseUP SeparableMetricBaseSealed MeasureUP MeasureBasic MeasureSplit
  BorelRegularMeasureUP ProductMeasure ProductBorelRegularity ProductSections
  CountablyMeasurableUP CountablyMeasurableBasic CountablyMeasurableProduct
  CountablyMeasurableSubsets PartialFunctionBasic MeasurableFunctionUP
  MeasureIntegralUP ProductSetFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projected_volume_function]: direct
    definition f_S(p)=L^m[p(S)] in Federer 2.10.5,
    p. 172. Its values remain extended real, so
    unbounded sets with infinite projections are included. *)
Definition projected_volume_function (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) : extended_real_line R :=
  euclidean_lebesgue_measure m (euclidean_projection_linear p @` S).

(** Source for [projected_volume_function_nonnegative]:
    supporting nonnegativity of f_S in Federer 2.10.5,
    p. 172, from the actual Lebesgue measure laws. *)
Lemma projected_volume_function_nonnegative (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) :
  0 <= projected_volume_function S p.
Proof. exact: measure_nonnegative (euclidean_lebesgue_is_measure R m) _. Qed.

(** Source for [projected_volume_function_empty]:
    supporting empty-set case of the function defined
    in Federer 2.10.5, p. 172. It also holds
    with the existing zero-dimensional Lebesgue convention. *)
Lemma projected_volume_function_empty (R : realType) (n m : nat)
    (p : orthogonal_projection_metric_space R n m) :
  projected_volume_function set0 p = 0.
Proof.
rewrite /projected_volume_function image_set0.
exact: measure_empty (euclidean_lebesgue_is_measure R m).
Qed.

(** Source for [projection_incidence_product_measurable]:
    direct product-measurability step in Federer
    2.10.5, p. 172. This supporting generalization
    permits any Borel regular parameter measure; its
    finite mass is not required at this step. *)
Theorem projection_incidence_product_measurable (R : realType) (n m : nat)
    (theta : set (orthogonal_projection_metric_space R n m) -> \bar R)
    (ht : is_measure theta)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_borel_regular_measure theta -> is_suslin_set R S ->
  measure_measurable (product_measure (euclidean_lebesgue_is_measure R m) ht)
    (projection_incidence (m:=m) S).
Proof.
move=> hr hS.
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose P := orthogonal_projection_metric_space R n m.
have [U hU] := euclidean_countable_open_base R m.
have [D [hc hd]] := orthogonal_projection_metric_separable R n m.
pose V := @SeparableMetricBase.value R P D hc hd.
have hV := @SeparableMetricBase.laws R P D hc hd.
have hprod := @product_measure_borel_regular R Y P
  (@euclidean_lebesgue_measure R m) theta (euclidean_lebesgue_is_measure R m)
  ht U V hU hV (euclidean_lebesgue_borel_regular R m) hr.
apply: (@suslin_set_measurable R (Y*P)%type _
  (product_measure_is_measure (euclidean_lebesgue_is_measure R m) ht)
  (projection_incidence (m:=m) S)); last exact: projection_incidence_suslin hS.
move=> C hC; apply: (borel_regular_borel_measurable
  (product_measure_is_measure (euclidean_lebesgue_is_measure R m) ht) hprod).
exact: closed_borel_set hC.
Qed.

(** Source for [projected_volume_function_measurable]:
    direct conclusion of the measurability paragraph
    in Federer 2.10.5, p. 172, generalized to
    any finite Borel regular parameter measure. Fubini
    yields measurability of the actual total section-
    volume function, with infinite values preserved. *)
Theorem projected_volume_function_measurable (R : realType) (n m : nat)
    (theta : set (orthogonal_projection_metric_space R n m) -> \bar R)
    (ht : is_measure theta)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_borel_regular_measure theta -> theta setT < +oo -> is_suslin_set R S ->
  is_measure_measurable_function theta (partial_function_total (projected_volume_function S)).
Proof.
move=> hr hfin hS.
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose P := orthogonal_projection_metric_space R n m.
pose hm := euclidean_lebesgue_is_measure R m.
have hwhole : measure_countably_measurable (product_measure hm ht) setT.
  apply: product_whole_countably_measurable.
  - exact: euclidean_lebesgue_countably_measurable.
  - apply: finite_measurable_set_countably_measurable=> //.
    exact: measure_measurable_whole ht.
have hinc := projection_incidence_product_measurable ht hr hS.
have hcount := @measurable_subset_countably_measurable R (Y*P)%type
  (product_measure hm ht) (product_measure_is_measure hm ht)
  (projection_incidence (m:=m) S) setT hinc (fun _ _ => I) hwhole.
have hf := (@product_set_fubini R Y P (@euclidean_lebesgue_measure R m)
  theta hm ht (projection_incidence (m:=m) S) hcount).2.2.2.1.
have he : (fun p => euclidean_lebesgue_measure m
    (product_horizontal_section (projection_incidence (m:=m) S) p)) =
    projected_volume_function S.
  apply: funext=> p; rewrite /product_horizontal_section
    projection_incidence_horizontal_section; by [].
by rewrite he in hf.
Qed.
