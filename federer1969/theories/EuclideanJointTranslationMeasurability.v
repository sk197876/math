(** Federer (1969), 3.1.8, p. 217: joint
    measurability of the translated growth exceptional sets, by
    the linear epimorphism principle of 3.1.3(3). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanBlockMeasure EuclideanLebesgueDimensions
  EuclideanEpimorphismMeasurable EuclideanEpimorphismNull EuclideanBlockMeasurableFunctions
  MeasureUP ProductMeasure ProductFunctionMeasurability PushforwardMeasurableSets
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  PartialFunctionPair PartialFunctionPostcomposition RealMetricBackground
  MeasurableFunctionUP MeasurableGraphEquivalence MeasurableMetricDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_full_translation_map]: the map
    (a,h) to a+h used in Q(a,r,j), Federer 3.1.8,
    p. 217, expressed in the usual Euclidean block coordinates. *)
Definition euclidean_full_translation_map (R : realType) m (w : R_n R (m+m)) :
    R_n R m := (@euclidean_block_split R m m w).1+(@euclidean_block_split R m m w).2.

(** Source for [euclidean_full_translation_map_linear]:
    the elementary linearity needed for 3.1.3(3) in the
    measurability assertion of 3.1.8, p. 217. *)
Lemma euclidean_full_translation_map_linear (R : realType) m :
  linear (@euclidean_full_translation_map R m).
Proof.
move=> t x y; apply/ffunP=> i.
rewrite /euclidean_full_translation_map /euclidean_block_split /= !ffunE.
by rewrite scalerDr addrACA.
Qed.
HB.instance Definition _ (R : realType) m :=
  GRing.isLinear.Build R (R_n R (m+m)) (R_n R m) *:%R
    (@euclidean_full_translation_map R m) (@euclidean_full_translation_map_linear R m).

(** Source for [euclidean_full_translation_map_surjective]:
    the preimage (x,0) proves surjectivity for applying
    3.1.3(3) in Federer 3.1.8, p. 217. *)
Lemma euclidean_full_translation_map_surjective (R : realType) m y :
  exists w, @euclidean_full_translation_map R m w=y.
Proof.
exists (@euclidean_block_join R m m (y,0)).
by rewrite /euclidean_full_translation_map euclidean_block_joinK addr0.
Qed.

(** Source for [euclidean_joint_translation_measurable]:
    translated values f(a+h) are jointly measurable in the
    proof of Federer 3.1.8, p. 217. This uses the
    project's own epimorphism pullback theorem. *)
Lemma euclidean_joint_translation_measurable (R : realType) m (Y : topologicalType)
    (f : inner_metric_space (@euclidean_inner_productP R m)->Y) :
  is_measure_measurable_function (@euclidean_lebesgue_measure R m) (partial_function_total f) ->
  is_measure_measurable_function
    (product_measure (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_is_measure R m))
    (partial_function_total (fun ah=>f (ah.1+ah.2))).
Proof.
move=> hf.
pose p := GRing.Linear.clone _ _ _ _ (@euclidean_full_translation_map R m) _.
have hh := euclidean_block_join_measurable_precompose
  (euclidean_epimorphism_measurable_precompose (p:=p)
    (@euclidean_full_translation_map_surjective R m) hf).
apply: (measurable_function_graph_equivalent _ hh).
move=> [a h] y.
change (f (euclidean_full_translation_map (euclidean_block_join (a,h)))=y <-> f (a+h)=y).
by rewrite /euclidean_full_translation_map euclidean_block_joinK.
Qed.

(** Source for [euclidean_joint_translation_set_measurable]:
    the missing-domain alternative x notin A in Q(u,r,j),
    Federer 3.1.8, p. 217, is jointly measurable after
    translation. *)
Lemma euclidean_joint_translation_set_measurable (R : realType) m
    (A : set (inner_metric_space (@euclidean_inner_productP R m))) :
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  measure_measurable
    (product_measure (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_is_measure R m))
    [set ah | A (ah.1+ah.2)].
Proof.
move=> hA; rewrite -euclidean_block_measure.
apply: pushforward_measurable_from_preimage.
change (measure_measurable (@euclidean_lebesgue_measure R (m+m))
  ((@euclidean_full_translation_map R m) @^-1` A)).
exact: euclidean_epimorphism_preimage_measurable
  (@euclidean_full_translation_map_surjective R m) hA.
Qed.

(** Source for [euclidean_joint_translation_distance_measurable]:
    the distance |f(a+h)-f(a)| in Q, Federer 3.1.8,
    p. 217. The target can be any separable metric space;
    the theorem will be used for Euclidean targets and the source identity. *)
Lemma euclidean_joint_translation_distance_measurable (R : realType) m
    (Y : metricType R) (D : set Y)
    (f : inner_metric_space (@euclidean_inner_productP R m)->Y) :
  countable D -> dense D ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m) (partial_function_total f) ->
  is_measure_measurable_function
    (product_measure (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_is_measure R m))
    (partial_function_total
      (fun ah=>(mdist (f (ah.1+ah.2)) (f ah.1) : real_line_metric R))).
Proof.
move=> hc hd hf.
pose hmu := euclidean_lebesgue_is_measure R m.
have hs := euclidean_joint_translation_measurable hf.
have hb := product_measurable_first_function hmu hmu hf.
have hh := measurable_partial_metric_distance
  (product_measure_is_measure hmu hmu) hc hd hs hb.
apply: (measurable_function_graph_equivalent _ hh)=> ah z.
split.
- by move=> [[u v] [[<- <-] hz]].
- by move=> hz; exists (f (ah.1+ah.2),f ah.1); split; [split|].
Qed.
