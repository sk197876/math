(** Federer (1969), 3.2.11, p. 249: Borelness
    and Lebesgue measure of Q=A times B(0,1). Use
    the actual block isomorphism of 2.6.5 and the
    product rectangle theorem of 2.6.2. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanBlockMeasure EuclideanLebesgueDimensions
  CoareaCylinderFibres TopologicalBorel BorelFamilyBasic ContinuousBorelPreimages
  TopologicalProductMaps MeasureUP MeasurePushforward ProductMeasure ProductRectangleValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_cylinder_borel]: the Borel
    source Q in the first-case application of Federer
    3.2.11, p. 249. Supporting product-set assertion
    for any Borel A and B, including empty blocks. *)
Lemma coarea_cylinder_borel (R:realType) m n (A:set (R_n R m)) (B:set (R_n R n)):
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] A ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] B ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R (m+n))]
    (coarea_cylinder A B).
Proof.
move=>hA hB.
pose X:=inner_metric_space (@euclidean_inner_productP R (m+n)).
pose M:=inner_metric_space (@euclidean_inner_productP R m).
pose N:=inner_metric_space (@euclidean_inner_productP R n).
pose p:=fun x:X=>(@euclidean_first_block R m n x:M).
pose q:=fun x:X=>(@euclidean_last_block R m n x:N).
have hp:continuous p.
  move=>x; exact (continuous_comp (@euclidean_block_split_continuous R m n x)
    (@first_projection_continuous [the topologicalType of M] [the topologicalType of N]
      (euclidean_block_split x))).
have hq:continuous q.
  move=>x; exact (continuous_comp (@euclidean_block_split_continuous R m n x)
    (@second_projection_continuous [the topologicalType of M] [the topologicalType of N]
      (euclidean_block_split x))).
change (@borel_set [the topologicalType of X] ((p @^-1` A) `&` (q @^-1` B))).
exact (borel_family_binary_intersection (borel_sets_family [the topologicalType of X])
  (continuous_borel_preimage hp hA) (continuous_borel_preimage hq hB)).
Qed.

(** Source for [coarea_cylinder_lebesgue_mass]: the product
    source mass in the first inequality of Federer 3.2.11,
    p. 249. For any measurable factors the actual
    cylinder has Lebesgue measure Leb^m(A) Leb^n(B), including
    infinite values and the existing zero-times-infinity convention. *)
Lemma coarea_cylinder_lebesgue_mass (R:realType) m n (A:set (R_n R m)) (B:set (R_n R n)):
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  measure_measurable (@euclidean_lebesgue_measure R n) B ->
  euclidean_lebesgue_measure (m+n) (coarea_cylinder A B)=
    euclidean_lebesgue_measure m A*euclidean_lebesgue_measure n B.
Proof.
move=>hA hB.
have hBlock:=congr1 (fun mu=>mu (A `*` B)) (@euclidean_block_measure R m n).
change (euclidean_lebesgue_measure (m+n) (coarea_cylinder A B)=
  product_measure (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_is_measure R n)
    (A `*` B)) in hBlock.
rewrite hBlock.
exact (@product_measure_rectangle_value R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  (@euclidean_lebesgue_measure R m) (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_is_measure R n) A B hA hB).
Qed.
