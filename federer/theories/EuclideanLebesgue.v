(** Public Euclidean Lebesgue products for Federer (1969), 2.6.5, pp.
    119–120. Positive-dimensional measures are used through the sealed
    inductive laws. Stage n denotes dimension n+1. The first coordinate is
    the scalar factor in the successor identification. Source context and
    the equivalent product convention: EuclideanLebesgueUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MeasureUP MeasurePushforward
  ProductMeasureUP ProductMeasure LebesgueScalarMeasure EuclideanCoordinateSplit EuclideanOneCoordinate
  EuclideanLebesgueUP EuclideanLebesgueSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [positive_euclidean_lebesgue_measure]: the
    n+1-dimensional Lebesgue product in Federer 2.6.5,
    pp. 119–120, with the construction hidden by a seal. *)
Definition positive_euclidean_lebesgue_measure (R : realType) := @EuclideanLebesgue.value R.
Arguments positive_euclidean_lebesgue_measure {R} n A.

(** Source for [positive_euclidean_lebesgue_specification]:
    inductive product laws of Federer 2.6.5, pp. 119–120. *)
Lemma positive_euclidean_lebesgue_specification (R : realType) :
  is_euclidean_lebesgue_family (@positive_euclidean_lebesgue_measure R).
Proof. exact: EuclideanLebesgue.laws. Qed.

(** Source for [positive_euclidean_lebesgue_is_measure]:
    each finite Euclidean product is a measure, Federer
    2.6.5, pp. 119–120. *)
Lemma positive_euclidean_lebesgue_is_measure (R : realType) n :
  is_measure (@positive_euclidean_lebesgue_measure R n).
Proof. exact (@euclidean_lebesgue_measure_law R (@positive_euclidean_lebesgue_measure R) (positive_euclidean_lebesgue_specification R) n). Qed.

(** Source for [positive_euclidean_lebesgue_first]: the
    single factor from Federer 2.5.17, p. 111, under
    its one-coordinate identification in 2.6.5, p. 119. *)
Lemma positive_euclidean_lebesgue_first (R : realType) :
  @positive_euclidean_lebesgue_measure R 0 =
    measure_pushforward (@euclidean_one_embed R) (@lebesgue_scalar_measure R).
Proof. exact: euclidean_lebesgue_first_law (positive_euclidean_lebesgue_specification R). Qed.

(** Source for [positive_euclidean_lebesgue_split_product]:
    the one-scalar instance of the block-product identity
    in Federer 2.6.5, p. 120, directly from its
    inductive product specification. *)
Lemma positive_euclidean_lebesgue_split_product (R : realType) n :
  measure_pushforward (@euclidean_split R n.+1) (@positive_euclidean_lebesgue_measure R n.+1) =
    product_measure (positive_euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R).
Proof.
exact: product_measure_unique
  (euclidean_lebesgue_successor_law (positive_euclidean_lebesgue_specification R) n)
  (product_measure_specification (positive_euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R)).
Qed.

(** Source for [positive_euclidean_lebesgue_successor]:
    the same inductive law in the inverse coordinate
    direction, supporting Federer 2.6.5, pp. 119–120.
    It is derived from the specification and inverse laws. *)
Lemma positive_euclidean_lebesgue_successor (R : realType) n :
  @positive_euclidean_lebesgue_measure R n.+1 =
    measure_pushforward (@euclidean_join R n.+1)
      (product_measure (positive_euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R)).
Proof.
rewrite -positive_euclidean_lebesgue_split_product.
apply: funext=> A; rewrite /measure_pushforward.
congr (positive_euclidean_lebesgue_measure _ _).
apply/seteqP; split=> x /=; by rewrite euclidean_splitK.
Qed.
