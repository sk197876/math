(** Supporting canonical Euclidean product identifications for Federer
    (1969), 2.6.5, pp. 119–120, through their proved inverse and
    image-measure laws. These are consequences of the sealed family, not
    computations through its construction. Source context:
    EuclideanLebesgueUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MeasureUP MeasurePushforward ProductMeasure
  MeasureBijectionUP LebesgueScalarMeasure EuclideanOneCoordinate EuclideanCoordinateSplit
  EuclideanCoordinateLists EuclideanLebesgue EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [positive_euclidean_line_bijection]: the
    scalar-line identification of the first Euclidean
    product in Federer 2.6.5, pp. 119–120. *)
Lemma positive_euclidean_line_bijection (R : realType) :
  is_measure_bijection (@positive_euclidean_lebesgue_measure R 0) (@lebesgue_scalar_measure R)
    (@euclidean_one_project R) (@euclidean_one_embed R).
Proof.
constructor; [exact: euclidean_one_projectK | exact: euclidean_one_embedK |].
rewrite positive_euclidean_lebesgue_first; apply: funext=> A; rewrite /measure_pushforward.
congr (lebesgue_scalar_measure _); apply/seteqP; split=> t /=; by rewrite euclidean_one_embedK.
Qed.

(** Source for [positive_euclidean_split_bijection]: the
    inductive one-scalar product identification of Federer
    2.6.5, p. 120, with both inverse identities. *)
Lemma positive_euclidean_split_bijection (R : realType) n :
  is_measure_bijection (@positive_euclidean_lebesgue_measure R n.+1)
    (product_measure (positive_euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R))
    (@euclidean_split R n.+1) (@euclidean_join R n.+1).
Proof.
constructor; [exact: euclidean_splitK | exact: euclidean_joinK | exact: positive_euclidean_lebesgue_split_product].
Qed.

(** Source for [euclidean_dimension_cast_bijection]: supporting
    arithmetic reindexing in the usual block identity of
    Federer 2.6.5, p. 120. Equal dimensions carry
    exactly the same measure after the identity transport. *)
Lemma euclidean_dimension_cast_bijection (R : realType) n m (h : n = m) :
  is_measure_bijection (@euclidean_lebesgue_measure R n) (@euclidean_lebesgue_measure R m)
    (euclidean_dimension_cast h) (euclidean_dimension_cast (esym h)).
Proof. destruct h; constructor=> //; by apply: funext=> A. Qed.
