(** Federer (1969), 2.6.5, pp. 119–120: supporting identification of the
    sealed Euclidean Lebesgue family with the iterated scalar products. The
    reverse coordinate order records the tail-first convention of the
    existing recursion; it is made explicit before comparing the usual block
    maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import CountableMeasureSpaceUP MeasureBijectionUP MeasureBijectionLaws
  ProductMeasureBijections MeasureAssociationTrees LebesgueMeasureTree
  LebesgueScalarMeasure EuclideanLebesgue EuclideanLebesgueBijections
  EuclideanCoordinateLists EuclideanCoordinateSplit EuclideanOneCoordinate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [lebesgue_labelled_point]: supporting labelled
    scalar coordinate in the finite product of Federer
    2.6.5, pp. 119–120. *)
Definition lebesgue_labelled_point (R : realType) (t : R) : labelled_measure_point R :=
  existT _ (lebesgue_scalar_space R) t.

(** Source for [lebesgue_tree_identification]: supporting
    actual measure-preserving coordinate identification between
    Euclidean Lebesgue measure and its scalar factors in
    Federer 2.6.5, pp. 119–120. *)
Lemma lebesgue_tree_identification (R : realType) n :
  is_measure_bijection (@positive_euclidean_lebesgue_measure R n)
    (countable_measure_value (measure_tree_space (@lebesgue_measure_tree R n)))
    (lebesgue_tree_encode n) (lebesgue_tree_decode n).
Proof.
elim: n=> [|n ih]; first exact: positive_euclidean_line_bijection.
have hp := @measure_bijection_product R _ _ _ _ _ _ _ _
  (positive_euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R)
  (countable_measure_law (measure_tree_space (@lebesgue_measure_tree R n)))
  (lebesgue_scalar_is_measure R)
  (lebesgue_tree_encode n) (lebesgue_tree_decode n) (fun t => t) (fun t => t)
  ih (measure_bijection_identity (@lebesgue_scalar_measure R)).
exact: measure_bijection_compose (positive_euclidean_split_bijection R n) hp.
Qed.

(** Source for [lebesgue_tree_decode_coordinates]: supporting
    ordered factor values of the canonical identification in
    Federer 2.6.5, pp. 119–120. Tail-first recursion
    lists the Euclidean coordinates in reverse order. *)
Lemma lebesgue_tree_decode_coordinates (R : realType) n
    (x : countable_measure_carrier (measure_tree_space (@lebesgue_measure_tree R n))) :
  measure_tree_coordinates (@lebesgue_measure_tree R n) x =
    map (@lebesgue_labelled_point R) (rev (euclidean_coordinate_list (lebesgue_tree_decode n x))).
Proof.
elim: n x=> [x|n ih [x t]].
- by rewrite /= /euclidean_one_embed /FiniteCoordinates.coordinate_head ffunE.
- change (measure_tree_coordinates (@lebesgue_measure_tree R n) x ++ [:: lebesgue_labelled_point t] =
    map (@lebesgue_labelled_point R)
      (rev (euclidean_coordinate_list (euclidean_join (lebesgue_tree_decode n x,t))))).
  by rewrite euclidean_join_coordinate_list rev_cons map_rcons ih cats1.
Qed.

(** Source for [lebesgue_tree_encode_coordinates]: supporting
    ordered-coordinate description for the forward Euclidean
    identification in Federer 2.6.5, pp. 119–120. *)
Lemma lebesgue_tree_encode_coordinates (R : realType) n x :
  measure_tree_coordinates (@lebesgue_measure_tree R n) (lebesgue_tree_encode n x) =
    map (@lebesgue_labelled_point R) (rev (euclidean_coordinate_list x)).
Proof. by rewrite lebesgue_tree_decode_coordinates lebesgue_tree_encodeK. Qed.
