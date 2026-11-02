(** Supporting comparison of Euclidean Lebesgue products with all finite
    associations in Federer (1969), 2.6.5, pp. 119–120. The tree records the
    same left association as the sealed Euclidean family's tail-and-head
    recursion. Source context and the countability correction:
    MeasureAssociationTrees.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP CountablyMeasurableUP CountableMeasureSpaceUP LebesgueScalarMeasure
  MeasureAssociationTrees EuclideanInnerProduct InnerMetric FiniteCoordinates
  EuclideanOneCoordinate EuclideanCoordinateSplit EuclideanCoordinateLists.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_scalar_space]: the scalar factor
    L^1 of Federer 2.6.5, pp. 119–120, with its
    proved countable cover and measure laws. *)
Definition lebesgue_scalar_space (R : realType) : countable_measure_space R :=
  @Build_countable_measure_space R (Choice.clone R _) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) (lebesgue_scalar_countably_measurable R).

(** Source for [lebesgue_measure_tree]: supporting explicit
    left association of n+1 copies of L^1 in Federer
    2.6.5, pp. 119–120. *)
Fixpoint lebesgue_measure_tree (R : realType) n : measure_product_tree R :=
  match n with
  | 0 => MeasureFactor (lebesgue_scalar_space R)
  | k.+1 => MeasurePair (@lebesgue_measure_tree R k) (MeasureFactor (lebesgue_scalar_space R))
  end.

(** Source for [lebesgue_tree_factors]: supporting ordered
    factor list for the Euclidean product of Federer
    2.6.5, pp. 119–120: exactly n+1 copies of L^1. *)
Lemma lebesgue_tree_factors (R : realType) n :
  measure_tree_factors (@lebesgue_measure_tree R n) = nseq n.+1 (lebesgue_scalar_space R).
Proof.
elim: n=> [|n ih] //=; rewrite ih.
change (nseq n.+1 (lebesgue_scalar_space R) ++ nseq 1 (lebesgue_scalar_space R) = nseq n.+2 (lebesgue_scalar_space R)).
by rewrite -nseqD addn1.
Qed.

(** Source for [lebesgue_tree_encode]: supporting Euclidean
    coordinate map to the nested factors in Federer
    2.6.5, pp. 119–120, following the family's
    verified tail-and-head decomposition. *)
Fixpoint lebesgue_tree_encode (R : realType) n :
    inner_metric_space (@euclidean_inner_productP R n.+1) ->
    countable_measure_carrier (measure_tree_space (@lebesgue_measure_tree R n)) :=
  match n as k return inner_metric_space (@euclidean_inner_productP R k.+1) ->
    countable_measure_carrier (measure_tree_space (@lebesgue_measure_tree R k)) with
  | 0 => @euclidean_one_project R
  | k.+1 => fun x => (@lebesgue_tree_encode R k (coordinate_tail x), coordinate_head x)
  end.
Arguments lebesgue_tree_encode {R} n x.

(** Source for [lebesgue_tree_decode]: supporting inverse
    Euclidean coordinate map for Federer 2.6.5,
    pp. 119–120. *)
Fixpoint lebesgue_tree_decode (R : realType) n :
    countable_measure_carrier (measure_tree_space (@lebesgue_measure_tree R n)) ->
    inner_metric_space (@euclidean_inner_productP R n.+1) :=
  match n as k return countable_measure_carrier (measure_tree_space (@lebesgue_measure_tree R k)) ->
    inner_metric_space (@euclidean_inner_productP R k.+1) with
  | 0 => @euclidean_one_embed R
  | k.+1 => fun p => euclidean_join (@lebesgue_tree_decode R k p.1,p.2)
  end.
Arguments lebesgue_tree_decode {R} n x.

(** Source for [lebesgue_tree_encodeK]: supporting inverse
    identity for the Euclidean association map of Federer
    2.6.5, pp. 119–120. *)
Lemma lebesgue_tree_encodeK (R : realType) n :
  cancel (@lebesgue_tree_encode R n) (lebesgue_tree_decode n).
Proof.
elim: n=> [|n ih] x; first exact: euclidean_one_projectK.
change (euclidean_join (lebesgue_tree_decode n (lebesgue_tree_encode n (coordinate_tail x)),coordinate_head x) = x).
rewrite ih; exact: euclidean_splitK.
Qed.

(** Source for [lebesgue_tree_decodeK]: supporting other
    inverse identity for Federer 2.6.5, pp. 119–120. *)
Lemma lebesgue_tree_decodeK (R : realType) n :
  cancel (@lebesgue_tree_decode R n) (lebesgue_tree_encode n).
Proof.
elim: n=> [|n ih]; first exact: euclidean_one_embedK.
move=> [x t].
change ((lebesgue_tree_encode n (euclidean_split (euclidean_join (lebesgue_tree_decode n x,t))).1,
  (euclidean_split (euclidean_join (lebesgue_tree_decode n x,t))).2) = (x,t)).
by rewrite euclidean_joinK /= ih.
Qed.
