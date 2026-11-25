(** Supporting canonical nature of finite-product identifications in Federer
    (1969), 2.6.5, p. 119. Ordered factor values determine the nested point
    uniquely. Consequently any explicitly given coordinate-preserving map
    has the already proved image-measure identity. Source context and
    countability correction: MeasureAssociationTrees.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import CountableMeasureSpaceUP MeasurePushforward MeasureBijectionUP
  MeasureAssociationTrees FiniteMeasureAssociations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measure_tree_coordinate_size]: supporting
    length of the ordered coordinate list in Federer
    2.6.5, p. 119: one value per original factor. *)
Lemma measure_tree_coordinate_size (R : realType) (t : measure_product_tree R)
    (x : countable_measure_carrier (measure_tree_space t)) :
  size (measure_tree_coordinates t x) = size (measure_tree_factors t).
Proof.
elim: t x=> [A x|a iha b ihb [x y]] //=.
by rewrite !size_cat iha ihb.
Qed.
Arguments measure_tree_coordinate_size {R} t x.

(** Source for [measure_tree_coordinates_injective]:
    supporting uniqueness of a nested point from its
    ordered coordinates in Federer 2.6.5, p. 119.
    Classical equality on factor labels is set-theoretic
    background already provided by the project's boolp assumptions. *)
Lemma measure_tree_coordinates_injective (R : realType) (t : measure_product_tree R) :
  injective (measure_tree_coordinates t).
Proof.
elim: t=> [A x y he|a iha b ihb [x1 x2] [y1 y2] he].
- have hp : existT (fun M : countable_measure_space R => countable_measure_carrier M) A x =
      existT (fun M : countable_measure_space R => countable_measure_carrier M) A y :=
      congr1 (head (existT _ A x)) he.
  exact (@internal_Eqdep_dec.inj_pair2_eq_dec (countable_measure_space R)
    (fun U V => pselect (U = V))
    (fun M => countable_measure_carrier M) A x y hp).
- have hl := congr1 (take (size (measure_tree_factors a))) he.
  have hr := congr1 (drop (size (measure_tree_factors a))) he.
  have ht p q : take (size (measure_tree_factors a))
      (measure_tree_coordinates a p ++ measure_tree_coordinates b q) = measure_tree_coordinates a p.
    by rewrite -(measure_tree_coordinate_size a p) take_size_cat.
  have hd p q : drop (size (measure_tree_factors a))
      (measure_tree_coordinates a p ++ measure_tree_coordinates b q) = measure_tree_coordinates b q.
    by rewrite -(measure_tree_coordinate_size a p) drop_size_cat.
  change (take (size (measure_tree_factors a)) (measure_tree_coordinates a x1 ++ measure_tree_coordinates b x2) =
    take (size (measure_tree_factors a)) (measure_tree_coordinates a y1 ++ measure_tree_coordinates b y2)) in hl.
  change (drop (size (measure_tree_factors a)) (measure_tree_coordinates a x1 ++ measure_tree_coordinates b x2) =
    drop (size (measure_tree_factors a)) (measure_tree_coordinates a y1 ++ measure_tree_coordinates b y2)) in hr.
  rewrite !ht in hl; rewrite !hd in hr.
  by rewrite (iha _ _ hl) (ihb _ _ hr).
Qed.

(** Source for [finite_product_coordinate_map_image]: the actual
    image-measure identity under any explicitly supplied canonical
    coordinate map in Federer 2.6.5, p. 119. Preservation of ordered
    coordinates identifies the map with the proved finite association
    bijection. *)
Theorem finite_product_coordinate_map_image (R : realType) (t u : measure_product_tree R)
    (f : countable_measure_carrier (measure_tree_space t) -> countable_measure_carrier (measure_tree_space u)) :
  measure_tree_factors t = measure_tree_factors u ->
  (forall x, measure_tree_coordinates u (f x) = measure_tree_coordinates t x) ->
  measure_pushforward f (countable_measure_value (measure_tree_space t)) =
    countable_measure_value (measure_tree_space u).
Proof.
move=> hfac hc; have [g [gi [hm hg]]] := finite_product_association_invariance hfac.
have he : f = g.
  apply: funext=> x; apply: measure_tree_coordinates_injective.
  by rewrite hc hg.
rewrite he; exact: measure_bijection_pushforward hm.
Qed.
