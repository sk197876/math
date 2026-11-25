(** Canonical changes of parenthesisation for Federer (1969), 2.6.5, p. 119,
    with explicit countability hypotheses. Identity, inverse, composition,
    grouping, and the displayed triple associator all retain the ordered
    factor values. Source context: MeasureAssociationTrees.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasurePushforward ProductMeasure CountablyMeasurableUP
  CountableMeasureSpaceUP MeasureBijectionUP MeasureBijectionLaws ProductMeasureBijections
  ProductMeasureAssociativity MeasureAssociationTrees.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measure_tree_identity]: supporting identity
    change of association in Federer 2.6.5, p. 119. *)
Lemma measure_tree_identity (R : realType) (t : measure_product_tree R) :
  is_measure_tree_identification t t (fun x => x) (fun x => x).
Proof. constructor; first exact: measure_bijection_identity. by []. Qed.

(** Source for [measure_tree_inverse]: supporting inverse
    change of association in Federer 2.6.5, p. 119,
    preserving the same ordered factor values. *)
Lemma measure_tree_inverse (R : realType) (t u : measure_product_tree R) f g :
  is_measure_tree_identification t u f g -> is_measure_tree_identification u t g f.
Proof.
move=> [hm hc]; constructor; first exact: measure_bijection_inverse hm.
move=> y; have h := hc (g y).
rewrite (measure_bijection_inverse_cancel hm) in h; exact: esym h.
Qed.

(** Source for [measure_tree_compose]: supporting composition
    of coordinate-preserving associations in Federer 2.6.5,
    p. 119. *)
Lemma measure_tree_compose (R : realType) (t u v : measure_product_tree R) f g h k :
  is_measure_tree_identification t u f g -> is_measure_tree_identification u v h k ->
  is_measure_tree_identification t v (fun x => h (f x)) (fun z => g (k z)).
Proof.
move=> [hm hc] [hn hd]; constructor; first exact: measure_bijection_compose hm hn.
by move=> x; rewrite hd hc.
Qed.

(** Source for [measure_tree_pair]: supporting replacement
    of grouped factors by identified associations in
    Federer 2.6.5, p. 119. *)
Lemma measure_tree_pair (R : realType) (a b c d : measure_product_tree R) f fi g gi :
  is_measure_tree_identification a c f fi -> is_measure_tree_identification b d g gi ->
  is_measure_tree_identification (MeasurePair a b) (MeasurePair c d)
    (cartesian_map f g) (cartesian_map fi gi).
Proof.
move=> [hf hfc] [hg hgc]; constructor.
- exact (@measure_bijection_product R
    (countable_measure_carrier (measure_tree_space a)) (countable_measure_carrier (measure_tree_space b))
    (countable_measure_carrier (measure_tree_space c)) (countable_measure_carrier (measure_tree_space d))
    _ _ _ _ (countable_measure_law (measure_tree_space a)) (countable_measure_law (measure_tree_space b))
    (countable_measure_law (measure_tree_space c)) (countable_measure_law (measure_tree_space d))
    f fi g gi hf hg).
- by move=> [x y]; rewrite /= /cartesian_map /= hfc hgc.
Qed.

(** Source for [measure_tree_associator]: the actual map s of Federer 2.6.5,
    p. 119, acting on arbitrary already grouped factors. the equality is not
    asserted for unrestricted measures. *)
Lemma measure_tree_associator (R : realType) (a b c : measure_product_tree R) :
  is_measure_tree_identification (MeasurePair (MeasurePair a b) c) (MeasurePair a (MeasurePair b c))
    (@product_associate (countable_measure_carrier (measure_tree_space a))
      (countable_measure_carrier (measure_tree_space b)) (countable_measure_carrier (measure_tree_space c)))
    (@product_unassociate (countable_measure_carrier (measure_tree_space a))
      (countable_measure_carrier (measure_tree_space b)) (countable_measure_carrier (measure_tree_space c))).
Proof.
constructor.
- constructor.
  + by move=> [[x y] z].
  + by move=> [x [y z]].
  + exact (@product_measure_associative_countable R
      (countable_measure_carrier (measure_tree_space a)) (countable_measure_carrier (measure_tree_space b))
      (countable_measure_carrier (measure_tree_space c)) _ _ _
      (countable_measure_law (measure_tree_space a)) (countable_measure_law (measure_tree_space b))
      (countable_measure_law (measure_tree_space c))
      (countable_measure_cover_law (measure_tree_space a)) (countable_measure_cover_law (measure_tree_space b))
      (countable_measure_cover_law (measure_tree_space c))).
- by move=> [[x y] z]; rewrite /= /product_associate /= catA.
Qed.
