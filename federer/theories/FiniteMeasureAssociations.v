(** Federer (1969), 2.6.5, p. 119: independence of all finite
    parenthesisations. We reduce each finite product to a common association
    using the proved canonical triple maps. The final bijection preserves
    every ordered factor coordinate and the actual measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import CountableMeasureSpaceUP MeasureAssociationTrees
  MeasureAssociationNormalForm MeasureAssociationTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [measure_tree_equivalent]: supporting existence
    of a canonical coordinate identification between two
    associations in Federer 2.6.5, p. 119. The
    specification includes both inverse identities, the
    image-measure law, and preservation of ordered coordinates. *)
Definition measure_tree_equivalent (R : realType) (t u : measure_product_tree R) : Prop :=
  exists f g, is_measure_tree_identification t u f g.

(** Source for [measure_tree_equivalent_refl]: supporting
    identity association in Federer 2.6.5, p. 119. *)
Lemma measure_tree_equivalent_refl (R : realType) (t : measure_product_tree R) : measure_tree_equivalent t t.
Proof. exists (fun x => x), (fun x => x); exact: measure_tree_identity. Qed.

(** Source for [measure_tree_equivalent_sym]: supporting
    reversal of the canonical association in Federer
    2.6.5, p. 119. *)
Lemma measure_tree_equivalent_sym (R : realType) (t u : measure_product_tree R) :
  measure_tree_equivalent t u -> measure_tree_equivalent u t.
Proof. move=> [f [g h]]; exists g, f; exact: measure_tree_inverse h. Qed.

(** Source for [measure_tree_equivalent_trans]: supporting
    successive changes of association in Federer 2.6.5,
    p. 119. *)
Lemma measure_tree_equivalent_trans (R : realType) (t u v : measure_product_tree R) :
  measure_tree_equivalent t u -> measure_tree_equivalent u v -> measure_tree_equivalent t v.
Proof.
move=> [f [g h]] [j [k l]]; exists (fun x => j (f x)), (fun z => g (k z)).
exact: measure_tree_compose h l.
Qed.

(** Source for [measure_tree_equivalent_pair]: supporting
    association changes within grouped factors, Federer
    2.6.5, p. 119. *)
Lemma measure_tree_equivalent_pair (R : realType) (a b c d : measure_product_tree R) :
  measure_tree_equivalent a c -> measure_tree_equivalent b d ->
  measure_tree_equivalent (MeasurePair a b) (MeasurePair c d).
Proof.
move=> [f [fi hf]] [g [gi hg]].
eexists; eexists; exact: measure_tree_pair hf hg.
Qed.

(** Source for [measure_tree_equivalent_associate]: supporting existence of
    the displayed triple identification in Federer 2.6.5, p. 119, under the
    correction. *)
Lemma measure_tree_equivalent_associate (R : realType) (a b c : measure_product_tree R) :
  measure_tree_equivalent (MeasurePair (MeasurePair a b) c) (MeasurePair a (MeasurePair b c)).
Proof. eexists; eexists; exact: measure_tree_associator. Qed.

(** Source for [measure_tree_graft_identification]: supporting
    finite induction combining canonical triple maps in
    Federer 2.6.5, p. 119. Countable measurability of
    grouped products was proved from that of their factors. *)
Lemma measure_tree_graft_identification (R : realType) (t u : measure_product_tree R) :
  measure_tree_equivalent (MeasurePair t u) (measure_tree_graft t u).
Proof.
elim: t u=> [A u|a iha b ihb u] /=; first exact: measure_tree_equivalent_refl.
apply: (@measure_tree_equivalent_trans R _ (MeasurePair a (MeasurePair b u)));
  first exact: measure_tree_equivalent_associate.
apply: (@measure_tree_equivalent_trans R _ (MeasurePair a (measure_tree_graft b u))).
- exact: measure_tree_equivalent_pair (measure_tree_equivalent_refl a) (ihb u).
- exact: iha.
Qed.

(** Source for [measure_tree_normal_identification]: each finite product has
    its canonical identification with a common right association, supporting
    Federer 2.6.5, p. 119. *)
Lemma measure_tree_normal_identification (R : realType) (t : measure_product_tree R) :
  measure_tree_equivalent t (measure_tree_normal_form t).
Proof.
elim: t=> [A|a iha b ihb] /=; first exact: measure_tree_equivalent_refl.
apply: (@measure_tree_equivalent_trans R _ (MeasurePair a (measure_tree_normal_form b))).
- exact: measure_tree_equivalent_pair (measure_tree_equivalent_refl a) ihb.
- exact: measure_tree_graft_identification.
Qed.

(** Source for [finite_product_association_invariance]: complete corrected
    arbitrary-finite-association assertion of Federer 2.6.5, p. 119 Any two
    parenthesisations of the same ordered factors have a measure-preserving
    bijection retaining all factor coordinates. This includes one factor and
    empty factor spaces, but assumes every factor countably measurable. *)
Theorem finite_product_association_invariance (R : realType) (t u : measure_product_tree R) :
  measure_tree_factors t = measure_tree_factors u ->
  exists f g, is_measure_tree_identification t u f g.
Proof.
move=> he; apply: (@measure_tree_equivalent_trans R _ (measure_tree_normal_form t)).
- exact: measure_tree_normal_identification.
- rewrite (measure_tree_normal_form_unique he).
  exact: measure_tree_equivalent_sym (measure_tree_normal_identification u).
Qed.
