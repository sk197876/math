(** Supporting finite induction on parenthesisations for Federer (1969),
    2.6.5, p. 119. Every parenthesisation has a unique fully
    right-associated form with its ordered list of factors. This file is
    purely finite set-theoretic infrastructure for the corrected measure
    theorem. Source context and correction: MeasureAssociationTrees.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import CountableMeasureSpaceUP MeasureAssociationTrees.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [measure_tree_graft]: supporting finite
    reassociation procedure for Federer 2.6.5, p. 119:
    place all factors of t before the factors of u. *)
Fixpoint measure_tree_graft (R : realType) (t u : measure_product_tree R) : measure_product_tree R :=
  match t with
  | MeasureFactor A => MeasurePair (MeasureFactor A) u
  | MeasurePair a b => measure_tree_graft a (measure_tree_graft b u)
  end.

(** Source for [measure_tree_normal_form]: supporting fully
    right-associated form in the finite induction of
    Federer 2.6.5, p. 119. *)
Fixpoint measure_tree_normal_form (R : realType) (t : measure_product_tree R) : measure_product_tree R :=
  match t with
  | MeasureFactor A => MeasureFactor A
  | MeasurePair a b => measure_tree_graft a (measure_tree_normal_form b)
  end.

(** Source for [measure_tree_right_associated]: supporting
    specification of the normal parenthesisation used to
    compare all finite products in Federer 2.6.5, p. 119. *)
Inductive measure_tree_right_associated (R : realType) : measure_product_tree R -> Prop :=
  (** Source for [measure_tree_right_leaf]: a single
      factor is already associated, Federer 2.6.5, p. 119. *)
  | measure_tree_right_leaf A : measure_tree_right_associated (MeasureFactor A)
  (** Source for [measure_tree_right_cons]: right association
      adds a single factor on the left, supporting
      Federer 2.6.5, p. 119. *)
  | measure_tree_right_cons A t : measure_tree_right_associated t ->
      measure_tree_right_associated (MeasurePair (MeasureFactor A) t).

(** Source for [measure_tree_factors_nonempty]: supporting
    nonempty-factor convention of the induction in Federer
    2.6.5, p. 119. *)
Lemma measure_tree_factors_nonempty (R : realType) (t : measure_product_tree R) :
  exists A s, measure_tree_factors t = A :: s.
Proof.
elim: t=> [A|a [A [s hs]] b _]; first by exists A, [::].
by exists A, (s ++ measure_tree_factors b); rewrite /= hs.
Qed.

(** Source for [measure_tree_graft_factors]: the finite
    reassociation preserves ordered factors, supporting
    Federer 2.6.5, p. 119. *)
Lemma measure_tree_graft_factors (R : realType) (t u : measure_product_tree R) :
  measure_tree_factors (measure_tree_graft t u) = measure_tree_factors t ++ measure_tree_factors u.
Proof. elim: t u=> [A u|a iha b ihb u] //=; by rewrite iha ihb catA. Qed.

(** Source for [measure_tree_normal_factors]: the normal
    form has the original ordered factors, supporting
    Federer 2.6.5, p. 119. *)
Lemma measure_tree_normal_factors (R : realType) (t : measure_product_tree R) :
  measure_tree_factors (measure_tree_normal_form t) = measure_tree_factors t.
Proof. elim: t=> [A|a iha b ihb] //=; by rewrite measure_tree_graft_factors ihb. Qed.

(** Source for [measure_tree_graft_right_associated]:
    supporting termination in a right-associated product
    for the finite induction of Federer 2.6.5, p. 119. *)
Lemma measure_tree_graft_right_associated (R : realType) (t u : measure_product_tree R) :
  measure_tree_right_associated u -> measure_tree_right_associated (measure_tree_graft t u).
Proof.
elim: t u=> [A u hu|a iha b ihb u hu] /=.
- exact: measure_tree_right_cons hu.
- exact (iha (measure_tree_graft b u) (ihb u hu)).
Qed.

(** Source for [measure_tree_normal_right_associated]:
    the normal form satisfies its specified association,
    supporting Federer 2.6.5, p. 119. *)
Lemma measure_tree_normal_right_associated (R : realType) (t : measure_product_tree R) :
  measure_tree_right_associated (measure_tree_normal_form t).
Proof.
elim: t=> [A|a iha b ihb] /=; first exact: measure_tree_right_leaf.
exact: measure_tree_graft_right_associated ihb.
Qed.

(** Source for [measure_tree_right_factors_injective]:
    supporting uniqueness of a normal association from its
    ordered factors in Federer 2.6.5, p. 119. *)
Lemma measure_tree_right_factors_injective (R : realType) (t u : measure_product_tree R) :
  measure_tree_right_associated t -> measure_tree_right_associated u ->
  measure_tree_factors t = measure_tree_factors u -> t = u.
Proof.
move=> ht; elim: ht u=> [A u hu he|A v0 ht ih u hu he].
- case: hu he=> [B|B v hv] /= he.
  + have hAB : A = B := congr1 (head A) he; by rewrite hAB.
  + have [C [s hs]] := measure_tree_factors_nonempty v.
    rewrite hs in he; discriminate he.
- case: hu he=> [B|B v hv] /= he.
  + have [C [s hs]] := measure_tree_factors_nonempty v0.
    rewrite hs in he; discriminate he.
  + have hAB : A = B := congr1 (head A) he.
    have htv : measure_tree_factors v0 = measure_tree_factors v := congr1 behead he.
    by rewrite hAB (ih v hv htv).
Qed.

(** Source for [measure_tree_normal_form_unique]: all
    associations of the same ordered finite factors have
    the same normal form, supporting Federer 2.6.5,
    p. 119. No measure equality is assumed in this
    purely combinatorial step. *)
Theorem measure_tree_normal_form_unique (R : realType) (t u : measure_product_tree R) :
  measure_tree_factors t = measure_tree_factors u -> measure_tree_normal_form t = measure_tree_normal_form u.
Proof.
move=> he; apply: measure_tree_right_factors_injective;
  try exact: measure_tree_normal_right_associated.
by rewrite !measure_tree_normal_factors.
Qed.
