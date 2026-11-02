(** Federer (1969), 1.10.1, p. 44: the evaluation bracket. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear GradedComponents Hom HomogeneousHom
  SymmetricAlgebra SymmetricGrading SymmetricForms SymmetricFormWords
  SymmetricFormExtension SymmetricFormIsomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Pairing.
Variable K : fieldType.
Variables V W : lmodType K.
Variable m : nat.
Local Notation P := (symmetric_power V m).
Local Notation A := (S_m V W m).
Local Notation H := (Hom_m W (symmetric_grading V) m).
(** Source for [symmetric_pairing_hom]: Federer 1.10.1, p. 44,
    the bracket convention following the first Hom isomorphism.
    In words: Evaluate a linear map on a symmetric power. *)
Definition symmetric_pairing_hom (x : P) (h : Hom P W) := h x.
(** Source for [symmetric_pairing]: Federer 1.10.1, p. 44,
    the bracket convention following the first Hom isomorphism.
    In words: The bracket of a symmetric vector and a form is evaluation of the corresponding linear map. *)
Definition symmetric_pairing (x : P) (f : A) := sform_to_hom f x.
(** Source for [symmetric_pairing_homogeneous]: Federer 1.10.1, p. 44,
    the bracket convention following the first Hom isomorphism.
    In words: The same bracket can use the homogeneous linear map on the full algebra. *)
Definition symmetric_pairing_homogeneous (x : P) (h : H) := h (component_val x).
(** Source for [symmetric_pairing_homE]: Federer 1.10.1, p. 44,
    the bracket convention following the first Hom isomorphism.
    In words: The Hom bracket is evaluation. *)
Lemma symmetric_pairing_homE x h : symmetric_pairing_hom x h = h x.
Proof. by []. Qed.
(** Source for [symmetric_pairing_sform_hom]: Federer 1.10.1, p. 44,
    the bracket convention following the first Hom isomorphism.
    In words: The brackets for a form and its corresponding linear map agree. *)
Lemma symmetric_pairing_sform_hom x f : symmetric_pairing x f = symmetric_pairing_hom x (sform_to_hom f).
Proof. by []. Qed.
(** Source for [symmetric_pairing_sform_homogeneous]: Federer 1.10.1, p. 44,
    the bracket convention following the first Hom isomorphism.
    In words: The bracket also agrees with the homogeneous-map interpretation. *)
Lemma symmetric_pairing_sform_homogeneous x f : symmetric_pairing x f = symmetric_pairing_homogeneous x (sform_homogeneous f).
Proof. by []. Qed.
(** Source for [symmetric_pairing_hom_identification]: Federer 1.10.1, p. 44,
    the bracket convention following the first Hom isomorphism.
    In words: The inverse form identification preserves the bracket. *)
Lemma symmetric_pairing_hom_identification x h : symmetric_pairing x (hom_to_sform h) = symmetric_pairing_hom x h.
Proof. by rewrite /symmetric_pairing hom_to_sformK. Qed.
(** Source for [symmetric_pairing_homogeneous_identification]: Federer 1.10.1, p. 44,
    the bracket convention following the first Hom isomorphism.
    In words: The inverse homogeneous-map identification preserves the bracket. *)
Lemma symmetric_pairing_homogeneous_identification x h :
  symmetric_pairing x (homogeneous_sform h) = symmetric_pairing_homogeneous x h.
Proof. by rewrite /symmetric_pairing /sform_to_hom homogeneous_sformK. Qed.
(** Source for [symmetric_pairing_tuple]: Federer 1.10.1, p. 44,
    the bracket convention following the first Hom isomorphism.
    In words: On a product of m vectors, the bracket evaluates the form on its tuple. *)
Lemma symmetric_pairing_tuple (t : m.-tuple V) f : symmetric_pairing (symmetric_tuple_component t) f = f t.
Proof. exact: sform_to_hom_tuple. Qed.
(** Source for [symmetric_pairing_bilinear]: Federer 1.10.1, p. 44,
    the bracket convention following the first Hom isomorphism.
    In words: Evaluation is bilinear in the symmetric vector and the form. *)
Lemma symmetric_pairing_bilinear : bilinear symmetric_pairing.
Proof.
split.
- move=> f; exact: hom_linear.
- move=> x a f g; rewrite /symmetric_pairing linearP hom_addE hom_scaleE; by [].
Qed.
(** Source for [symmetric_pairing_ext]: Federer 1.10.1, p. 44,
    the bracket convention following the first Hom isomorphism.
    In words: Supporting extensionality: brackets against all vectors determine a form. *)
Lemma symmetric_pairing_ext (f g : A) : (forall x, symmetric_pairing x f = symmetric_pairing x g) -> f = g.
Proof.
move=> h; have he : sform_to_hom f = sform_to_hom g by apply: hom_ext.
exact (can_inj (@sform_to_homK K V W m) he).
Qed.
End Pairing.
