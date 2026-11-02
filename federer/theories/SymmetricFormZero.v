(** Federer (1969), 1.10.1, p. 44: the convention S^0(V,W)=W. Both
    identifications are linear and inverse. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import AlternatingForms SymmetricForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section DegreeZero.
Variable K : fieldType.
Variables V W : lmodType K.

(** Source for [zero_sform_multilinear]: Federer 1.10.1, p. 44,
    degree-zero convention. In words: There are no argument positions to check in degree zero. *)
Lemma zero_sform_multilinear (w : W) : @m_linear K V W 0 (fun _ => w).
Proof.
move=> s t h; have hs := h.
by rewrite size_cat /= addnS in hs.
Qed.
(** Source for [zero_sform_tuple_symmetric]: Federer 1.10.1, p. 44,
    degree-zero convention. In words: A constant function on the single empty tuple is symmetric. *)
Lemma zero_sform_tuple_symmetric (w : W) : @tuple_symmetric K V W 0 (fun _ => w).
Proof. by move=> s t _. Qed.
(** Source for [zero_sform]: Federer 1.10.1, p. 44,
    degree-zero convention. In words: Include a coefficient as a degree-zero symmetric form. *)
Definition zero_sform (w : W) : S_m V W 0 :=
  @SymmetricForm K V W 0 (fun _ => w)
    (introT (asboolP _) (conj (zero_sform_multilinear w) (zero_sform_tuple_symmetric w))).
(** Source for [zero_sform_value]: Federer 1.10.1, p. 44,
    degree-zero convention. In words: Recover the coefficient by evaluating on the empty tuple. *)
Definition zero_sform_value (f : S_m V W 0) : W := f [tuple].
(** Source for [zero_sformE]: Federer 1.10.1, p. 44,
    degree-zero convention. In words: A degree-zero constant form evaluates as its coefficient. *)
Lemma zero_sformE w t : zero_sform w t = w.
Proof. by []. Qed.
(** Source for [zero_sformK]: Federer 1.10.1, p. 44,
    degree-zero convention. In words: Evaluation recovers the included coefficient. *)
Lemma zero_sformK : cancel zero_sform zero_sform_value.
Proof. by []. Qed.
(** Source for [zero_sform_valueK]: Federer 1.10.1, p. 44,
    degree-zero convention. In words: Inclusion recovers the original zero-form from its empty-tuple value. *)
Lemma zero_sform_valueK : cancel zero_sform_value zero_sform.
Proof. move=> f; apply: sform_ext => t; by rewrite (tuple0 t). Qed.
(** Source for [zero_sform_linear]: Federer 1.10.1, p. 44,
    degree-zero convention. In words: Inclusion of coefficients is linear. *)
Lemma zero_sform_linear : linear zero_sform.
Proof. move=> a x y; apply: sform_ext => t; by []. Qed.
HB.instance Definition _ := GRing.isLinear.Build K W (S_m V W 0)
  *:%R zero_sform zero_sform_linear.
(** Source for [zero_sform_value_linear]: Federer 1.10.1, p. 44,
    degree-zero convention. In words: Evaluation is linear. Together with both cancellation laws this proves the degree-zero identification. *)
Lemma zero_sform_value_linear : linear zero_sform_value.
Proof. by move=> a f g; rewrite /zero_sform_value sform_addE sform_scaleE. Qed.
HB.instance Definition _ := GRing.isLinear.Build K (S_m V W 0) W
  *:%R zero_sform_value zero_sform_value_linear.
End DegreeZero.
