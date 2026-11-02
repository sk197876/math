(** Federer (1969), 1.7.9, p. 35: the specified inner product and associated
    norm on the space of linear maps. Only sealed laws are used here. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerDual TensorInner
  Hom Gamma LinearBasis HomInnerUP HomInnerSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Interface.
Variable R : rcfType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [hom_inner]: Federer 1.7.9, p. 35, final
    sentence: the inner product of maps abbreviates that of their
    canonical tensors. *)
Definition hom_inner := @HomInner.product R V W B C hB hC n e he.

(** Source for [hom_innerP]: Federer 1.7.9, p. 35, the
    public inner product satisfies the abstract specification. *)
Theorem hom_innerP : is_hom_inner_product hB hC he hom_inner.
Proof. exact: HomInner.laws. Qed.

(** Source for [hom_inner_productP]: Federer 1.7.9, p. 35,
    the product of maps is an inner product. *)
Theorem hom_inner_productP : is_inner_product hom_inner.
Proof. exact: hom_inner_laws hom_innerP. Qed.

(** Source for [hom_innerE]: Federer 1.7.9, p. 35, the
    inner product on Hom makes its canonical tensor identification
    an isometry. *)
Theorem hom_innerE f g : hom_inner f g =
  tensor_inner (inner_dual_productP hB he) hC (@Gamma R V W (Finite.clone 'I_n _) e he f) (@Gamma R V W (Finite.clone 'I_n _) e he g).
Proof. exact (@hom_inner_tensor R V W B C hB hC n e he hom_inner hom_innerP f g). Qed.

(** Source for [hom_norm]: Federer 1.7.9, p. 35, final
    sentence: the length of a map abbreviates the length of its
    canonical tensor. This is distinct from the operator norm. *)
Definition hom_norm := inner_norm hom_inner_productP.

(** Source for [hom_norm_tensor]: Federer 1.7.9, p. 35,
    the norm of a map equals that of its tensor under Gamma. *)
Theorem hom_norm_tensor f : hom_norm f =
  tensor_norm (inner_dual_productP hB he) hC (@Gamma R V W (Finite.clone 'I_n _) e he f).
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
by rewrite inner_norm_sqr hom_innerE.
Qed.
End Interface.
