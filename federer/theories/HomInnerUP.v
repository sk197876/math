(** Federer (1969), 1.7.9, p. 35: the inner product on Hom(V,W) is specified
    by making the canonical tensor identification Gamma an isometry. Only
    the source space is finite dimensional. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerDual TensorInner Hom Gamma
  LinearBasis TensorProduct AlternatingCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Specification.
Variable R : rcfType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [is_hom_inner_product]: Federer 1.7.9, p. 35,
    final sentence and preceding tensor identification: the product of
    maps is the tensor inner product of their canonical images. This
    record specifies the laws independently of a witness. *)
Record is_hom_inner_product (D : Hom V W -> Hom V W -> R) : Prop := {
  hom_inner_laws : is_inner_product D;
  hom_inner_tensor : forall f g,
    D f g = tensor_inner (inner_dual_productP hB he) hC
      (@Gamma R V W (Finite.clone 'I_n _) e he f) (@Gamma R V W (Finite.clone 'I_n _) e he g)
}.

(** Source for [hom_inner_unique]: Federer 1.7.9, p. 35,
    supporting uniqueness of the inner product specified through Gamma. *)
Theorem hom_inner_unique (D E : Hom V W -> Hom V W -> R) :
  is_hom_inner_product D -> is_hom_inner_product E -> forall f g, D f g = E f g.
Proof. move=> hD hE f g; by rewrite (hom_inner_tensor hD) (hom_inner_tensor hE). Qed.
End Specification.
