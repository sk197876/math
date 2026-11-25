(** Federer (1969), 1.7.9, p. 35: sealed Hom inner product. Only the product
    and its abstract characterising laws are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP Hom LinearBasis HomInnerUP HomInnerConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type HomInnerSig.
(** Source for [product]: Federer 1.7.9, p. 35,
    the characterised inner product on the space of linear maps. *)
Parameter product : forall (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e),
  Hom V W -> Hom V W -> R.
(** Source for [laws]: Federer 1.7.9, p. 35,
    the exported product satisfies the abstract specification. *)
Parameter laws : forall (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e),
  is_hom_inner_product hB hC he (@product R V W B C hB hC n e he).
End HomInnerSig.
Module HomInner : HomInnerSig.
(** Source for [product]: Federer 1.7.9, p. 35,
    select the proved existence witness inside the sealed module. *)
Definition product (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) :=
  sval (constructive_indefinite_description (hom_inner_exists hB hC he)).
(** Source for [laws]: Federer 1.7.9, p. 35,
    the selected witness obeys the characterising laws of the Hom inner product. *)
Lemma laws (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) :
  is_hom_inner_product hB hC he (@product R V W B C hB hC n e he).
Proof. exact: (svalP (constructive_indefinite_description (hom_inner_exists hB hC he))). Qed.
End HomInner.
