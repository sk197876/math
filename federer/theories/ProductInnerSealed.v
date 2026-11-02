(** Federer (1969), 1.7.11, p. 36: sealed inner product on the Cartesian
    product of two inner-product spaces. The interface exposes only its
    defining pair formula and the inner-product laws. Source context and
    ingredients: ProductInnerUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP ProductInnerUP ProductInnerConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ProductInnerSig.
(** Source for [product]: Federer 1.7.11, p. 36,
    the characterised inner product on the Cartesian product. *)
Parameter product : forall (R : realFieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C),
  (V * W)%type -> (V * W)%type -> R.
(** Source for [laws]: Federer 1.7.11, p. 36,
    the exported product satisfies the abstract specification. *)
Parameter laws : forall (R : realFieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C),
  is_product_inner_product B C (@product R V W B C hB hC).
End ProductInnerSig.
Module ProductInner : ProductInnerSig.
(** Source for [product]: Federer 1.7.11, p. 36,
    select the proved existence witness inside the sealed module. *)
Definition product (R : realFieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C) :=
  sval (constructive_indefinite_description (product_inner_exists hB hC)).
(** Source for [laws]: Federer 1.7.11, p. 36,
    the selected witness obeys the characterising product-metric laws. *)
Lemma laws (R : realFieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C) :
  is_product_inner_product B C (@product R V W B C hB hC).
Proof. exact: (svalP (constructive_indefinite_description (product_inner_exists hB hC))). Qed.
End ProductInner.
