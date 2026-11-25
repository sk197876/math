(** Federer (1969), 1.7.2, p. 28: sealed dual inner product. Source
    editions: InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP LinearBasis AlternatingCoordinates.
From Federer Require Import InnerDualUP InnerDualConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type InnerDualSig.
(** Source for [product]: Federer 1.7.2, p. 28, the inner product
    on the one-covectors, specified by its laws below. *)
Parameter product : forall (R : rcfType) (V : lmodType R)
  (B : V -> V -> R), is_inner_product B ->
  forall n (e : 'I_n -> V), is_basis e -> A_m V R^o 1 -> A_m V R^o 1 -> R.
(** Source for [laws]: Federer 1.7.2, p. 28, the abstract dual
    inner-product specification, fulfilled by the existence witness. *)
Parameter laws : forall (R : rcfType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  n (e : 'I_n -> V) (he : is_basis e),
  is_dual_inner_product hB (@product R V B hB n e he).
End InnerDualSig.

Module InnerDual : InnerDualSig.
(** Source for [product]: Federer 1.7.2, p. 28, existence witness
    hidden by opaque ascription; downstream use is through the laws. *)
Definition product := @dual_inner_product_witness.
(** Source for [laws]: Federer 1.7.2, p. 28, verification of the
    witness against the abstract dual inner-product specification. *)
Lemma laws (R : rcfType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  n (e : 'I_n -> V) (he : is_basis e) :
  is_dual_inner_product hB (@product R V B hB n e he).
Proof. exact: dual_inner_product_witnessP. Qed.
End InnerDual.
