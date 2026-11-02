(** Federer (1969), 1.7.3, p. 29: sealed principal-axis witness. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp reals.
From Federer Require Import InnerProductUP TensorUP LinearBasis
  PrincipalAxesUP PrincipalAxesConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type PrincipalAxesSig.
(** Source for [family]: Federer 1.7.3, p. 29, a principal-axis
    basis specified by its ordered orthonormal diagonalisation laws. *)
Parameter family : forall (R : realType) (V : lmodType R)
  (B S : V -> V -> R), is_inner_product B -> @bilinear R V V R^o S ->
  (forall x y, S x y = S y x) ->
  forall n (b : 'I_n -> V), is_basis b -> 'I_n -> V.
(** Source for [laws]: Federer 1.7.3, p. 29, the abstract
    principal-axis specification satisfied by the hidden witness. *)
Parameter laws : forall (R : realType) (V : lmodType R)
  (B S : V -> V -> R) (hB : is_inner_product B) (hS : @bilinear R V V R^o S)
  (hs : forall x y, S x y = S y x) n (b : 'I_n -> V) (hb : is_basis b),
  is_principal_axes B S (@family R V B S hB hS hs n b hb).
End PrincipalAxesSig.

Module PrincipalAxes : PrincipalAxesSig.
(** Source for [family]: Federer 1.7.3, p. 29, choose the
    witness whose existence is proved by successive maximisation. *)
Definition family (R : realType) (V : lmodType R)
  (B S : V -> V -> R) (hB : is_inner_product B) (hS : @bilinear R V V R^o S)
  (hs : forall x y, S x y = S y x) n (b : 'I_n -> V) (hb : is_basis b) :=
  sval (constructive_indefinite_description
    (@principal_axes_witness R V B S hB hS n b hb hs)).
(** Source for [laws]: Federer 1.7.3, p. 29, verification that
    the chosen witness satisfies the principal-axis specification. *)
Lemma laws (R : realType) (V : lmodType R)
  (B S : V -> V -> R) (hB : is_inner_product B) (hS : @bilinear R V V R^o S)
  (hs : forall x y, S x y = S y x) n (b : 'I_n -> V) (hb : is_basis b) :
  is_principal_axes B S (@family R V B S hB hS hs n b hb).
Proof. exact: (svalP (constructive_indefinite_description
  (@principal_axes_witness R V B S hB hS n b hb hs))). Qed.
End PrincipalAxes.
