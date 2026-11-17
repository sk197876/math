(** Federer (1969), 3.4.8(10), p. 331:
    saturating the equation ideal by the
    original nonzero coefficient stays inside
    the original prime quotient kernel.
    Apply its existing field embedding and
    cancellation to the exact power-membership law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealSaturationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_saturation_field_kernel]:
    the original equation ideal remains inside
    I_g after removing finite powers of
    delta outside I_g, supporting the
    original induction in 3.4.8(10), p. 331.
    A nonzero image in the existing
    fraction field supplies cancellation; no new
    localization or fraction construction is needed. *)
Theorem commutative_saturation_field_kernel (A:comNzRingType) (K:fieldType)
  (f:{rmorphism A->K}) (I S:set A) (delta:A):
  is_commutative_ideal_saturation I delta S ->
  (forall x:A,I x ->f x = 0) ->f delta!=0 ->
  forall x:A,S x ->f x = 0.
Proof.
move=>hS hKernel hDelta x /(hS x) [u hMember].
have hZero:=hKernel _ hMember.
rewrite rmorphM rmorphXn in hZero.
have hPower:(f delta)^+u!=0 by rewrite expf_neq0.
apply:(mulfI hPower);by rewrite mulr0.
Qed.
