(** Federer (1969), 1.7.3, p. 29: public principal-axis theorem. Only the
    sealed specification is used in this interface. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP TensorUP LinearBasis
  PrincipalAxesUP PrincipalAxesSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Principal.
Variable R : realType.
Variable V : lmodType R.
Variable B S : V -> V -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hS : @bilinear R V V R^o S.
Hypothesis hs : forall x y, S x y = S y x.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.

(** Source for [principal_axes_family]: Federer 1.7.3,
    p. 29, a principal-axis family selected through the sealed laws. *)
Definition principal_axes_family := @PrincipalAxes.family R V B S hB hS hs n b hb.

(** Source for [principal_axesP]: Federer 1.7.3, p. 29,
    the chosen family is an orthonormal basis with decreasing
    diagonal values and zero off-diagonal values. *)
Theorem principal_axesP : is_principal_axes B S principal_axes_family.
Proof. exact: PrincipalAxes.laws. Qed.

(** Source for [principal_axes_exists]: Federer 1.7.3,
    p. 29, the full principal-axis existence theorem. Dimension zero
    is included. The bilinear form S need not be positive definite. *)
Theorem principal_axes_exists : exists e : 'I_n -> V, is_principal_axes B S e.
Proof. exists principal_axes_family; exact: principal_axesP. Qed.
End Principal.
