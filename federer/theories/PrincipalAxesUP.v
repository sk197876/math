(** Federer (1969), 1.7.3, p. 29: specification of a principal-axis basis
    for a symmetric bilinear form. Existence is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import OrthonormalFamilies LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_principal_axes]: Federer 1.7.3, p. 29,
    first displayed assertion: an orthonormal basis with decreasing
    diagonal values and zero off-diagonal values for i<j. *)
Record is_principal_axes (R : realFieldType) (V : lmodType R)
    (B S : V -> V -> R) n (e : 'I_n -> V) : Prop := {
  principal_axes_basis : is_basis e;
  principal_axes_orthonormal : orthonormal_family B e;
  principal_axes_ordered : forall i j : 'I_n, (i < j)%N -> S (e j) (e j) <= S (e i) (e i);
  principal_axes_off_diagonal : forall i j : 'I_n, (i < j)%N -> S (e i) (e j) = 0
}.
