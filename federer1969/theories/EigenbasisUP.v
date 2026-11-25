(** Federer (1969), 1.7.3, p. 29: specification of an orthonormal
    eigenbasis. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import OrthonormalFamilies LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_orthonormal_eigenbasis]: Federer 1.7.3,
    p. 29, an orthonormal basis e_i with f(e_i)=lambda_i e_i
    and real eigenvalues, as obtained for symmetric endomorphisms. *)
Record is_orthonormal_eigenbasis (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (f : {linear V -> V}) n
    (e : 'I_n -> V) (lambda : 'I_n -> R) : Prop := {
  eigenbasis_basis : is_basis e;
  eigenbasis_orthonormal : orthonormal_family B e;
  eigenbasis_eigenvalue : forall i, f (e i) = lambda i *: e i
}.
