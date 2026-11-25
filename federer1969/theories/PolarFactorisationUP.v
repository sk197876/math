(** Federer (1969), 1.7.3, p. 30: the two orthogonal factorisations of a
    linear map. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricEndomorphisms OrthogonalMaps AdjointUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_injection_factorisation]: Federer 1.7.3,
    p. 30, g is symmetric, h is an orthogonal injection, and
    h composed with g equals the prescribed linear map. *)
Record is_injection_factorisation (R : fieldType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R) (f : {linear V -> U})
    (g : {linear V -> V}) (h : {linear V -> U}) : Prop := {
  injection_factor_symmetric : is_symmetric_endomorphism B g;
  injection_factor_orthogonal : is_orthogonal_map B C h;
  injection_factor_equation : forall x, h (g x) = f x
}.

(** Source for [is_projection_factorisation]: Federer 1.7.3,
    p. 30, k is symmetric, p is an orthogonal projection, and
    k composed with p equals the prescribed linear map. *)
Record is_projection_factorisation (R : fieldType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R) (f : {linear V -> U})
    (k : {linear U -> U}) (p : {linear V -> U}) : Prop := {
  projection_factor_symmetric : is_symmetric_endomorphism C k;
  projection_factor_orthogonal : is_orthogonal_projection B C p;
  projection_factor_equation : forall x, k (p x) = f x
}.
