(** Federer (1969), 1.7.3, p. 30, final factorisation, referring forward to
    the adjoint definition in 1.7.4, p. 30. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_adjoint]: Federer 1.7.4, p. 30, the
    equivalent defining equation x.f*(y)=f(x).y. This abstract
    condition is also needed for the final factorisation in 1.7.3. *)
Definition is_adjoint (R : fieldType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (f : {linear V -> U}) (g : {linear U -> V}) :=
  forall x y, B x (g y) = C (f x) y.

(** Source for [is_orthogonal_projection]: Federer 1.7.4, p. 30, an
    orthogonal projection is an adjoint of an orthogonal injection. This
    characterisation states the exact meaning used in the final
    factorisation of 1.7.3, including different source and target spaces. *)
Definition is_orthogonal_projection (R : fieldType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R) (p : {linear V -> U}) :=
  exists h : {linear U -> V},
    (forall x y, B (h x) (h y) = C x y) /\ is_adjoint C B h p.
