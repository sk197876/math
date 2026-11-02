(** Federer (1969), 1.7.3, p. 29: supporting consequences of the
    principal-axis specification. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import PrincipalAxesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [principal_axes_distinct]: Federer 1.7.3,
    p. 29, supporting extension of the displayed i<j vanishing
    to every pair of distinct indices, by symmetry of S. *)
Lemma principal_axes_distinct (R : realFieldType) (V : lmodType R)
    (B S : V -> V -> R) (hs : forall x y, S x y = S y x)
    n (e : 'I_n -> V) (he : is_principal_axes B S e) (i j : 'I_n) :
    i != j -> S (e i) (e j) = 0.
Proof.
move=> hne; case: (ltngtP i j) => hij.
- exact (@principal_axes_off_diagonal R V B S n e he i j hij).
- rewrite hs; exact (@principal_axes_off_diagonal R V B S n e he j i hij).
- have heq : i = j := val_inj hij.
  by move: hne; rewrite heq eqxx.
Qed.
