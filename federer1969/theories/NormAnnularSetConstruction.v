(** Private set witness for Federer (1969),
    3.2.16, p. 253. Only its sealing
    module and the assumptions audit may import it. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import NormAnnularSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_annular_set_exists]: existence
    of T in Federer 3.2.16, p. 253,
    proved by the indicated annular union. *)
Lemma norm_annular_set_exists (R : realType) (X : lmodType R)
    (NX : X -> R) (S : nat -> set X) (a : X) (rho : nat -> R) :
  exists T, is_norm_annular_set NX S a rho T.
Proof.
exists [set x | exists n, S n x /\ NX (x-a)<=rho n /\ rho n.+1<NX (x-a)].
by move=> x.
Qed.
