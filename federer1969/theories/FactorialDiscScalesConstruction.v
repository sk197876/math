(** Federer (1969), 3.3.19, p. 302: private recursive
    existence witness for the independent scale laws.
    Downstream proofs use only the sealed specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import FactorialDiscScalesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [factorial_disc_recursive_count]: private
    count recursion witnessing 3.3.19, p. 302. *)
Fixpoint factorial_disc_recursive_count (j:nat):nat:=
  if j is k.+1 then ((k+4)*factorial_disc_recursive_count k)%N else 1%N.

(** Source for [factorial_disc_recursive_radius]: private
    radius recursion witnessing 3.3.19, p. 302. *)
Fixpoint factorial_disc_recursive_radius (R:realType) (j:nat):R:=
  if j is k.+1 then factorial_disc_recursive_radius R k/(k+4)%:R else 1.

(** Source for [factorial_disc_scales_exists]: existence of
    the printed count and radius recursions in 3.3.19,
    p. 302, before choosing public objects. *)
Theorem factorial_disc_scales_exists (R:realType):
  exists N:nat->nat,exists rho:nat->R,is_factorial_disc_scales N rho.
Proof.
exists factorial_disc_recursive_count,(@factorial_disc_recursive_radius R).
by constructor.
Qed.
