(** Finite coefficient padding for the section-polynomial
    comparison in Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_ascending_power_padding]: supporting
    comparison of the actual section and ambient Steiner
    coefficients in Federer 3.2.45, p. 279.
    The proved finite ordinal widening law pads the
    smaller ascending polynomial by zero coefficients.
    All boundary degrees, including zero, remain. *)
Lemma finite_ascending_power_padding (R : realType) q N (hQN : (q<=N)%N)
    (a : nat -> R) (r : R) :
  \sum_(j : 'I_q.+1) a j*r^+j=
    \sum_(j : 'I_N.+1) (if (j<=q)%N then a j else 0)*r^+j.
Proof.
have hQN1 : (q.+1<=N.+1)%N := hQN.
rewrite (big_ord_widen N.+1 (fun j => a j*r^+j) hQN1) big_mkcond.
apply: eq_bigr=> j _; rewrite ltnS.
by case: (j<=q)%N; rewrite ?mul0r.
Qed.
