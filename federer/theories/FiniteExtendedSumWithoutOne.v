(** Federer (1969), 3.2.39, p. 276: isolate
    the first layer in a finite sum without losing any
    of the remaining original indices. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ereal_scope.

(** Source for [finite_extended_sum_without_one]: the
    distinguished S_1 term in the mixed upper/lower comparison
    of Federer 3.2.39, p. 276. Replacing only that
    index by zero gives the exact remaining sum, including
    a one-element family and infinite extended values. *)
Lemma finite_extended_sum_without_one (R:realType) (I:finType) (i0:I) (a:I->\bar R):
  (\sum_i a i)=a i0+(\sum_i if i==i0 then 0 else a i).
Proof.
have hRest:(\sum_i if i==i0 then 0 else a i)=\sum_(i:I|i!=i0) a i.
  rewrite (bigD1 i0) // eqxx.
  change ((0+\sum_(i:I|i!=i0) if i==i0 then 0 else a i)=\sum_(i:I|i!=i0) a i)%E.
  rewrite add0e; apply:eq_bigr=>i hi; by rewrite (negbTE hi).
by rewrite hRest (bigD1 i0).
Qed.
