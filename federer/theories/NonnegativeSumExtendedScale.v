(** Federer (1969), 2.4.10, p. 85: multiplying the characteristic expansion
    of 2.3.3, p. 76, by a possibly infinite nonnegative density commutes
    with its nonnegative sum. This extends the finite scalar law of
    2.1.1(6), p. 52, by treating the infinite multiplier separately. Source
    editions: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_extended_scale]: supporting distribution of
    a nonnegative extended multiplier over the characteristic sum in Federer
    2.4.10, p. 85 *)
Lemma nonnegative_sum_extended_scale (R : realType) (J : choiceType)
    (D : set J) (u : J -> \bar R) c :
  0 <= c -> (forall j, D j -> 0 <= u j) ->
  nonnegative_sum D (fun j => c*u j)=c*nonnegative_sum D u.
Proof.
move=> hc hp; case ec: c hc=> [r| |] hc; last by [].
- exact: nonnegative_sum_scale hc hp.
- have [he|he] := pselect (exists j, D j /\ 0 < u j).
  + have [j [hj huj]] := he.
    have hsumpos : 0 < nonnegative_sum D u := lt_le_trans huj (nonnegative_sum_term u hj).
    have hterm : +oo*u j=+oo := gt0_mulye huj.
    have hsum : nonnegative_sum D (fun j => +oo*u j)=+oo.
      apply/eqP; rewrite -leye_eq -[X in X <= _]hterm; exact (@nonnegative_sum_term R J D (fun j => +oo*u j) j hj).
    by rewrite hsum (gt0_mulye hsumpos).
  + have hu0 j (hj : D j) : u j=0.
      apply/eqP; rewrite eq_le (hp j hj) andbT leNgt; apply/negP=> hpos.
      apply: he; exists j; by split.
    rewrite (nonnegative_sum_zero hu0) mule0; apply: nonnegative_sum_zero=> j hj.
    by rewrite (hu0 j hj) mule0.
Qed.
