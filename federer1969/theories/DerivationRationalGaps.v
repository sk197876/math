(** The countable rational gaps in Federer (1969), 2.9.5, p. 154.
    Nonnegative lower limits permit restricting to 0<a<b. Two applications
    of rational order density find a positive rational gap between distinct
    ordered limits, including infinite endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_rational_gaps]: supporting countable indexing of
    R(a,b) in Federer 2.9.5, p. 154 *)
Definition positive_rational_gaps (R : realType) :=
  [set p : rat*rat | (0<(ratr p.1 : R))%R /\ ((ratr p.1 : R)<ratr p.2)%R].

(** Source for [positive_rational_gap_between]: supporting
    rational-density step behind the union of exceptional
    sets R(a,b) in Federer 2.9.5, p. 154.
    The nonnegative lower endpoint makes the chosen rational
    indices positive, so only the bounds proved by 2.9.4
    at positive coefficients are needed. *)
Lemma positive_rational_gap_between (R : realType) (l u : \bar R) :
  0<=l -> l<u -> exists p : rat*rat, positive_rational_gaps R p /\
    l<(ratr p.1 : R)%:E /\ (ratr p.2 : R)%:E<u.
Proof.
move=> hl hlu.
have [a [hla hau]] := @extended_rationals_order_dense R l u hlu.
have [b [hab hbu]] := @extended_rationals_order_dense R (ratr a : R)%:E u hau.
have ha0 : (0<(ratr a : R))%R.
  have h := le_lt_trans hl hla; by rewrite lte_fin in h.
have habR : ((ratr a : R)<ratr b)%R by move: hab; rewrite lte_fin.
exists (a,b); split; first by split.
by split.
Qed.
