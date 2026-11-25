(** Federer (1969), 3.3.20, p. 307: exact finite uniform cover-cost budget. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal.
From Federer Require Import NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_constant_nonnegative_sum]: supporting exact
    cardinal budget for the original square covers in 3.3.20, p. 307.
    Every actual original index is retained, including repeated images;
    a finite family of equal nonnegative costs sums to its cardinal
    times that cost. *)
Lemma finite_constant_nonnegative_sum (R:realType) (I:choiceType) (F:{fset I}) (w:R):
  0<=w ->nonnegative_sum [set` F] (fun _=>w%:E)=(#|` F|%:R * w)%:E.
Proof.
move=>hw;rewrite nonnegative_sum_finite;last by move=>i _;rewrite lee_fin.
by rewrite sumEFin big_seq_fsetE sumr_const cardT cardfE mulr_natl cardE.
Qed.
