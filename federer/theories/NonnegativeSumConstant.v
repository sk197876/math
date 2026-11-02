(** Federer (1969), 2.1.1(3), p. 52: constant nonnegative summands on
    infinite sets. Supporting example for 2.1.2's counting measure, pp.
    53-54. Source context: NonnegativeSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumCountable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_infinite_constant]: Federer
    2.1.1(3), p. 52, supporting consequence: a positive constant
    summed over an infinite set has value positive infinity. *)
Lemma nonnegative_sum_infinite_constant (R : realType) (I : choiceType)
    (A : set I) (c : R) : (0 < c)%R -> infinite_set A ->
  nonnegative_sum A (fun _ => c%:E) = +oo.
Proof.
move=> hc hA; have [he|he] := eqVneq (nonnegative_sum A (fun _ => c%:E)) +oo; first exact he.
exfalso; have hlt : nonnegative_sum A (fun _ => c%:E) < +oo by rewrite ltey.
have hf := @nonnegative_sum_threshold_finite R I A (fun _ => c%:E) c hc hlt.
apply: hA; have hs : (A `&` [set _ : I | c%:E <= c%:E]) = A.
  apply/seteqP; split=> [x [hx _]|x hx] //; split=> //; exact: lexx.
by rewrite hs in hf.
Qed.
