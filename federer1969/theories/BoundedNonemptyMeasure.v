(** Federer (1969), 2.1.5, p. 57: verification principle for the three
    printed irregular measures, all of which lie between one and two on
    nonempty sets. The other two are checked directly against Federer. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum TwoTermSumBound MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_nonempty_is_measure]: Federer 2.1.5,
    p. 57, supporting lemma for the counterexamples: a monotone
    set function vanishing at the empty set and taking values between
    one and two on nonempty sets satisfies the covering law. A cover
    either has two distinct nonempty members, or one member covers A.
    This general verification principle is not separately stated in Federer. *)
Lemma bounded_nonempty_is_measure (R : realType) (I : choiceType)
    (mu : set I -> \bar R) : mu set0 = 0 ->
  (forall A B, A `<=` B -> mu A <= mu B) ->
  (forall A, A != set0 -> (1 : R)%:E <= mu A) ->
  (forall A, mu A <= (2 : R)%:E) -> is_measure mu.
Proof.
move=> h0 hmono hlo hhi; constructor.
- move=> A; rewrite -h0; apply: hmono=> x [].
- move=> A F _ hc; have [he|he] := eqVneq A set0.
  + rewrite he h0; exact: nonnegative_sum_nonnegative.
  + have [x hx] := proj1 (set0P A) he.
    have [B hB hxB] := hc x hx.
    have hB0 : B != set0 by apply/eqP=> h; rewrite h in hxB.
    case: (pselect (exists C, F C /\ C != B /\ C != set0))=> [[C [hC [hCB hC0]]]|hno].
    * apply: le_trans (hhi A) _.
      have hsum := @nonnegative_sum_two_term_bound R _ F mu C B hC hB hCB.
      apply: le_trans (_ : (2 : R)%:E <= mu C + mu B) hsum.
      change ((1 : R)%:E + (1 : R)%:E <= mu C + mu B).
      exact: leeD (hlo C hC0) (hlo B hB0).
    * have hAB : A `<=` B.
        move=> y hy; have [C hC hyC] := hc y hy.
        have [hCB|hCB] := eqVneq C B; first by rewrite -hCB.
        exfalso; apply: hno; exists C; split=> //; split=> //.
        by apply/eqP=> h; rewrite h in hyC.
      exact: le_trans (hmono A B hAB) (@nonnegative_sum_term R _ F mu B hB).
Qed.
