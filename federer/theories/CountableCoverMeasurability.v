(** Measurability criterion for the fixed-family construction of Federer
    (1969), 2.10.1, p. 170, supporting the concrete example for 2.3.8, p.
    78. A set is measurable if splitting each generator across that set
    costs no more than the assigned generator cost. This follows from the
    Caratheodory definition in 2.1.2, p. 54, and the covering-infimum laws;
    it is local supporting infrastructure. Source context:
    CountableCoverEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumAdd CountableCoverEnvelopeUP
  CountableCoverEnvelopeLaws MeasureUP MeasureSplit MeasureIndexedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_cover_generator_split_measurable]:
    supporting generator-splitting criterion derived from Federer
    2.1.2, p. 54, and 2.10.1, p. 170.
    This will prove the binary cylinders measurable in the local
    counterexample to 2.3.8, p. 78. *)
Theorem countable_cover_generator_split_measurable (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (nu : set X -> \bar R)
    (hn : is_countable_cover_envelope S cost nu)
    (hcost : forall j, 0 <= cost j) (A : set X) :
  (forall j, nu (S j `&` A) + nu (S j `\` A) <= cost j) ->
  measure_measurable nu A.
Proof.
move=> hsplit; have hm := @countable_cover_envelope_is_measure R X J S cost nu hn hcost.
move=> T; apply/eqP; rewrite eq_le (measure_split_upper hm) /=.
apply: (countable_cover_envelope_greatest hn)=> G hG hcov.
have hi : nu (T `&` A) <= nonnegative_sum G (fun j => nu (S j `&` A)).
  apply: (@measure_indexed_cover R X J nu hm _ G (fun j => S j `&` A) hG).
  move=> x [hx ha]; have [j hj hxj] := hcov x hx; exists j=> //; by split.
have hd : nu (T `\` A) <= nonnegative_sum G (fun j => nu (S j `\` A)).
  apply: (@measure_indexed_cover R X J nu hm _ G (fun j => S j `\` A) hG).
  move=> x [hx ha]; have [j hj hxj] := hcov x hx; exists j=> //; by split.
apply: le_trans (leeD hi hd) _.
have hni j (hj : G j) := @measure_nonnegative R X nu hm (S j `&` A).
have hnd j (hj : G j) := @measure_nonnegative R X nu hm (S j `\` A).
rewrite -(@nonnegative_sum_add R J G (fun j => nu (S j `&` A)) (fun j => nu (S j `\` A)) hni hnd).
apply: nonnegative_sum_mono=> j _; exact: hsplit.
Qed.
