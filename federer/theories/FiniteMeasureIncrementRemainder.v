(** Federer (1969), 3.2.42, printed p. 278:
    subtract the finite original-source volume from the
    Brunn--Minkowski increment through Caratheodory splitting.
    The containing set's volume may be infinite. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_measure_increment_remainder]: supporting
    finite cancellation in both proof displays of Federer
    3.2.42, p. 278. Only the measurable inner piece has
    finite prescribed volume. No measurability or finite
    volume of the outer set or difference is assumed. *)
Lemma finite_measure_increment_remainder (R:realType) (X:choiceType)
    (mu:set X -> \bar R) (A U:set X) (a c:R):
  measure_measurable mu A ->A `<=` U ->mu A=a%:E ->
  ((a+c)%:E<=mu U)%E ->(c%:E<=mu (U `\` A))%E.
Proof.
move=>hA hAU hMass hBound.
have hIntersection:U `&` A=A.
  apply/seteqP; split=>[x [_ hx]//|x hx]; split=>//; exact:hAU x hx.
have hSplit:=hA U; rewrite hIntersection hMass in hSplit.
by rewrite EFinD hSplit leeD2lE in hBound.
Qed.
