(** Federer (1969), 2.6.5, p. 120, the dimension induction: the slices whose
    coefficients all vanish lie in the zero set of any fixed nonzero
    coefficient polynomial. This file isolates that exceptional-set
    argument. Taylor coefficients are supplied by 1.10.4, p. 46 *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PolynomialCoefficientUniqueness MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coefficient_polynomial_all_zero]: elementary
    supporting zero-coefficient case in the univariate step
    of Federer 2.6.5, p. 120, using the finite polynomial
    expansion of 1.10.4, p. 46. *)
Lemma coefficient_polynomial_all_zero (K : fieldType) (W : lmodType K)
    (s : seq W) t : all (pred1 0) s -> coefficient_polynomial_value s t = 0.
Proof.
elim: s=> [|c s ih] //= /andP[/eqP hc hs].
change (c+t *: coefficient_polynomial_value s t = 0).
by rewrite hc (ih hs) scaler0 addr0.
Qed.

(** Source for [polynomial_coefficients_almost_nonzero]:
    exceptional slices in the induction of Federer 2.6.5,
    p. 120. If one coefficient has a null zero set,
    almost every coefficient list is nonzero. Neither the
    coefficient functions nor their individual zero sets
    need an additional measurability hypothesis. *)
Lemma polynomial_coefficients_almost_nonzero (R : realType) (X : choiceType)
    (W : lmodType R) (mu : set X -> \bar R) (hm : is_measure mu)
    N (c : nat -> X -> W) i :
  (i < N)%N -> mu [set x | c i x = 0] = 0%:E ->
  measure_almost_everywhere mu
    [set x | ~~ all (pred1 0) [seq c j x | j <- iota 0 N]].
Proof.
move=> hi hz; apply: (@measure_null_subset R X mu hm _ _ _ hz)=> x hx.
have ha : all (pred1 0) [seq c j x | j <- iota 0 N].
  case h: (all (pred1 0) [seq c j x | j <- iota 0 N])=> //.
  exfalso; apply: hx.
  change (~~ all (pred1 0) [seq c j x | j <- iota 0 N]); by rewrite h.
apply/eqP; apply: (allP ha).
apply/mapP; exists i=> //; by rewrite mem_iota add0n leq0n hi.
Qed.
