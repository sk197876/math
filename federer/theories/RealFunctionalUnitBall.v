(** Federer (1969), 2.4.12, p. 87: the dual norm is sup {alpha(y) : |y| <=
    1}. The unsigned least-bound specification is equivalent to precisely
    this signed unit-ball formula. Source context and expanded context:
    RealFunctionalNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP RealFunctionalNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_functional_unit_ball_bound]: supporting
    normalisation for the exact supremum in Federer 2.4.12, p. 87. *)
Lemma real_functional_unit_ball_bound (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (a : {linear V -> R^o}) C :
  (forall y, N y <= 1 -> a y <= C) ->
  0 <= C /\ forall y, `|a y| <= C*N y.
Proof.
move=> hb; have hC : 0 <= C.
  have hh := hb 0; rewrite linear0 (real_seminorm_zero hN.1) in hh.
  exact: hh ler01.
have hu y : N y <= 1 -> `|a y| <= C.
  move=> hy; rewrite ler_norml; apply/andP; split; last exact: hb hy.
  have hh := hb (-y); rewrite (real_seminorm_negate hN.1) linearN in hh.
  by rewrite lerNl; exact: hh hy.
split=> // y; have [->|hy] := eqVneq y 0.
- by rewrite linear0 normr0 (real_seminorm_zero hN.1) mulr0.
have hp : 0 < N y by rewrite (real_norm_positive hN.1 hN.2).
have hn : N ((N y)^-1 *: y) <= 1.
  by rewrite (real_seminorm_scale hN.1) normfV (ger0_norm (ltW hp)) mulVf ?gt_eqF.
have hh := hu _ hn.
rewrite linearZ /= normrM normfV (ger0_norm (ltW hp)) mulrC in hh.
by rewrite ler_pdivrMr // in hh.
Qed.

(** Source for [real_functional_norm_unit_ball_lub]: direct
    least-upper-bound form of Federer's signed unit-ball supremum,
    2.4.12, p. 87. No attainment or finite dimension is assumed. *)
Theorem real_functional_norm_unit_ball_lub (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (a : {linear V -> R^o}) n :
  is_real_functional_norm N a n ->
  (forall y, N y <= 1 -> a y <= n) /\
  (forall C, (forall y, N y <= 1 -> a y <= C) -> n <= C).
Proof.
move=> hn; split.
- move=> y hy; apply: le_trans (ler_norm _) _.
  apply: le_trans (real_functional_norm_bound hn y) _.
  have hh := ler_wpM2l (real_functional_norm_nonnegative hn) hy.
  by rewrite mulr1 in hh.
- move=> C hC; have [hpos hb] := real_functional_unit_ball_bound hN hC.
  exact: (real_functional_norm_least hn hpos hb).
Qed.
