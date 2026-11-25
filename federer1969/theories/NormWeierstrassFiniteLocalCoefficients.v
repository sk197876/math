(** Federer (1969), 3.4.12, p. 339: finite complex
    polynomial coefficients are determined by values on a short
    real interval. Apply the existing normed-target Taylor asymptotic
    coefficient uniqueness, retaining the same original complex target. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormLittleOPower PolynomialFiniteOrderComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_weierstrass_finite_local_coefficients]: local finite
    coefficient uniqueness in the complex extension of 3.4.6(2),
    p. 322, required by 3.4.12, p. 339. *)
Theorem norm_weierstrass_finite_local_coefficients (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) k (a b:nat->Y):
  (exists r:R,0<r /\forall t:R,`|t|<r ->
    (\sum_(i<k) t^+i*:a i)=\sum_(i<k) t^+i*:b i) ->
  forall i,(i<k)%N ->a i=b i.
Proof.
move=>[r [hr hEqual]] i hi.
pose F:=fun t:R=>\sum_(j<k) t^+j*:a j.
have hFirst:norm_little_o_power NY (fun t=>F t-\sum_(j<k) t^+j*:a j) k.
  move=>epsilon hEpsilon;exists 1;split;first exact:ltr01.
  move=>t ht;rewrite subrr (real_seminorm_zero hNY.1).
  exact:mulr_ge0 (ltW hEpsilon) (exprn_ge0 k (normr_ge0 t)).
have hSecond:norm_little_o_power NY (fun t=>F t-\sum_(j<k) t^+j*:b j) k.
  move=>epsilon hEpsilon;exists r;split;first exact:hr.
  move=>t /andP [ht0 ht];rewrite /F (hEqual t ht) subrr (real_seminorm_zero hNY.1).
  exact:mulr_ge0 (ltW hEpsilon) (exprn_ge0 k (normr_ge0 t)).
exact:(@finite_power_initial_asymptotic_coefficients_unique R Y NY hNY k k F a b hFirst hSecond
  i (ltnW hi) hi).
Qed.
