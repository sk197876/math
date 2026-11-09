(** Federer (1969), 3.4.6(2), p. 322: a
    finite polynomial known on a neighbourhood determines
    all its coefficients uniquely. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormLittleOPower PolynomialFiniteOrderComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_finite_local_coefficients]:
    local equality of the original finite transverse
    polynomials identifies every coefficient, supporting
    uniqueness in 3.4.6(2), p. 322. Actual
    Taylor asymptotic uniqueness proves this finite claim. *)
Theorem weierstrass_finite_local_coefficients (R:realType) k (a b:nat->R):
  (exists r:R,0<r /\forall t,`|t|<r ->
    (\sum_(i<k) t^+i*a i)=\sum_(i<k) t^+i*b i) ->
  forall i,(i<k)%N ->a i=b i.
Proof.
move=>[r [hr hEqual]] i hi.
pose N:=fun t:R^o=>`|t|.
pose F:=fun t=>\sum_(i<k) t^+i*a i.
have hFirst:norm_little_o_power N (fun t=>F t-\sum_(i<k) t^+i*:(a i:R^o)) k.
  move=>epsilon hEpsilon;exists 1;split;first exact:ltr01.
  move=>t ht;change (is_true (`|F t-F t|<=epsilon*`|t|^+k)).
  rewrite subrr normr0;exact:mulr_ge0 (ltW hEpsilon) (exprn_ge0 k (normr_ge0 t)).
have hSecond:norm_little_o_power N (fun t=>F t-\sum_(i<k) t^+i*:(b i:R^o)) k.
  move=>epsilon hEpsilon;exists r;split;first exact:hr.
  move=>t /andP [ht0 ht].
  change (is_true (`|F t-\sum_(i<k) t^+i*b i|<=epsilon*`|t|^+k)).
  rewrite /F (hEqual t ht) subrr normr0.
  exact:mulr_ge0 (ltW hEpsilon) (exprn_ge0 k (normr_ge0 t)).
exact:(@finite_power_initial_asymptotic_coefficients_unique R R^o N (@scalar_absolute_value_norm R)
  k k F a b hFirst hSecond i (ltnW hi) hi).
Qed.
