(** Federer (1969), 4.1.9, p. 364: the exact
    middle coefficient is nonnegative and at most the
    maximum of the endpoint powers. This supporting
    finite-sum estimate includes both zero endpoints
    and degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ScalarAffinePowerMeanBounds.
Variable R:realType.
Variables a b:R.
Hypothesis ha:0<=a.
Hypothesis hb:0<=b.
Variable j:nat.

(** Source for [scalar_mixed_power_max_bound]: every original
    mixed term a^k b^(j-k) is bounded by max(a^j,b^j),
    supporting the last inequality in Federer 4.1.9, p. 364. *)
Lemma scalar_mixed_power_max_bound k:(k<=j)%N->
  a^+k*b^+(j-k)<=Num.max (a^+j) (b^+j).
Proof.
move=>hk;case:(leP a b)=>hOrder.
- apply:(le_trans (ler_wpM2r (exprn_ge0 (j-k)%N hb)
    (lerXn2r k ha hb hOrder))).
  rewrite -exprD (subnKC hk).
  by rewrite le_max lexx orbT.
- have hWeak:b<=a:=ltW hOrder.
  apply:(le_trans (ler_wpM2l (exprn_ge0 k ha)
    (lerXn2r (j-k)%N hb ha hWeak))).
  rewrite -exprD (subnKC hk).
  by rewrite le_max lexx.
Qed.

(** Source for [scalar_affine_power_mean_nonnegative]: the
    exact middle coefficient is nonnegative, supporting
    the extended mass integrals in Federer 4.1.9, p. 364. *)
Lemma scalar_affine_power_mean_nonnegative:
  0<=(\sum_(k<j.+1) a^+k*b^+(j-k))/j.+1%:R.
Proof.
apply:divr_ge0;last exact:natr_ge0.
apply:sumr_ge0=>k _;exact:mulr_ge0 (exprn_ge0 k ha) (exprn_ge0 (j-k)%N hb).
Qed.

(** Source for [scalar_affine_power_mean_max_bound]: the
    printed mean is at most max(a^j,b^j), Federer
    4.1.9, p. 364. No positive endpoint or
    positive degree is assumed. *)
Theorem scalar_affine_power_mean_max_bound:
  (\sum_(k<j.+1) a^+k*b^+(j-k))/j.+1%:R<=Num.max (a^+j) (b^+j).
Proof.
have hPositive:0<(j.+1%:R:R) by rewrite ltr0n.
rewrite ler_pdivrMr //.
have hSum:(\sum_(k<j.+1) a^+k*b^+(j-k))<=
    (\sum_(k<j.+1) Num.max (a^+j) (b^+j)).
  apply:ler_sum=>k _;apply:scalar_mixed_power_max_bound.
  by move:(ltn_ord k);rewrite ltnS.
have hEqual:(\sum_(k<j.+1) Num.max (a^+j) (b^+j))=
    Num.max (a^+j) (b^+j)*j.+1%:R.
  by rewrite sumr_const card_ord mulr_natr.
by rewrite hEqual in hSum.
Qed.
End ScalarAffinePowerMeanBounds.
