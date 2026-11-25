(** Federer (1969), 3.2.41, printed p. 277, first proof display:
    the product-root comparison follows from 2.4.13, p. 88.
    This supporting finite arithmetic--geometric mean inequality is
    proved by induction from the project's actual two-weight theorem,
    with zero entries retained. No external mean inequality is imported. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealPower WeightedArithmeticGeometricMean.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_arithmetic_geometric_mean_successor]: supporting
    product-root comparison in Federer 3.2.41, p. 277, by the
    arithmetic--geometric mean of 2.4.13, p. 88. The finite family
    has n+1 nonnegative entries, so its root exponent is positive. *)
Theorem finite_arithmetic_geometric_mean_successor (R : realType) n
    (u : 'I_n.+1 -> R) :
  (forall i, 0<=u i) ->
  real_power (\prod_i u i) (n.+1%:R)^-1 <= (\sum_i u i)/n.+1%:R.
Proof.
elim: n u=> [|n ih] u hu.
- rewrite !big_ord1 invr1 mulr1.
  by rewrite real_power_one_exponent.
pose v (i : 'I_n.+1) : R := u (widen_ord (leqnSn n.+1) i).
pose x : R := u ord_max.
pose p : R := n.+1%:R.
pose q : R := n.+2%:R.
pose P : R := \prod_i v i.
pose S : R := \sum_i v i.
have hp : 0<p by rewrite /p ltr0n.
have hq : 0<q by rewrite /q ltr0n.
have hp0 : p!=0 by rewrite gt_eqF.
have hq0 : q!=0 by rewrite gt_eqF.
have hQP : q=p+1 by rewrite /q /p -addn1 natrD.
have hP : 0<=P by apply: prodr_ge0=> i _; exact: hu.
have hx : 0<=x := hu ord_max.
have hOld : real_power P p^-1<=S/p := ih v (fun i => hu (widen_ord (leqnSn n.+1) i)).
have ha : 0<p/q by rewrite divr_gt0.
have hb : 0<q^-1 by rewrite invr_gt0.
have hWeights : p/q+q^-1=(1:R).
  rewrite hQP; field; by rewrite gt_eqF //; lra.
have hMean := @weighted_arithmetic_geometric_mean R (p/q) q^-1
  (real_power P p^-1) x ha hb hWeights (real_power_nonnegative P p^-1) hx.
have hpi : 0<p^-1 by rewrite invr_gt0.
have hExponent : p^-1*(p/q)=q^-1.
  by rewrite mulrA mulVf // mul1r.
have hPower : real_power (P*x) q^-1=
    real_power (real_power P p^-1) (p/q)*real_power x q^-1.
  rewrite (@real_power_positive_iterate R P p^-1 (p/q) hP hpi ha) hExponent.
  exact: real_power_product hP hx.
have hScale := ler_wpM2l (ltW ha) hOld.
have hBound := le_trans hMean (lerD hScale (lexx (q^-1*x))).
have hRight : (p/q)*(S/p)+q^-1*x=(S+x)/q.
  by rewrite [p/q*(S/p)]mulrC mulrA divfK // [q^-1*x]mulrC -mulrDl.
rewrite hRight -hPower in hBound.
have hProduct : (\prod_(i<n.+2) u i) = P*x by rewrite big_ord_recr.
have hSum : (\sum_(i<n.+2) u i) = S+x by rewrite big_ord_recr.
by rewrite hProduct hSum; exact hBound.
Qed.

(** Source for [finite_arithmetic_geometric_mean]: supporting
    finite n-dimensional form of the arithmetic--geometric mean
    used in Federer 3.2.41, p. 277. Positive n is explicit;
    a zero-dimensional product has no corresponding positive root. *)
Theorem finite_arithmetic_geometric_mean (R : realType) n (u : 'I_n -> R) :
  (0<n)%N -> (forall i, 0<=u i) ->
  real_power (\prod_i u i) (n%:R)^-1 <= (\sum_i u i)/n%:R.
Proof.
case: n u=> [|n] u hn hu; first by rewrite ltn0 in hn.
exact: finite_arithmetic_geometric_mean_successor hu.
Qed.

(** Source for [complementary_product_root_bound]: supporting
    exact first proof display in Federer 3.2.41, p. 277:
    if u_i+v_i=1, the two product roots sum to at most one.
    Zero coordinates are retained; no positivity or finiteness
    premise on an eventual measure is hidden in this scalar lemma. *)
Theorem complementary_product_root_bound (R : realType) n
    (u v : 'I_n -> R) :
  (0<n)%N -> (forall i, 0<=u i) -> (forall i, 0<=v i) ->
  (forall i, u i+v i=(1:R)) ->
  real_power (\prod_i u i) (n%:R)^-1+
    real_power (\prod_i v i) (n%:R)^-1<=1.
Proof.
move=> hn hu hv hSum.
have hU := finite_arithmetic_geometric_mean hn hu.
have hV := finite_arithmetic_geometric_mean hn hv.
have hTotal : (\sum_i u i)+(\sum_i v i)=(n%:R:R).
  transitivity (\sum_i (u i+v i)); first by rewrite big_split.
  under eq_bigr do rewrite hSum.
  by rewrite sumr_const card_ord -(@mulr_natl R 1 n) mulr1.
have hPositive : (0<n%:R :> R) by rewrite ltr0n.
have hRight : (\sum_i u i)/n%:R+(\sum_i v i)/n%:R=(1:R).
  by rewrite -mulrDl hTotal divff // gt_eqF.
have hBound := lerD hU hV.
by rewrite hRight in hBound.
Qed.
