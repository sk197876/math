(** Federer (1969), 3.4.2(8), p. 316: cancellation of
    the subdivision counts in the real-dimensional Hausdorff cost. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealPower RealPowerSuccessor RealPowerNaturalHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_two_scale_power_budget]: the last
    inequality in 3.4.2(8), p. 316. With sigma=b+a/lambda,
    alpha*h=beta*j=r and j<=2*eps*h^lambda, the covering cost
    is at most c*N^sigma*r^(a+b)*(2*eps)^(a/lambda).
    All real powers use the existing scalar laws. No limiting
    cost estimate is assumed. *)
Theorem critical_two_scale_power_budget (R:realType) (a b alpha beta:nat)
    (r h j eps N c lambda:R):
  (0<a)%N ->0<lambda ->0<r ->0<h ->0<j ->0<eps ->0<=N ->0<=c ->
  alpha%:R*h=r ->beta%:R*j=r ->j<=2*eps*real_power h lambda ->
  (alpha%:R)^+a*(beta%:R)^+b*
    (c*real_power (N*j) (b%:R+a%:R/lambda))<=
  c*real_power N (b%:R+a%:R/lambda)*r^+(a+b)*
    real_power (2*eps) (a%:R/lambda).
Proof.
move=>ha hLambda hr hh hj hEps hN hc hAlpha hBeta hMesh.
pose t:=a%:R/lambda.
have ht:0<t by rewrite /t divr_gt0 // ltr0n.
have hExponent:lambda*t=(a%:R:R).
  rewrite /t;field;by rewrite gt_eqF.
have hA:(alpha%:R)^+a*h^+a=r^+a by rewrite -exprMn hAlpha.
have hB:(beta%:R)^+b*j^+b=r^+b by rewrite -exprMn hBeta.
have hExact:(alpha%:R)^+a*(beta%:R)^+b*
    (c*real_power (N*j) (b%:R+t))=
    c*real_power N (b%:R+t)*r^+b*(alpha%:R)^+a*real_power j t.
  rewrite (@real_power_product R N j (b%:R+t) hN (ltW hj))
    (@real_power_add_exponents_positive R j b%:R t hj)
    (@real_power_natural_exponent R j b (ltW hj)).
  transitivity (c*real_power N (b%:R+t)*
    ((beta%:R)^+b*j^+b)*(alpha%:R)^+a*real_power j t);first ring.
  by rewrite hB.
have hPower:=@real_power_monotone R j (2*eps*real_power h lambda) t
  (ltW hj) hMesh ht.
have hNonnegative:0<=2*eps by apply:mulr_ge0;[exact:ler0n|exact:ltW hEps].
rewrite (@real_power_product R (2*eps) (real_power h lambda) t hNonnegative (real_power_nonnegative h lambda))
  (@real_power_positive_iterate R h lambda t (ltW hh) hLambda ht) hExponent
  (@real_power_natural_exponent R h a (ltW hh)) in hPower.
rewrite hExact.
have hCoeff:0<=c*real_power N (b%:R+t)*r^+b*(alpha%:R)^+a.
  repeat apply:mulr_ge0;try exact:real_power_nonnegative;
    try apply:exprn_ge0;try exact:ler0n;try exact:ltW hr;exact:hc.
apply:(le_trans (ler_wpM2l hCoeff hPower)).
rewrite le_eqVlt;apply/orP;left;apply/eqP.
transitivity (c*real_power N (b%:R+t)*r^+b*
  ((alpha%:R)^+a*h^+a)*real_power (2*eps) t);first ring.
rewrite hA exprD;ring.
Qed.
