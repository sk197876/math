(** Federer (1969), 3.2.46, pp. 281–282: combine
    the local metric-volume comparison and a nearby positive
    density bound. This is scalar extended-nonnegative algebra;
    zero and infinite masses are included. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [local_density_comparison_algebra]: the local
    two-sided comparisons differ by at most lambda^(k+1),
    supporting the limit argument of 3.2.46, pp. 281–282.
    Both scalings are finite and strictly positive. *)
Lemma local_density_comparison_algebra (R : realType) (lambda d : R) k
    (phi mu nu : \bar R) :
  0<lambda ->
  (d%:E*phi<=(lambda^+k)%:E*mu)%E ->
  (mu<=(lambda^+k)%:E*d%:E*phi)%E ->
  ((d/lambda)%:E*phi<=nu)%E -> (nu<=(lambda*d)%:E*phi)%E ->
  (mu<=(lambda^+k.+1)%:E*nu)%E /\ (nu<=(lambda^+k.+1)%:E*mu)%E.
Proof.
move=> hLambda hLower hUpper hNuLower hNuUpper.
have hLambdaE : (0<=lambda%:E)%E by rewrite lee_fin; exact: ltW hLambda.
have hPowerE : (0<=(lambda^+k)%:E)%E by rewrite lee_fin exprn_ge0 //; exact: ltW hLambda.
have hCancel : lambda*(d/lambda)=d by rewrite mulrC divfK //; exact: lt0r_neq0 hLambda.
have hScaled := lee_wpmul2l hLambdaE hNuLower.
rewrite muleA -EFinM hCancel in hScaled.
split.
- apply: le_trans hUpper _; rewrite -muleA.
  have h := lee_wpmul2l hPowerE hScaled.
  have hCoefficient : ((lambda^+k)%:E*(lambda%:E*nu))%E =
      ((lambda^+k.+1)%:E*nu)%E by rewrite muleA -EFinM -exprSr.
  by rewrite hCoefficient in h.
- apply: le_trans hNuUpper _.
  have h := lee_wpmul2l hLambdaE hLower.
  have hCoefficient : (lambda%:E*((lambda^+k)%:E*mu))%E =
      ((lambda^+k.+1)%:E*mu)%E by rewrite muleA -EFinM -exprS.
  by rewrite hCoefficient muleA -EFinM in h.
Qed.
