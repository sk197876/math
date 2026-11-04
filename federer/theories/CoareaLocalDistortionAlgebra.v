(** Federer (1969), 3.2.46, p. 282: combine
    the local source-Jacobian, target-volume and fibre
    distortions before letting their common factor tend
    to one. All intermediate values may be infinite. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [coarea_local_distortion_algebra]:
    multiplication of the three actual local comparison
    factors supporting 3.2.46, p. 282. Finite
    positive scalar multiplication is order preserving
    at both zero and infinity; no cancellation by
    a possibly zero integral or Jacobian is used. *)
Lemma coarea_local_distortion_algebra (R : realType) (lambda : R) j k
    (nu common frozen actual : \bar R) :
  0<lambda ->
  (nu<=(lambda^+j)%:E*common)%E -> (common<=(lambda^+j)%:E*nu)%E ->
  (frozen<=lambda%:E*common)%E -> (common<=lambda%:E*frozen)%E ->
  (actual<=(lambda^+k)%:E*frozen)%E -> (frozen<=(lambda^+k)%:E*actual)%E ->
  (nu<=(lambda^+(j+k+1))%:E*actual)%E /\
  (actual<=(lambda^+(j+k+1))%:E*nu)%E.
Proof.
move=> hLambda hSourceUpper hSourceLower hTargetUpper hTargetLower hFibreUpper hFibreLower.
have hLambda0 : (0<=lambda%:E)%E by rewrite lee_fin; exact:ltW hLambda.
have hSource0 : (0<=(lambda^+j)%:E)%E by rewrite lee_fin exprn_ge0 //; exact:ltW hLambda.
have hFibre0 : (0<=(lambda^+k)%:E)%E by rewrite lee_fin exprn_ge0 //; exact:ltW hLambda.
have hFactor : lambda^+j*(lambda*lambda^+k)=lambda^+(j+k+1).
  by rewrite -exprS -exprD ?addn1 ?addnS.
have hFactorReverse : lambda^+k*(lambda*lambda^+j)=lambda^+(j+k+1).
  rewrite -hFactor; ring.
split.
- have hTarget := lee_wpmul2l hLambda0 hFibreLower.
  have hAll := lee_wpmul2l hSource0 (le_trans hTargetLower hTarget).
  apply:le_trans hSourceUpper _.
  by rewrite !muleA -!EFinM -mulrA hFactor in hAll.
- have hTarget := lee_wpmul2l hLambda0 hSourceLower.
  have hAll := lee_wpmul2l hFibre0 (le_trans hTargetUpper hTarget).
  apply:le_trans hFibreUpper _.
  by rewrite !muleA -!EFinM -mulrA hFactorReverse in hAll.
Qed.
