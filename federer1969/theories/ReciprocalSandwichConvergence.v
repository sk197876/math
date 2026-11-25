(** Federer (1969), 3.2.22, p. 260:
    the scalar convergence behind measurable Jacobian
    approximations as the distortion tends to one. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology lra.
From Federer Require Import RealMetricBackground ReciprocalNearOnePowerBound
  ReciprocalSequenceLimits RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [reciprocal_sandwich_convergence]: supporting
    lambda-to-one passage in Federer 3.2.22, p. 260.
    If a nonnegative scalar x bounds u_j between
    x/(1+1/(j+1)) and (1+1/(j+1))x, then u_j
    converges to x in the real metric. An elementary
    inverse bound controls both errors, including x=0. *)
Lemma reciprocal_sandwich_convergence (R:realType) (u:nat->real_line_metric R) (x:R):
  0<=x ->
  (forall j,(1+((j.+1%:R:R)^-1))^-1*x<=u j /\
    u j<=(1+((j.+1%:R:R)^-1))*x) ->
  u @ \oo --> (x:real_line_metric R).
Proof.
move=>hx hBounds; apply/cvg_ballP=>eps he.
have heR:0<eps:=he.
have hx1:0<x+1 by lra.
have hSmall:0<eps/(x+1) by rewrite divr_gt0.
have [N hN]:=@extended_finite_order_limit_error R (fun j=>(j.+1%:R:R)^-1) 0
  (eps/(x+1)) (reciprocal_natural_order_limit R) hSmall.
exists N=>// j hj.
have hRecip:=hN j hj.
rewrite subr0 ger0_norm ?invr_ge0 ?ler0n // in hRecip.
pose t:=(j.+1%:R:R)^-1.
have ht:0<=t by rewrite /t invr_ge0 ler0n.
have hInverse:=@inverse_near_one_power_lower_bound R 1 t ht.
rewrite expr1 mul1r in hInverse.
have hLower:=ler_wpM2r hx hInverse.
have [hL hU]:=hBounds j.
change (is_true ((1+t)^-1*x<=u j)) in hL.
change (is_true (u j<=(1+t)*x)) in hU.
have hLower2:(1-t)*x<=u j:=le_trans hLower hL.
have hError:t*x<eps.
  have hProduct:(x+1)*t<eps by move:hRecip; rewrite -/t ltr_pdivlMr // mulrC.
  nra.
rewrite ballEmdist /= real_line_metric_distanceE ltr_norml.
apply/andP; split; nra.
Qed.
