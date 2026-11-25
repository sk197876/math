(** Federer (1969), 3.2.7, p. 246:
    the auxiliary cubic sine parameter has an actual
    bounded differential on each bounded interval.
    Use this project's convex-domain differential bound
    to derive its Lipschitz restrictions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology normedtype lra.
From Federer Require Import Hom RealNormUP RealMetricBackground RealCurveDerivativeUP
  RealCurvePolynomialDerivatives CubicOscillationParameter RealTrigonometryUP RealTrigonometrySealed
  NormDifferentialUP NormDifferentialConvexBound NormHigherCurveDerivativeUP InnerConvex LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cubic_oscillation_actual_derivative_bound]:
    supporting bounded reparameterized derivative for the
    third example of Federer 3.2.7, p. 246.
    The bound 3|t|^2+2 includes the actual zero derivative at zero. *)
Lemma cubic_oscillation_actual_derivative_bound (R:realType) (t:R):
  exists v:R,has_real_curve_derivative (@cubic_oscillation_parameter R) t v /\
    `|v|<=3 * `|t|^+2+2.
Proof.
case:(eqVneq t 0)=>[->|ht].
- exists 0; split; first exact:cubic_oscillation_derivative_zero.
  rewrite normr0; have hs:=exprn_ge0 2 (normr_ge0 (0:R)); nra.
- exists (3*t^+2*RealTrigonometry.sine ((t^+2)^-1)-2*RealTrigonometry.cosine ((t^+2)^-1)); split.
  + exact:cubic_oscillation_derivative_nonzero ht.
  + apply:le_trans (ler_normB _ _) _.
    rewrite !normrM ?normrX !normr_nat.
    apply:lerD.
    * have hPos:0<=3 * `|t|^+2 by rewrite mulr_ge0 ?ler0n // exprn_ge0.
      have hh:=ler_wpM2l hPos (real_sine_bound (@RealTrigonometry.laws R) ((t^+2)^-1)).
      by rewrite mulr1 in hh.
    * have hh:=ler_wpM2l (ler0n R 2) (real_cosine_bound (@RealTrigonometry.laws R) ((t^+2)^-1)).
      by rewrite mulr1 in hh.
Qed.

(** Source for [cubic_oscillation_bounded_interval_lipschitz]:
    Lipschitz control of the auxiliary parameter on
    [-K,K], supporting absolute continuity of the printed
    curve in Federer 3.2.7, p. 246. Every
    derivative and the resulting bound are proved internally. *)
Theorem cubic_oscillation_bounded_interval_lipschitz (R:realType) (K:R):
  0<=K -> is_metric_lipschitz_bound (`[-K,K]:set (real_line_metric R))
    (@cubic_oscillation_parameter R:real_line_metric R->real_line_metric R) (3*K^+2+2).
Proof.
move=>hK.
pose N:=fun t:R^o=>`|t|; have hN:=scalar_absolute_value_norm R.
pose E:=(`[-K,K]:set R^o); pose M:=3*K^+2+2.
have hM:0<=M by rewrite /M; have hs:=exprn_ge0 2 hK; nra.
have hConvex:is_inner_convex E.
  move=>x y hx hy s hs0 hs1.
  move:hx hy; rewrite /E /= !in_itv /= =>/andP[hxl hxu] /andP[hyl hyu].
  change (is_true (-K<=(1-s)*x+s*y<=K)).
  apply/andP; split; nra.
have hD a:E a -> exists L:Hom R^o R^o,
    has_norm_differential N N (fun _=>True) (@cubic_oscillation_parameter R) a L /\
    forall v,N (L v)<=M*N v.
  move=>ha; have [v [hv hBound]]:=@cubic_oscillation_actual_derivative_bound R a.
  exists (@scalar_coefficient_linear_map R R^o v); split.
  - exact (real_curve_derivative_full_differential hv).
  - have haK:`|a|<=K by move:ha; rewrite /E /= in_itv /= -ler_norml.
    have hSquare:`|a|^+2<=K^+2.
      have hMul:=ler_wpM2l (normr_ge0 a) haK.
      have hMul2:=ler_wpM2r hK haK.
      rewrite !expr2; exact (le_trans hMul hMul2).
    have hVM:`|v|<=M.
      have hh:=ler_wpM2l (ler0n R 3) hSquare; rewrite /M; lra.
    move=>w; change (is_true (`|w*v|<=M * `|w|)).
    rewrite normrM [leRHS]mulrC; exact (ler_wpM2l (normr_ge0 w) hVM).
have hLip:=@norm_differential_convex_bound R R^o R^o N N hN hN
  setT E (@cubic_oscillation_parameter R) M hConvex hM hD.
split; first exact hM.
move=>x y hx hy; exact (hLip x y hx hy).
Qed.
