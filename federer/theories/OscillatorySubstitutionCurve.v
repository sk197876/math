(** Federer (1969), 3.2.7, p. 246: the
    printed oscillatory curve is locally absolutely
    continuous, despite the later failure of substitution.
    Express |x|^(3/2) as |x| sqrt(|x|), including zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology normedtype lra ring.
From Federer Require Import RealMetricBackground RealTrigonometryUP RealTrigonometrySealed
  SignedSquareRootUP SignedSquareRootSealed SignedSquareRootLaws SignedSquareRootAbsoluteContinuity
  CubicOscillationParameter CubicOscillationBounds MetricCurveRelativePostcomposition MetricCurveAbsoluteContinuityUP
  MetricCurveLocalization LocallyAbsolutelyContinuousCurve LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [oscillatory_substitution_curve]: the
    explicit f(x)=|x|^(3/2) sin(1/x), f(0)=0,
    in the third example of Federer 3.2.7, p. 246. *)
Definition oscillatory_substitution_curve (R:realType) (x:R):R:=
  `|x|*Num.sqrt `|x|*RealTrigonometry.sine (x^-1).

(** Source for [oscillatory_substitution_curve_zero]:
    the stipulated zero value in Federer 3.2.7, p. 246. *)
Lemma oscillatory_substitution_curve_zero (R:realType):
  @oscillatory_substitution_curve R 0= 0.
Proof. by rewrite /oscillatory_substitution_curve normr0 mul0r mul0r. Qed.

(** Source for [oscillatory_substitution_curve_factorization]:
    supporting reparameterization of the printed curve
    in Federer 3.2.7, p. 246. The signed
    root reduces its regularity to the proved
    bounded derivatives of the cubic sine parameter. *)
Lemma oscillatory_substitution_curve_factorization (R:realType) (x:R):
  oscillatory_substitution_curve x=
    cubic_oscillation_parameter (SignedSquareRoot.value x).
Proof.
rewrite /oscillatory_substitution_curve /cubic_oscillation_parameter signed_root_square.
case:(lerP 0 x)=>hx.
- rewrite (ger0_norm hx) (signed_square_root_nonnegative (@SignedSquareRoot.laws R) hx).
  have hs:=sqr_sqrtr hx.
  rewrite exprS hs; by ring.
- have hn:0<= -x by rewrite oppr_ge0; exact:ltW hx.
  rewrite (ler0_norm (ltW hx))
    (signed_square_root_nonpositive (@SignedSquareRoot.laws R) (ltW hx))
    invrN (real_sine_odd (@RealTrigonometry.laws R)).
  have hs:=sqr_sqrtr hn.
  rewrite exprS exprNn hs; by ring.
Qed.

(** Source for [oscillatory_substitution_curve_locally_absolutely_continuous]:
    regularity of the explicit curve in the third
    example of Federer 3.2.7, p. 246. The
    signed root is absolutely continuous and the
    outer parameter is Lipschitz on its compact range. *)
Theorem oscillatory_substitution_curve_locally_absolutely_continuous (R:realType):
  is_locally_absolutely_continuous_curve
    (@oscillatory_substitution_curve R:real_line_metric R->real_line_metric R).
Proof.
move=>a b hab; pose G:=@SignedSquareRoot.value R.
pose K:=`|G a|+`|G b|.
have hK:0<=K by apply:addr_ge0; exact:normr_ge0.
have hRange x:a<=x<=b -> (-K<=G x<=K).
  move=>/andP[hax hxb].
  have ha:G a<=G x:=@signed_root_monotone R a x hax.
  have hb:G x<=G b:=@signed_root_monotone R x b hxb.
  have haN:=ler_norm (G a); have haL:=ler_norm (-G a); rewrite normrN in haL.
  have hbN:=ler_norm (G b); have hbL:=ler_norm (-G b); rewrite normrN in hbL.
  rewrite /K; apply/andP; split; have hna:=normr_ge0 (G a); have hnb:=normr_ge0 (G b); lra.
have [hL hLip]:=@cubic_oscillation_bounded_interval_lipschitz R K hK.
have hComp:=@metric_absolute_continuity_relative_postcomposition R
  [the metricType R of real_line_metric R] [the metricType R of real_line_metric R]
  (@cubic_oscillation_parameter R) G (3*K^+2+2) a b hL.
have hAC:is_absolutely_continuous_metric_curve
    ((fun x=>cubic_oscillation_parameter (G x)):R->real_line_metric R) a b.
  apply:hComp.
  - move=>u v hu hv; apply:hLip; rewrite /= in_itv /=; exact:hRange.
  - exact (@signed_root_locally_absolutely_continuous R a b hab).
apply:(@metric_absolute_continuity_equal_on R [the metricType R of real_line_metric R]
  (fun x=>cubic_oscillation_parameter (G x)) (@oscillatory_substitution_curve R) a b _).1 hAC.
move=>x hx; exact:Logic.eq_sym (oscillatory_substitution_curve_factorization x).
Qed.
