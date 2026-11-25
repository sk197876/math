(** Federer (1969), 4.1.1, p. 346: the
    integral of a first derivative of a C1
    compactly supported scalar function is zero.
    Translation invariance, the compact Taylor
    estimate and finite-support integral bounds
    give the original vanishing assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity
  LinearBasis TopologicalBorel MeasureUP MeasurePushforward MeasureIntegralUP SummableRealFunctionUP
  SummableRealArithmetic SmoothCompactSet NormClassOneDirectionalField NormCompactDirectionalQuotient
  NormCompactDirectionalErrorSupport NormCompactScalarSummability RealTranslationIntegral
  FiniteMeasureUniformIntegralZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_scalar_directional_integral_zero]:
    the original compact-support reason for the
    vanishing derivative integral in Federer
    4.1.1, p. 346. Only C1 regularity
    is required, and any fixed direction is allowed. *)
Theorem compact_scalar_directional_integral_zero (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) d (b:'I_d->X) (hb:is_basis b)
    (mu:set X->\bar R) (hm:is_measure mu)
    (hB:forall A:set X,@borel_set (real_norm_metric_space hNX) A ->measure_measurable mu A)
    (hK:forall C:set X,@compact (real_norm_metric_space hNX) C ->(mu C< +oo)%E)
    (hInvariant:forall c:X,measure_pushforward (fun x=>x+c) mu=mu)
    (K:smooth_compact_set hNX (fun _=>True)) (f:X->R) (D:X->Hom X R^o) v:
  is_norm_class_one_field NX (fun t:R^o=>`|t|) (fun _=>True) f D ->
  (forall x,~smooth_compact_carrier K x ->f x=0) ->
  is_measure_integral mu (real_total_integrand (fun x=>D x v)) (0:R)%:E.
Proof.
move=>hF hZero.
pose hR:=@scalar_absolute_value_norm R.
have hDiff x:=@norm_class_one_differential R X R^o NX (fun t:R^o=>`|t|) (fun _=>True) f D hF x Logic.I.
have hDerivZero x:~smooth_compact_carrier K x ->D x v=0.
  move=>hx; by rewrite (@norm_differential_zero_off_compact R X R^o NX (fun t:R^o=>`|t|)
    hNX hR K f D hZero hDiff x hx) hom_zeroE.
have hDerivCont:=@norm_class_one_directional_continuous R X R^o NX (fun t:R^o=>`|t|)
  hNX hR (fun _=>True) f D v hF.
have [z hDerivInt]:=@norm_compact_scalar_summable R X NX hNX mu hm hB hK K (fun x=>D x v)
  hDerivCont hDerivZero.
have [a hFInt]:=@norm_compact_scalar_summable R X NX hNX mu hm hB hK K f
  (norm_class_one_zero hF) hZero.
have hClass:norm_class hNX hR (fun _=>True) f 1%N.
  apply:(@norm_class_firstP R X R^o NX (fun t:R^o=>`|t|) hNX hR (fun _=>True) f).2.
  by exists D.
have [C hCommon]:=@norm_compact_directional_error_support R X R^o NX (fun t:R^o=>`|t|)
  hNX hR d b hb K f D v hZero hDiff.
have hClosed:=compact_closed (@metric_hausdorff R (real_norm_metric_space hNX)) (smooth_compact_is_compact C).
have hCM:measure_measurable mu (smooth_compact_carrier C):=hB _ (closed_borel_set hClosed).
have hC0:=measure_nonnegative hm (smooth_compact_carrier C).
have hCFin:=hK _ (smooth_compact_is_compact C).
have hFinite:mu (smooth_compact_carrier C) \is a fin_num.
  by rewrite (ge0_fin_numE hC0).
pose m:=fine (mu (smooth_compact_carrier C)).
have hMass:mu (smooth_compact_carrier C)=m%:E by rewrite /m fineK.
have hz:-z=0.
  apply:(@finite_measure_uniform_integral_zero R X mu hm (smooth_compact_carrier C) m (-z) hCM hMass).
  move=>e he.
  have [s [hs hQuotient]]:=@norm_compact_directional_quotient R X R^o NX (fun t:R^o=>`|t|)
    hNX hR (fun _=>True) (smooth_compact_carrier C) f hClass
    (smooth_compact_is_compact C) (fun _ _=>Logic.I) v e he.
  pose t:=Num.min s 1 /2.
  have hMin:0<Num.min s 1 by rewrite lt_min hs ltr01.
  have ht:0<t by rewrite /t divr_gt0 // ltr0n.
  have htMin:t<Num.min s 1 by rewrite /t; lra.
  have hMs:Num.min s 1<=s by rewrite ge_min lexx.
  have hM1:Num.min s 1<=1 by rewrite ge_min lexx orbT.
  have hts:0<`|t|<s by rewrite (ger0_norm (ltW ht)) ht /=; exact:lt_le_trans htMin hMs.
  have ht1:`|t|<=1 by rewrite (ger0_norm (ltW ht)); exact:ltW (lt_le_trans htMin hM1).
  pose F x:=t^-1*(f (x+t*:v)-f x)-D x v.
  exists F; split.
  - have hTranslate:=@real_translation_integral R X mu hm (t*:v) f a (hInvariant (t*:v)) hFInt.
    have hSubtract:=@real_total_integral_subtract R X mu hm (fun x=>f (x+t*:v)) f a a hTranslate hFInt.
    rewrite subrr in hSubtract.
    have hScale:=@real_total_integral_scale R X mu hm (fun x=>f (x+t*:v)-f x) 0 t^-1 hSubtract.
    rewrite mulr0 in hScale.
    have hError:=@real_total_integral_subtract R X mu hm (fun x=>t^-1*(f (x+t*:v)-f x))
      (fun x=>D x v) 0 z hScale hDerivInt.
    by rewrite sub0r in hError.
  - split.
    + move=>x hx; exact:ltW (hQuotient x hx t hts (D x) (hDiff x)).
    + move=>x hx; exact:(hCommon t ht1 x hx).
have hz0:z=0 by have h:=congr1 (fun r:R=>-r) hz; by rewrite opprK oppr0 in h.
by rewrite hz0 in hDerivInt.
Qed.
