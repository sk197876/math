(** Federer (1969), 4.1.1, p. 346: the
    C1 pairing product rule and vanishing compact
    derivative integral give the original
    integration-by-parts identity. Only the
    vector factor has compact support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialDirectional NormClassOneUP
  NormRegularity LinearBasis ContinuousDualUP ContinuousDualNorm NormBoundedBilinearUP
  NormDualEvaluationBilinear NormBilinearDifferentialAlgebra NormDifferentialBilinearProduct
  NormClassOneDirectionalField SmoothCompactSet TopologicalBorel MeasureUP MeasurePushforward
  MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP SummableRealArithmetic
  NormCompactScalarSummability CompactScalarDirectionalIntegralZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_dual_pairing_integration_by_parts]:
    integral <D_v phi,xi> is minus integral
    <phi,D_v xi>, the original identity in
    Federer 4.1.1, p. 346. All integrals
    are proved finite before applying linearity. *)
Theorem compact_dual_pairing_integration_by_parts (R:realType) (X Y YD:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (ed:Hom YD (Hom Y R^o)) (DN:YD->R) (hD:is_continuous_dual hNY ed DN)
    d (b:'I_d->X) (hb:is_basis b) (mu:set X->\bar R) (hm:is_measure mu)
    (hB:forall A:set X,@borel_set (real_norm_metric_space hNX) A ->measure_measurable mu A)
    (hK:forall C:set X,@compact (real_norm_metric_space hNX) C ->(mu C< +oo)%E)
    (hInvariant:forall c:X,measure_pushforward (fun x=>x+c) mu=mu)
    (K:smooth_compact_set hNX (fun _=>True)) (phi:X->Y) (xi:X->YD)
    (DPhi:X->Hom X Y) (DXi:X->Hom X YD) (v:X):
  is_norm_class_one_field NX NY (fun _=>True) phi DPhi ->
  is_norm_class_one_field NX DN (fun _=>True) xi DXi ->
  (forall x,~smooth_compact_carrier K x ->phi x=0) ->
  exists a:R,
    is_measure_integral mu (real_total_integrand (fun x=>ed (xi x) (DPhi x v))) a%:E /\
    is_measure_integral mu (real_total_integrand (fun x=>ed (DXi x v) (phi x))) (-a)%:E.
Proof.
move=>hPhi hXi hZero.
pose hDN:=continuous_dual_norm_is_norm hD.
pose hR:=@scalar_absolute_value_norm R.
have hPhi1:norm_class hNX hNY (fun _=>True) phi 1%N.
  apply:(@norm_class_firstP R X Y NX NY hNX hNY (fun _=>True) phi).2; by exists DPhi.
have hXi1:norm_class hNX hDN (fun _=>True) xi 1%N.
  apply:(@norm_class_firstP R X YD NX DN hNX hDN (fun _=>True) xi).2; by exists DXi.
have hPair1:=@norm_class_dual_pairing R Y NY hNY YD ed DN hD X NX hNX
  (fun _=>True) phi xi 1%N hPhi1 hXi1.
have [H hH]:=(@norm_class_firstP R X R^o NX (fun t:R^o=>`|t|) hNX hR
  (fun _=>True) (fun x=>ed (xi x) (phi x))).1 hPair1.
have hPairZero x:~smooth_compact_carrier K x ->ed (xi x) (phi x)=0.
  move=>hx; by rewrite (hZero x hx) linear0.
have hIntegralZero:=@compact_scalar_directional_integral_zero R X NX hNX d b hb mu hm hB hK hInvariant
  K (fun x=>ed (xi x) (phi x)) H v hH hPairZero.
have hDPhi0:=@norm_class_one_directional_continuous R X Y NX NY hNX hNY (fun _=>True) phi DPhi v hPhi.
have hDXi0:=@norm_class_one_directional_continuous R X YD NX DN hNX hDN (fun _=>True) xi DXi v hXi.
have hDPhiClass:=(@norm_class_zeroP R X Y NX NY hNX hNY (fun _=>True) (fun x=>DPhi x v)).2 hDPhi0.
have hDXiClass:=(@norm_class_zeroP R X YD NX DN hNX hDN (fun _=>True) (fun x=>DXi x v)).2 hDXi0.
have hXi0:=norm_class_lower (leq0n 1) hXi1.
have hPhi0:=norm_class_lower (leq0n 1) hPhi1.
have hAClass:=@norm_class_dual_pairing R Y NY hNY YD ed DN hD X NX hNX
  (fun _=>True) (fun x=>DPhi x v) xi 0%N hDPhiClass hXi0.
have hBClass:=@norm_class_dual_pairing R Y NY hNY YD ed DN hD X NX hNX
  (fun _=>True) phi (fun x=>DXi x v) 0%N hPhi0 hDXiClass.
have hAZero x:~smooth_compact_carrier K x ->ed (xi x) (DPhi x v)=0.
  move=>hx.
  have hDiff y:=@norm_class_one_differential R X Y NX NY (fun _=>True) phi DPhi hPhi y Logic.I.
  by rewrite (@norm_differential_zero_off_compact R X Y NX NY hNX hNY K phi DPhi hZero hDiff x hx)
    hom_zeroE linear0.
have hBZero x:~smooth_compact_carrier K x ->ed (DXi x v) (phi x)=0.
  move=>hx; by rewrite (hZero x hx) linear0.
have [a hAInt]:=@norm_compact_scalar_summable R X NX hNX mu hm hB hK K
  (fun x=>ed (xi x) (DPhi x v)) (norm_class_continuous hAClass) hAZero.
have [c hBInt]:=@norm_compact_scalar_summable R X NX hNX mu hm hB hK K
  (fun x=>ed (DXi x v) (phi x)) (norm_class_continuous hBClass) hBZero.
have [hBilin [C [hC hBound]]]:=@norm_dual_evaluation_bounded_bilinear R Y NY hNY YD ed DN hD.
have hProduct x:H x v=ed (xi x) (DPhi x v)+ed (DXi x v) (phi x).
  have hRule:=@norm_differential_bilinear_product R X Y YD R^o NX NY DN (fun t:R^o=>`|t|)
    hNX hNY hDN hR (fun y a=>ed a y) hBilin C (fun _=>True) phi xi x (DPhi x) (DXi x) hC hBound
    (@norm_class_one_differential R X Y NX NY (fun _=>True) phi DPhi hPhi x Logic.I)
    (@norm_class_one_differential R X YD NX DN (fun _=>True) xi DXi hXi x Logic.I).
  have hSame:=norm_differential_unique hNX hR (norm_class_one_differential hH Logic.I) hRule.
  exact:(congr1 (fun L:Hom X R^o=>L v) hSame).
have hSum:=@real_total_integral_add R X mu hm (fun x=>ed (xi x) (DPhi x v))
  (fun x=>ed (DXi x v) (phi x)) a c hAInt hBInt.
have hEq:(fun x=>ed (xi x) (DPhi x v)+ed (DXi x v) (phi x))=(fun x=>H x v).
  apply:funext=>x; symmetry; exact:hProduct.
rewrite hEq in hSum.
have hAC:a+c=0:=congr1 (@fine R) (measure_integral_unique hSum hIntegralZero).
have hc:c= -a by lra.
exists a; split; first exact hAInt; by rewrite -hc.
Qed.
