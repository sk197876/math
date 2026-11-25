(** Federer (1969), 4.1.7, p. 359:
    the left primitive integrates an actual
    compact C1 scalar differential. The proof
    transports the preceding scalar fundamental
    theorem through the original R=R^1
    identification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import NormOpenDomainLaws Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLinear NormDifferentialLocal NormDifferentialChain NormDifferentialScalar
  NormClassOneUP NormClassOneDirectionalField NormRegularity NormRegularityLinearMaps
  NormCompactFunctionBound SmoothCompactSet NormHigherCurveDerivativeUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanOneNormDifferential EuclideanFiniteProductIntegral
  EuclideanLebesgueDimensions LebesgueScalarMeasure RealMetricBackground
  RealCompactPrimitiveIntegral MeasureIntegralUP MeasureSubsetIntegral
  RealSubsetIntegralGraph SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanOneCompactPrimitiveIntegral.
Variable R:realType.
Local Notation X := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1)).
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation e := (@coordinate_basis R 1 ord0).

(** Source for [euclidean_one_compact_primitive_integral]:
    the original integral of a compact
    scalar test's differential up to b,
    supporting the actual primitive in Federer
    4.1.7, p. 359. The derivative,
    compact support and integral are the
    project's original objects. *)
Theorem euclidean_one_compact_primitive_integral (f:X->R) (D:X->Hom X R^o)
    (K:smooth_compact_set hNX (fun _=>True)):
  is_norm_class_one_field NX NS (fun _=>True) f D ->
  (forall x,~smooth_compact_carrier K x->f x=0) ->
  forall b:R,is_measure_subset_integral (@euclidean_lebesgue_measure R 1)
    [set x:X|x ord0<=b] (real_total_integrand (fun x=>D x e))
    (f (euclidean_one_embed b))%:E.
Proof.
move=>hClass hOff b.
have hEmbedLinear:linear (fun t:R^o=>(euclidean_one_embed t:X)).
  move=>a t s;apply/ffunP=>i;by rewrite /euclidean_one_embed !ffunE.
pose E:=@HomMap R R^o X (@euclidean_one_embed R) (introT (asboolP _) hEmbedLinear).
have hEmbedBound:norm_bounded_linear NS NX E.
  exists 1;split;first exact:ler01.
  move=>t;by rewrite mul1r euclidean_one_norm_coordinate /E /= /euclidean_one_embed ffunE.
have hE1:E 1=e.
  apply/ffunP=>i;by rewrite /E /= /euclidean_one_embed /coordinate_basis !ffunE (ord1 i) eqxx.
pose F t:=f (E t).
pose G t:=D (E t) e.
have hDerivative t:has_norm_differential NS NS (fun _=>True) F t
    (@scalar_coefficient_linear_map R R^o (G t)).
  have hE:=@norm_differential_linear R R^o X NS NX hNS hNX (fun _=>True)
    t E (norm_full_domain_interior NS t) hEmbedBound.
  have hComposite:=norm_differential_chain hNS hNX hNS hE
    (norm_class_one_differential hClass Logic.I).
  have hWhole:=norm_differential_restrict (fun _ (_:True)=>conj Logic.I Logic.I)
    (norm_full_domain_interior NS t) hComposite.
  have hSame:hom_comp (D (E t)) E=@scalar_coefficient_linear_map R R^o (G t).
    apply:hom_ext=>s;rewrite hom_compE [E s]real_source_linear_evaluation hE1 linearZ.
    by rewrite /scalar_coefficient_linear_map /= /G.
  by rewrite hSame in hWhole.
have hContinuous:norm_class_zero NS NS (fun _=>True) G.
  have hDirectional:=norm_class_one_directional_continuous hNX hNS e hClass.
  have hZero:=(@norm_class_zeroP R X R^o NX NS hNX hNS
    (fun _=>True) (fun x=>D x e)).2 hDirectional.
  have hPre:=@norm_class_precompose_linear R R^o X R^o NS NX NS hNS hNX hNS
    (fun _=>True) (fun x=>D x e) E 0%N hEmbedBound hZero.
  exact:(@norm_class_zeroP R R^o R^o NS NS hNS hNS (fun _=>True) G).1 hPre.
have hId:norm_class_zero NX NX (fun _=>True) (fun x:X=>x).
  move=>x _;split;first exact:norm_full_domain_interior.
  move=>eps heps;exists eps;split=>// h _ hh;by rewrite /= addrAC subrr add0r.
have [M [hM hBound]]:=@norm_class_zero_compact_bounded R X X NX NX hNX hNX
  (fun _=>True) (smooth_compact_carrier K) (fun x=>x)
  (smooth_compact_is_compact K) (fun _ _=>Logic.I) hId.
have hFOff t:M<`|t| ->F t=0.
  move=>ht;apply:hOff=>hK.
  have hb:=hBound (E t) hK.
  rewrite euclidean_one_norm_coordinate /E /= /euclidean_one_embed ffunE in hb.
  have hFalse:=lt_le_trans ht hb;by rewrite ltxx in hFalse.
have hGOff t:M<`|t| ->G t=0.
  move=>ht;have hOutside:~smooth_compact_carrier K (E t).
    move=>hK;have hb:=hBound (E t) hK.
    rewrite euclidean_one_norm_coordinate /E /= /euclidean_one_embed ffunE in hb.
    have hFalse:=lt_le_trans ht hb;by rewrite ltxx in hFalse.
  have hZero:=@norm_differential_zero_off_compact R X R^o NX NS hNX hNS K f D hOff
    (fun x=>norm_class_one_differential hClass Logic.I) (E t) hOutside.
  by rewrite /G hZero hom_zeroE.
pose g t:=if pselect (t<=b) then G t else 0.
have hOn:forall t,([set t:R|t<=b]:set (real_line_metric R)) t->g t=G t.
  by move=>t ht;rewrite /g;case:pselect.
have hAway:forall t,~([set t:R|t<=b]:set (real_line_metric R)) t->g t=0.
  by move=>t ht;rewrite /g;case:pselect.
have hScalar:=@real_compact_primitive_left_integral R F G M hM hDerivative hContinuous hFOff hGOff b.
have hScalarTotal:=(@real_subset_integral_total R (real_line_metric R) (@lebesgue_scalar_measure R)
  [set t:R|t<=b] G g (F b)%:E hOn hAway).1 hScalar.
have hEuclidean:=euclidean_scalar_function_integral hScalarTotal.
apply:(@real_subset_integral_total R X (@euclidean_lebesgue_measure R 1)
  [set x:X|x ord0<=b] (fun x=>D x e) (fun x=>g (euclidean_one_project x))
  (f (euclidean_one_embed b))%:E _ _).2 hEuclidean.
- move=>x hx;rewrite hOn // /G /E /= euclidean_one_projectK;by [].
- move=>x hx;exact:hAway.
Qed.
End EuclideanOneCompactPrimitiveIntegral.
