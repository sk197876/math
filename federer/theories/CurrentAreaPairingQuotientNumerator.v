(** Federer (1969), 4.1.25, p. 383: the
    fixed-covector paired numerator is summable for the
    original compact L1 field. Apply the preceding first
    action to a constant target form cut off to
    one on the compact image of the field's carrier.
    No finite source volume or normality is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExteriorGrading
  ExteriorMaps AlternatingForms AlternatingPairing AlternatingZero
  LipschitzUP EuclideanLipschitzClassZero SmoothCompactSet SmoothCompactImage
  CurrentSpaces CurrentConstantFields CurrentScalarCutoffs CurrentScalarCutoffFormTest
  CompactSummableMultivectors CompactSummableMultivectorAmbient
  EuclideanLebesgueDimensions MeasureIntegralUP MeasureIntegralGraphEquivalence
  SummableRealFunctionUP CurrentLipschitzLebesgueActionIntegrand
  CurrentLipschitzLebesgueAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AreaPairingNumerator.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables m n : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation FullX := (fun _:X=>True).
Local Notation FullY := (fun _:Y=>True).
Local Notation hFullX := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hFullY := (fun (y:Y) (_:True)=>norm_full_domain_interior NY y).
Variable f : inner_metric_space (@euclidean_inner_productP R m)->
  inner_metric_space (@euclidean_inner_productP R n).
Hypothesis hLip : is_metric_lipschitz setT f.
Variable xi : @compact_summable_multivector_space R h2 m m FullX hFullX.
Local Notation raw := (@compact_summable_multivector_ambient_value
  R h2 m m FullX hFullX xi).
Variable a : A_m Y R^o m.

(** Source for [current_area_pairing_numerator_summable]:
    the fixed-covector numerator is an actual summable
    partial Lebesgue integrand, supporting the area step
    in 4.1.25, p. 383. The internally chosen
    compact target test changes none of its original
    differential values or its partial domain. *)
Theorem current_area_pairing_numerator_summable :
  is_measure_summable (@euclidean_lebesgue_measure R m)
    (@current_lipschitz_lebesgue_action_integrand R m n m f raw (fun _=>a)).
Proof.
have hNormLip:@is_metric_lipschitz R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY) setT f.
  have [L [hL hBound]]:=hLip.
  exists L; split; [exact: hL | exact: hBound].
have hContinuous:=@euclidean_lipschitz_norm_class_zero R m n f hLip.
have [C [hC [_ hOff]]]:=@compact_summable_multivector_ambient_carrier
  R h2 m m FullX hFullX xi.
pose K:=@Build_smooth_compact_set R X NX hNX FullX C (fun _ _=>Logic.I) hC.
pose image:=@smooth_compact_image R X Y NX NY hNX hNY FullX FullY
  f (fun _ _=>Logic.I) hContinuous K.
have [gamma [W [hW [hImageW [_ hOne]]]]]:=
  @current_compact_scalar_cutoff R h2 n FullY hFullY image.
pose constant:=@current_constant_form R h2 n FullY hFullY m a.
pose phi:=@current_scalar_cutoff_form_test R h2 n m FullY hFullY constant gamma.
have hPhi x (hx:C x):@current_test_value R h2 n FullY hFullY m phi (f x)=a.
  have hImage:smooth_compact_carrier image (f x) by exists x.
  rewrite (@current_scalar_cutoff_form_test_values R h2 n m FullY hFullY
    constant gamma (f x) Logic.I)
    (@current_constant_form_values R h2 n FullY hFullY m a (f x) Logic.I)
    (hOne (f x) (hImageW (f x) hImage)) zero_formK scale1r.
  reflexivity.
have hAction:=@current_lipschitz_lebesgue_action R h2 m n m xi f hNormLip phi.
eexists.
apply:(@measure_integral_graph_equivalent R X (@euclidean_lebesgue_measure R m)
  _ _ _ _ hAction)=>x z.
rewrite !current_lipschitz_lebesgue_action_integrand_graph.
have hPair (D:Hom X Y):
    pairing (exterior_power_map (hom_as_linear D) m (raw x))
      (@current_test_value R h2 n FullY hFullY m phi (f x))=
    pairing (exterior_power_map (hom_as_linear D) m (raw x)) a.
  case:(pselect (C x))=>hx.
  - by rewrite (hPhi x hx).
  - rewrite (hOff x hx) linear0
      (Bilinear.lin0 ((@pairing_bilinear R Y R^o m).1
        (@current_test_value R h2 n FullY hFullY m phi (f x))))
      (Bilinear.lin0 ((@pairing_bilinear R Y R^o m).1 a)).
    reflexivity.
split.
- move=>[D [hD hValue]];exists D;split;first exact:hD.
  by rewrite -(hPair D).
- move=>[D [hD hValue]];exists D;split;first exact:hD.
  by rewrite (hPair D).
Qed.
End AreaPairingNumerator.
