(** Federer (1969), 4.1.18, p. 375: the
    full-domain Omega density current has exactly
    its original ambient Lebesgue action. The
    canonical inverse domain copies preserve every
    original test integral, by 2.4.18. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingPairing CurrentDomain CurrentSpaces CurrentDensityAction
  CompactSummableMultivectors CompactSummableMultivectorDensity CompactSummableMultivectorLinear
  CompactSummableMultivectorAmbient EuclideanOpenDomainMeasure EuclideanFullDomainMeasure
  EuclideanLebesgueDimensions MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  SummableRealFunctionUP RadonWeightedPushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CompactSummableFullCurrentAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Local Notation mu:=(@euclidean_open_domain_measure R n Full).
Local Notation hm:=(@euclidean_open_domain_measure_laws R n Full hFull).1.
Local Notation W:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation value:=(@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation A:=(@compact_summable_multivector_current R h2 n m Full hFull).
Local Notation raw:=(@compact_summable_multivector_ambient_value R h2 n m Full hFull).

(** Source for [compact_summable_full_current_action]:
    the original Lebesgue wedge xi on R^n integrates
    its literal total representative, supporting ordinary
    field smoothing in Federer 4.1.18, p. 375. *)
Theorem compact_summable_full_current_action (xi:W):
  @is_current_density_action R h2 n m (@euclidean_lebesgue_measure R n) (raw xi) (A xi).
Proof.
move=>omega.
pose f:=fun x:X=>pairing (raw xi x) (@current_test_value R h2 n Full hFull m omega x).
have hOriginal:=@compact_summable_multivector_current_action R h2 n m Full hFull xi omega.
have hFunction:(fun x:FT=>pairing (value xi x)
      (@current_test_value R h2 n Full hFull m omega (set_val x)))=
    (fun x:FT=>f (set_val x)).
  apply:funext=>x;rewrite /f
    (@compact_summable_multivector_ambient_inside R h2 n m Full hFull xi x).
  reflexivity.
rewrite hFunction in hOriginal.
have hImage:=(@real_total_pushforward_integral_iff R FT X mu hm set_val f hOriginal.1 _).1 hOriginal.
by rewrite euclidean_full_domain_measure_ambient in hImage.
Qed.
End CompactSummableFullCurrentAction.
