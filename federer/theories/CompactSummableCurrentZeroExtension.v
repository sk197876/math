(** Federer (1969), 4.1.18, p. 375: the
    original Lebesgue-density current on U is the
    open restriction of its literal zero extension
    to R^n. The earlier test zero extension and
    original-U integral give this equality directly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormBoundedLinearTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingForms AlternatingPairing CurrentDomain CurrentSpaces CurrentEvaluation CurrentCoefficientNorms
  CurrentOpenRestriction CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorLinear CompactSummableMultivectorAmbient CompactSummableFullCurrentAction
  EuclideanFullDomainMeasure EuclideanOpenDomainMeasure EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext OpenSubspaceExtension OpenSubspaceTotalZeroExtension
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CompactSummableCurrentZeroExtension.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation WU:=(@compact_summable_multivector_space R h2 n m U hU).
Local Notation WF:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation valueU:=(@compact_summable_multivector_value R h2 n m U hU).
Local Notation valueF:=(@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation rawU:=(@compact_summable_multivector_ambient_value R h2 n m U hU).
Local Notation rawF:=(@compact_summable_multivector_ambient_value R h2 n m Full hFull).
Local Notation AU:=(@compact_summable_multivector_current R h2 n m U hU).
Local Notation AF:=(@compact_summable_multivector_current R h2 n m Full hFull).
Local Notation inclusion:=(fun (x:X) (_:U x)=>Logic.I).
Local Notation restriction:=(@current_open_restriction R h2 n m U Full hU hFull inclusion).

(** Source for [compact_summable_current_zero_extension]:
    open restriction identifies the actual original-U
    density current with its ambient zero extension,
    supporting both ordinary convolutions of 4.1.18,
    p. 375. Empty U and all degrees remain. *)
Theorem compact_summable_current_zero_extension (xi:WU) (zeta:WF):
  valueF zeta=(fun x:FT=>rawU xi (set_val x))->
  AU xi=restriction (AF zeta).
Proof.
move=>hValue.
have hRaw:rawF zeta=rawU xi.
  apply:funext=>x.
  pose x':FT:=@euclidean_full_domain_point R n x.
  change (rawF zeta (set_val x')=rawU xi (set_val x')).
  by rewrite compact_summable_multivector_ambient_inside hValue.
have hOpen:@open XT U.
  rewrite openE=>x hx.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1 (@hU x hx).
have hMeas:@measure_measurable R X (@euclidean_lebesgue_measure R n) U.
  exact:(@euclidean_distribution_measure_open R n U hOpen).
apply:(@current_values_extensional R h2 n m U hU)=>psi.
pose f:=fun x:UT=>pairing (valueU xi x)
  (@current_test_value R h2 n U hU m psi (set_val x)).
have hOriginal:=@compact_summable_multivector_current_action R h2 n m U hU xi psi.
have hZero:=@open_subspace_total_zero_extension_integral R XT U
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) hMeas f
  (@current_value R h2 n U hU m (AU xi) psi)%:E hOriginal.
pose testF:=@current_open_test_extension R h2 n m U Full hU hFull inclusion psi.
have hAmbient:=@compact_summable_full_current_action R h2 n m zeta testF.
have hFunction:(fun x:X=>pairing (rawF zeta x)
      (@current_test_value R h2 n Full hFull m testF x))=
    @open_extension R XT U f.
  apply:funext=>x;rewrite hRaw
    (@current_open_test_extension_values R h2 n m U Full hU hFull inclusion psi x).
  rewrite /open_extension;case:pselect=>hx.
  - pose x':UT:=exist _ x (mem_set hx).
    change (pairing (rawU xi (set_val x'))
      (@current_test_value R h2 n U hU m psi (set_val x'))=f x').
    by rewrite /f compact_summable_multivector_ambient_inside.
  - rewrite (@compact_summable_multivector_ambient_outside R h2 n m U hU xi x hx).
    exact:(lin0 ((@pairing_bilinear R X R^o m).1
      (@current_test_value R h2 n U hU m psi x))).
rewrite hFunction in hAmbient.
rewrite current_open_restriction_evaluation.
exact:(EFin_inj (measure_integral_unique hZero hAmbient)).
Qed.
End CompactSummableCurrentZeroExtension.
