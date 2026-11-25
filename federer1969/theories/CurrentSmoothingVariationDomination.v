(** Federer (1969), 4.1.18, p. 375: the
    original variation of T_epsilon is at most the
    literal reflected average of translated ||T||.
    Compact positive gauges and the earlier Radon
    comparison law prove the inequality on every set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import SmoothTestEvaluation Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  CurrentSpaces CurrentCoefficientNorms CurrentIntegrationCriterion SmoothTestSpaces
  DistributionVariationUP CurrentAmbientVariation SmoothingKernelUP SmoothingDilationUP
  CurrentSmoothingOperators CurrentSmoothingRepresentable CurrentSmoothingOriginalGaugeUpper
  CurrentSmoothingVariationAverage PositiveCompactSmoothing MeasureUP RadonMeasureUP
  RadonCompactScalarIntegral RadonPositiveCompactComparison FunctionLatticeUP CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSmoothingVariationDomination.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation NY:=(@current_form_comass R h2 n m).
Local Notation hE:=(@current_smooth_space_laws R h2 n Full hFull m).
Local Notation values:=(smooth_test_values_hom hE).
Variable T:@current_space R h2 n Full hFull m.
Hypothesis hT:@is_integration_representable_current R h2 n m Full hFull T.
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation Smooth:=(@current_smoothing R h2 n m phi family hPhi hFamily T epsilon).
Local Notation hSmooth:=(@current_smoothing_representable R h2 n m phi family hPhi hFamily T epsilon hEpsilon).
Local Notation rho:=(@current_ambient_variation R h2 n m Smooth hSmooth).
Local Notation hRho:=(@current_ambient_variation_laws R h2 n m Smooth hSmooth).
Local Notation nu:=(@current_smoothing_variation_average R h2 n m T hT
  phi family hPhi hFamily epsilon hEpsilon).
Local Notation hNu:=(@current_smoothing_variation_average_laws R h2 n m T hT
  phi family hPhi hFamily epsilon hEpsilon).
Local Notation D:=(@radon_positive_compact_integral R XT rho hRho.1 hRho.2).
Local Notation A:=(@radon_positive_compact_integral R XT nu hNu.1 hNu.2.1).

(** Source for [current_smoothing_variation_domination]:
    the displayed ||T_epsilon|| <= integral
    Phi_epsilon(-z) tau_z#||T|| dz in Federer
    4.1.18, p. 375, on every original set.
    The input needs only integration representation;
    finite total mass and compact support are not assumed. *)
Theorem current_smoothing_variation_domination:
  forall C:set XT,(rho C<=nu C)%E.
Proof.
apply:(@radon_positive_compact_integral_comparison R XT rho nu
  hRho.1 hNu.1 hRho.2 hNu.2.1 D A
  (@radon_positive_compact_integral_laws R XT rho hRho.1 hRho.2)
  (@radon_positive_compact_integral_laws R XT nu hNu.1 hNu.2.1)).
move=>f hF.
have[g [hG hConv]]:=@positive_compact_smoothing_exists R n phi family hPhi hFamily
  epsilon hEpsilon f hF.
pose mu:=@current_ambient_variation R h2 n m T hT.
pose hMu:=@current_ambient_variation_laws R h2 n m T hT.
pose B:=@radon_positive_compact_integral R XT mu hMu.1 hMu.2.
have hOriginalGauge:=@current_ambient_variation_original_gauge R h2 n m T hT g hG.
have hSmoothGauge:=@current_ambient_variation_original_gauge R h2 n m Smooth hSmooth f hF.
have hBound:=@current_smoothing_original_gauge_upper R h2 n m phi family hPhi hFamily
  epsilon hEpsilon T f g (B g) (D f)%:E hConv hOriginalGauge hSmoothGauge.
have hAverage:=@current_smoothing_variation_average_convolution R h2 n m T hT
  phi family hPhi hFamily epsilon hEpsilon f g hF hG hConv.
rewrite hAverage.
by move:hBound;rewrite lee_fin.
Qed.
End CurrentSmoothingVariationDomination.
