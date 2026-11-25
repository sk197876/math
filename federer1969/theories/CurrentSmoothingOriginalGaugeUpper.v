(** Federer (1969), 4.1.18, p. 375: smoothing
    decreases the original scalar-test variation gauge
    after the positive test is smoothed by the same
    kernel. This is the precise compact-test upper
    inequality before Radon representation.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentSpaces CurrentCoefficientNorms SmoothTestSpaces SmoothTestEvaluation
  DistributionVariationUP DistributionVariationBasic SmoothingKernelUP SmoothingDilationUP
  SmoothingDilationSmooth SmoothingConvolutionUP SmoothingNormMajorant CurrentSmoothingOperators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothingOriginalGaugeUpper.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation Y:=(A_m X R^o m).
Local Notation NY:=(@current_form_comass R h2 n m).
Local Notation hNY:=(@current_form_comass_real_norm R h2 n m).
Local Notation E:=(@current_smooth_space R h2 n Full hFull m).
Local Notation ev:=(@current_smooth_value R h2 n Full hFull m).
Local Notation hE:=(@current_smooth_space_laws R h2 n Full hFull m).
Local Notation DT:=(@current_test_space R h2 n Full hFull m).
Local Notation value:=(@current_test_value R h2 n Full hFull m).
Local Notation values:=(smooth_test_values_hom hE).
Local Notation C:=(@current_space R h2 n Full hFull m).
Local Notation action:=(@current_value R h2 n Full hFull m).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation Q:=(@current_test_smoothing R h2 n m phi family hPhi hFamily epsilon).
Local Notation Smooth:=(@current_smoothing R h2 n m phi family hPhi hFamily).

(** Source for [current_smoothing_original_gauge_upper]:
    ||T_epsilon||(f)<=||T||(Phi_epsilon*f) in the
    original compact scalar-test gauge, supporting the
    averaged-variation inequality of Federer 4.1.18,
    p. 375. Neither measure representation nor
    finite total mass is added to this intermediate law. *)
Theorem current_smoothing_original_gauge_upper (T:C) (f g:X->R^o) b c:
  is_smoothing_convolution (@scalar_absolute_value_norm R) (family epsilon) f g ->
  is_distribution_variation_value NY values (action T) g b%:E ->
  is_distribution_variation_value NY values (action (Smooth T epsilon)) f c ->
    (c<=b%:E)%E.
Proof.
move=>hConv hGauge hSmoothedGauge.
apply:(@distribution_variation_least_finite_bound R X Y NY DT values
  (action (Smooth T epsilon)) f c b hSmoothedGauge)=>omega hOmega.
have hVector:is_smoothing_convolution hNY (family epsilon) (value omega) (value (Q omega)).
  have hOriginal:=@current_smooth_smoothing_convolution R h2 n m phi family hPhi hFamily
    epsilon hEpsilon (smooth_test_inclusion hE omega).
  have hInclusion:=@current_test_smoothing_inclusion R h2 n m phi family hPhi hFamily
    epsilon hEpsilon omega.
  by rewrite -hInclusion in hOriginal.
have hBound:forall x,NY (value (Q omega) x)<=g x.
  exact:(@smoothing_convolution_norm_majorant R n Y NY hNY (family epsilon)
    (value omega) (value (Q omega)) f g
    (@smoothing_dilation_nonnegative R n phi hPhi family hFamily epsilon hEpsilon)
    hVector hConv hOmega).
have hUpper:=@distribution_variation_upper R X Y NY DT values (action T) g b%:E
  hGauge (Q omega) hBound.
rewrite (@current_smoothing_action R h2 n m phi family hPhi hFamily T epsilon hEpsilon omega).
by move:hUpper;rewrite lee_fin.
Qed.
End CurrentSmoothingOriginalGaugeUpper.
