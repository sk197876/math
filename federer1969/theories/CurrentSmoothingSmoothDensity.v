(** Federer (1969), 4.1.18, pp. 374–376: each
    original smoothed current has an actual smooth
    multivector density. This is the full distribution
    regularisation theorem of 4.1.2 specialised to the
    earlier mass/comass duality.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing CurrentCoefficientNorms
  CurrentCoefficientCompleteness CurrentSpaces CurrentVectorSpaces CurrentMultivectorDual
  MultivectorDualSealed ContinuousDualUP ContinuousDualNorm ContinuousRealDual
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius
  SmoothSmoothingFamilyUP SmoothSmoothingFamilySealed TestSmoothingFamilySealed TranslatedKernelTestSealed
  SmoothedDistributionUP SmoothedDistributionDensityCharacterization
  CurrentSmoothingOperators CurrentDensityAction CurrentDensityUniqueness
  CurrentSmoothLebesgue EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothingSmoothDensity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation Y:=(A_m X R^o m).
Local Notation NY:=(@current_form_comass R h2 n m).
Local Notation hNY:=(@current_form_comass_real_norm R h2 n m).
Local Notation hY:=(@current_form_complete R h2 n m).
Local Notation hSep:=(@current_form_separable R h2 n m).
Local Notation E:=(@current_smooth_space R h2 n Full hFull m).
Local Notation ev:=(@current_smooth_value R h2 n Full hFull m).
Local Notation hE:=(@current_smooth_space_laws R h2 n Full hFull m).
Local Notation D:=(@current_smooth_derivatives R h2 n Full hFull m).
Local Notation hD:=(@current_smooth_derivative_laws R h2 n Full hFull m).
Local Notation DT:=(@current_test_space R h2 n Full hFull m).
Local Notation C:=(@current_space R h2 n Full hFull m).
Local Notation action:=(@current_value R h2 n Full hFull m).
Local Notation V:=(@current_vector_smooth_space R h2 n Full hFull m).
Local Notation vv:=(@current_vector_smooth_value R h2 n Full hFull m).
Local Notation hV:=(@current_vector_smooth_space_laws R h2 n Full hFull m).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation dual:=(@MultivectorDual.evaluation R X m).
Local Notation hDual:=(@current_multivector_continuous_dual R h2 n m).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation hKernel:=(@smoothing_dilation_smooth R n phi hPhi family hFamily epsilon hEpsilon).
Local Notation hOff:=(@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily epsilon hEpsilon).
Local Notation B:=(@TranslatedKernelTest.value R n Y NY hNY E ev hE
  (family epsilon) hKernel epsilon hOff).
Local Notation hB:=(@TranslatedKernelTest.laws R n Y NY hNY E ev hE
  (family epsilon) hKernel epsilon hOff).
Local Notation P:=(@current_smooth_smoothing R h2 n m phi family hPhi hFamily).
Local Notation Q:=(@current_test_smoothing R h2 n m phi family hPhi hFamily).
Local Notation Smooth:=(@current_smoothing R h2 n m phi family hPhi hFamily).

(** Source for [current_smoothing_smooth_density_exists]:
    the original smooth g_epsilon from 4.1.2,
    p. 347, represented in the actual multivector
    smooth space for 4.1.18, pp. 374–376.
    Both its literal kernel action and its current
    integral action are retained. *)
Theorem current_smoothing_smooth_density_exists (T:C):
  exists xi:V,
    @is_current_density_action R h2 n m (@euclidean_lebesgue_measure R n)
      (vv xi) (Smooth T epsilon) /\
    forall z theta,pairing (vv xi z) theta=action T (B z theta).
Proof.
have hP:is_smooth_smoothing_family hNY ev family P.
  move=>e he;exact:(@current_smooth_smoothing_convolution R h2 n m
    phi family hPhi hFamily e he).
have hQ:forall omega,smooth_test_inclusion hE (Q epsilon omega)=
    P epsilon (smooth_test_inclusion hE omega).
  exact:(@current_test_smoothing_inclusion R h2 n m phi family hPhi hFamily
    epsilon hEpsilon).
have hT:=@continuous_real_dual_member_continuous R DT (smooth_test_opens hE hD)
  (smooth_test_final_topology_laws hE hD).1 T.
have hA:is_smoothed_distribution action (action T) (Q epsilon) (Smooth T epsilon).
  exact:(@current_smoothing_action R h2 n m phi family hPhi hFamily
    T epsilon hEpsilon).
have [field [hField [hFieldKernel hFieldAction]]]:=
  @smoothed_distribution_has_smooth_density R n Y NY hNY hY hSep E ev hE D hD
    (family epsilon) hKernel epsilon hOff (ltW hEpsilon) B hB
    (P epsilon) (@hP epsilon hEpsilon) (Q epsilon) hQ (action T) hT
    (exterior_power X m) dual VN hDual (Smooth T epsilon) hA.
have hNorm:continuous_dual_norm_is_norm hDual=hVN:=Prop_irrelevance _ _.
rewrite hNorm in hField.
have [xi hXi]:=@smooth_function_evaluation_surjective R X (exterior_power X m)
  NX VN hNX hVN Full V vv hV field hField.
exists xi;split.
- move=>omega.
  have hIntegral:=hFieldAction omega.
  have hFunction:(fun x=>dual (field x) (@current_test_value R h2 n Full hFull m omega x))=
      (fun x=>pairing (vv xi x) (@current_test_value R h2 n Full hFull m omega x)).
    apply:funext=>x;rewrite (@hXi x Logic.I).
    exact:MultivectorDual.laws.
  by rewrite -hFunction.
- move=>z theta;rewrite (@hXi z Logic.I).
  rewrite -(@MultivectorDual.laws R X m (field z) theta).
  exact:hFieldKernel.
Qed.

(** Source for [current_smoothing_smooth_lebesgue_exists]:
    the actual T_epsilon is the original smooth
    Lebesgue-density current, supporting the normal
    approximants in Federer 4.1.18, pp. 375–376.
    No finite total mass premise is required. *)
Theorem current_smoothing_smooth_lebesgue_exists (T:C):
  exists xi:V,Smooth T epsilon=@current_smooth_lebesgue_map R h2 n m xi.
Proof.
have [xi [hAction _]]:=current_smoothing_smooth_density_exists T.
exists xi.
exact:(@current_density_action_unique R h2 n m (@euclidean_lebesgue_measure R n)
  (vv xi) (Smooth T epsilon) (@current_smooth_lebesgue_map R h2 n m xi)
  hAction (current_smooth_lebesgue_action xi)).
Qed.
End CurrentSmoothingSmoothDensity.
