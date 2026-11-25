(** Federer (1969), 4.1.18, p. 375: averaging
    the two original parameter-homotopy endpoint
    pullbacks gives the form itself and its
    actual convolution. The proof retains the
    reflected kernel and every smooth form degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal.
From Federer Require Import SmoothFunctionSpaceLaws Hom TensorUP RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading ExteriorMaps ExteriorMapScaling AlternatingForms AlternatingDual
  AlternatingPairing PairingLinear CurrentSpaces SmoothFunctionSpaceUP CurrentDiracDensity CurrentCoefficientNorms
  CurrentZeroDegreeExteriorLaws CurrentCartesianDomain CurrentCartesianVectorProduct
  CurrentCartesianProjections SmoothFormPullbackUP SmoothFormPullbackSealed
  CurrentTranslationParameterHomotopy CurrentAdditionZeroFactorPullback
  CurrentCompactKernelFormAverageUP CurrentCompactSmoothingFormAverage
  CurrentSmoothingOperators CurrentFormVectorIntegralPairing SmoothingReflectedTranslationIntegral
  SmoothingKernelUP SmoothingDilationUP SmoothingReflectedWeight EuclideanLebesgueDimensions
  SummableRealFunctionUP SummableRealArithmetic MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothingFormAverageEndpoints.
Variable R:realType.
Hypothesis h2:(1+1:R)!= 0.
Variables n j:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (n+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation AB:=(@euclidean_cartesian_set R n n Full Full).
Local Notation hAB:=(@current_cartesian_domain_open R n n Full Full hFull hFull).
Local Notation E:=(@current_smooth_space R h2 n Full hFull j).
Local Notation ev:=(@current_smooth_value R h2 n Full hFull j).
Local Notation F:=(@current_smooth_space R h2 (n+n)%N AB hAB j).
Local Notation fv:=(@current_smooth_value R h2 (n+n)%N AB hAB j).
Local Notation q:=(@euclidean_last_block_map R n n).
Local Notation Q:=(@euclidean_last_injection_map R n n).
Local Notation Add:=(@current_translation_parameter_end R n).
Local Notation Image:=(fun (a:Z) (_:AB a)=>Logic.I).
Local Notation hQ:=(@current_cartesian_last_projection_smooth R n n Full Full hFull hFull).
Local Notation PullQ:=(@SmoothFormPullback.operator R h2 (n+n)%N n j AB Full hAB hFull
  q Image hQ).
Local Notation PullAdd:=(@SmoothFormPullback.operator R h2 (n+n)%N n j AB Full hAB hFull
  Add Image (@current_addition_product_smooth R n)).
Local Notation unit:=(@current_scalar_multivector_unit R n).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation w:=(fun z:X=>family epsilon (-z)).
Local Notation A:=(@current_compact_smoothing_form_average R h2 n
  phi family hPhi hFamily epsilon hEpsilon j).

(** Source for [current_projection_zero_factor_pullback]:
    the original starting projection leaves spatial
    form coefficients unchanged on the zero-degree
    parameter factor, supporting 4.1.18, p. 375. *)
Theorem current_projection_zero_factor_pullback (omega:E) z x eta:
  pairing (@current_cartesian_vector_product R n n 0%N j unit eta)
    (fv (PullQ omega) (euclidean_block_join (z,x)))= pairing eta (ev omega x).
Proof.
have hPoint:AB (euclidean_block_join (z,x)) by split.
rewrite (@smooth_form_pullback_values R (n+n)%N n j AB Full E F ev fv q PullQ
  (@SmoothFormPullback.laws R h2 (n+n)%N n j AB Full hAB hFull q Image hQ)
  omega (euclidean_block_join (z,x)) q hPoint
  (@current_cartesian_last_projection_differential R n n Full Full hFull hFull
    (euclidean_block_join (z,x)) hPoint)).
rewrite A_m_dual_pairing /current_cartesian_vector_product /current_scalar_multivector_unit
  exterior_power_map_zeroth_scalar exterior_product_zeroth_scalar_left scale1r
  exterior_power_map_composition.
have hComp:linear_comp (hom_as_linear q) (hom_as_linear Q)=1 (linear_id X).
  move=>v;exact:euclidean_last_block_injectionK.
rewrite (@exterior_power_map_ext R X X _ (linear_id X) hComp j eta)
  exterior_power_map_identity.
change (pairing eta (ev omega
  ((@euclidean_block_split R n n (euclidean_block_join (z,x))).2))=
  pairing eta (ev omega x)).
by rewrite euclidean_block_joinK.
Qed.

(** Source for [current_smoothing_form_average_initial]:
    averaging the original identity endpoint gives
    exactly omega, supporting the corresponding form
    homotopy in 4.1.18, p. 375. *)
Theorem current_smoothing_form_average_initial (omega:E):A (PullQ omega)= omega.
Proof.
apply:(smooth_function_extensional (@current_smooth_space_laws R h2 n Full hFull j))=>x _.
apply:pairing_ext=>eta.
have hAverage:=@current_compact_smoothing_form_average_laws R h2 n
  phi family hPhi hFamily epsilon hEpsilon j (PullQ omega) x Logic.I eta.
have hConstant:=@real_total_integral_scale R X (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) w 1 (pairing eta (ev omega x))
  (@smoothing_reflected_weight_integral_one R n phi family hPhi hFamily epsilon hEpsilon).
rewrite mulr1 in hConstant.
have hFunction:(fun z=>w z*
    pairing (@current_cartesian_vector_product R n n 0%N j unit eta)
      (fv (PullQ omega) (euclidean_block_join (z,x))))=
    (fun z=>pairing eta (ev omega x)*w z).
  by apply:funext=>z;rewrite current_projection_zero_factor_pullback mulrC.
change (is_measure_integral (@euclidean_lebesgue_measure R n)
  (real_total_integrand (fun z=>w z*
    pairing (@current_cartesian_vector_product R n n 0%N j unit eta)
      (fv (PullQ omega) (euclidean_block_join (z,x)))))
  (pairing eta (ev (A (PullQ omega)) x))%:E) in hAverage.
rewrite hFunction in hAverage.
exact:(EFin_inj (measure_integral_unique hAverage hConstant)).
Qed.

(** Source for [current_smoothing_form_average_final]:
    averaging the original addition endpoint is
    exactly Phi_epsilon*omega, with the actual
    Banach convolution from 4.1.2, supporting
    the form homotopy of 4.1.18, p. 375. *)
Theorem current_smoothing_form_average_final (omega:E):
  A (PullAdd omega)=@current_smooth_smoothing R h2 n j phi family hPhi hFamily epsilon omega.
Proof.
apply:(smooth_function_extensional (@current_smooth_space_laws R h2 n Full hFull j))=>x _.
apply:pairing_ext=>eta.
have hAverage:=@current_compact_smoothing_form_average_laws R h2 n
  phi family hPhi hFamily epsilon hEpsilon j (PullAdd omega) x Logic.I eta.
have hVector:=@smoothing_reflected_translation_integral R n (A_m X R^o j)
  (@current_form_comass R h2 n j) (@current_form_comass_real_norm R h2 n j)
  (family epsilon) (ev omega)
  (ev (@current_smooth_smoothing R h2 n j phi family hPhi hFamily epsilon omega))
  (@current_smooth_smoothing_convolution R h2 n j phi family hPhi hFamily
    epsilon hEpsilon omega) x.
have hScalar:=@current_form_vector_integral_pairing R h2 n j X
  (@euclidean_lebesgue_measure R n) (fun z=>w z*:ev omega (x+z))
  (ev (@current_smooth_smoothing R h2 n j phi family hPhi hFamily epsilon omega) x)
  eta hVector.
have hFunction:(fun z=>w z*
    pairing (@current_cartesian_vector_product R n n 0%N j unit eta)
      (fv (PullAdd omega) (euclidean_block_join (z,x))))=
    (fun z=>pairing eta (w z*:ev omega (x+z))).
  apply:funext=>z;rewrite current_addition_zero_factor_pullback.
  change (w z*pairing eta (ev omega (x+z))= pairing_right eta (w z*:ev omega (x+z))).
  by rewrite linearZ_LR pairing_rightE.
change (is_measure_integral (@euclidean_lebesgue_measure R n)
  (real_total_integrand (fun z=>w z*
    pairing (@current_cartesian_vector_product R n n 0%N j unit eta)
      (fv (PullAdd omega) (euclidean_block_join (z,x)))))
  (pairing eta (ev (A (PullAdd omega)) x))%:E) in hAverage.
rewrite hFunction in hAverage.
exact:(EFin_inj (measure_integral_unique hAverage hScalar)).
Qed.
End CurrentSmoothingFormAverageEndpoints.
