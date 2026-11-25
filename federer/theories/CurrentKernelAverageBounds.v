(** Federer (1969), 4.1.18, pp. 374–375: the
    reflected kernel zero-current is a compact normal
    probability current. Prove every assertion from its
    independent original scalar integral law, preserving the
    exact constant one and dimension zero.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms AlternatingZero CurrentSpaces
  CurrentCoefficientNorms CurrentZeroCovectorMaps CurrentSupportGeometry
  SmoothCompactSet MetricClosedBalls EuclideanNormClosedBalls
  SmoothFunctionSupport CurrentMassUP CurrentMassSealed CurrentMassBasic
  CurrentGlobalComassSealed CurrentGlobalComassBound CurrentFiniteMassRepresentation
  CurrentIntegrationCriterion NormalCurrentsUP CurrentScalarCutoffs
  CurrentBoundedNeighbourhoodTest CurrentCompactSmoothValue CurrentCompactSmoothAgreement
  ExtendedSupremumUP EuclideanLebesgueDimensions SmoothingKernelUP SmoothingDilationUP
  SmoothingReflectedWeight CurrentKernelAverageUP CurrentKernelAverageSealed
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralComparison
  RealTotalCharacteristicBounds SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentKernelAverageBounds.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation DT:=(@current_test_space R h2 n Full hFull 0%N).
Local Notation value:=(@current_test_value R h2 n Full hFull 0%N).
Local Notation action:=(@current_value R h2 n Full hFull 0%N).
Local Notation mu:=(@euclidean_lebesgue_measure R n).
Local Notation hm:=(euclidean_lebesgue_is_measure R n).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation w:=(fun z:X=>family epsilon (-z)).
Local Notation S:=(@CurrentKernelAverage.value R h2 n phi family hPhi hFamily epsilon hEpsilon).
Local Notation hS:=(@CurrentKernelAverage.laws R h2 n phi family hPhi hFamily epsilon hEpsilon).
Local Notation hIntegral:=(@smoothing_reflected_weight_integral_one R n phi family
  hPhi hFamily epsilon hEpsilon).
Local Notation hPositive:=(@smoothing_reflected_weight_nonnegative R n phi family
  hPhi hFamily epsilon hEpsilon).
Local Notation hOff:=(@smoothing_reflected_weight_off R n phi family
  hPhi hFamily epsilon hEpsilon).

(** Source for [current_kernel_average_index]: the literal
    compact closed epsilon ball carrying the averaging
    current in 4.1.18, pp. 374–375. *)
Definition current_kernel_average_index:smooth_compact_set hNX Full:=
  @Build_smooth_compact_set R X NX hNX Full (metric_closed_ball
    (0:real_norm_metric_space hNX) epsilon) (fun _ _=>Logic.I)
    (@euclidean_norm_closed_ball_compact R n 0 epsilon).
Local Notation K:=current_kernel_average_index.

(** Source for [current_kernel_average_index_carrier]: the
    support ball has exactly |z|<=epsilon, including
    the boundary, in 4.1.18, p. 375. *)
Theorem current_kernel_average_index_carrier:
  smooth_compact_carrier K=[set z|NX z<=epsilon].
Proof.
rewrite /current_kernel_average_index /= euclidean_norm_closed_ballE.
apply:funext=>z.
change (is_true (NX (z-0)<=epsilon)=is_true (NX z<=epsilon)).
by rewrite subr0.
Qed.

(** Source for [current_kernel_average_support]: the original
    average uses no translation beyond epsilon, as
    required by 4.1.18, pp. 374–375. *)
Theorem current_kernel_average_support:
  @current_support R h2 n Full hFull 0%N S `<=` smooth_compact_carrier K.
Proof.
apply:(@current_support_compact_criterion R h2 n 0%N Full hFull K S).2=>omega hOmega.
have hValues:forall z,smooth_compact_carrier K z->value omega z=0.
  move=>z hz;apply:contrapT=>hNonzero.
  have hAt:=@smooth_function_nonzero_in_support R X (A_m X R^o 0%N)
    NX hNX Full DT value omega z Logic.I hNonzero.
  exact:(hOmega z hAt).2 hz.
have hIntegrand:(fun z=>w z*zero_form_value (value omega z))=(fun _:X=>(0:R)).
  apply:funext=>z;case:(leP (NX z) epsilon)=>hz.
  - have hKz:smooth_compact_carrier K z by rewrite current_kernel_average_index_carrier.
    by rewrite (hValues z hKz) linear0 mulr0.
  - have hZero:family epsilon (-z)=0:=@hOff z hz.
    by rewrite hZero mul0r.
have hAction:=hS omega.
rewrite hIntegrand in hAction.
have hZero:=@real_total_integral_scale R X mu hm w 1 0 hIntegral.
have hZeroFunction:(fun z:X=>0*w z)=(fun _:X=>(0:R)).
  apply:funext=>z;exact:mul0r.
rewrite hZeroFunction mul0r in hZero.
exact:(congr1 (@fine R) (measure_integral_unique hAction hZero)).
Qed.

(** Source for [current_kernel_average_compact]: compactness
    of the original averaging zero-current, needed only
    inside the existence proof in 4.1.18, p. 374. *)
Theorem current_kernel_average_compact:
  @compact (real_norm_metric_space hNX) (@current_support R h2 n Full hFull 0%N S).
Proof.
exact:(@current_support_compact_bound R h2 n 0%N Full hFull K S
  current_kernel_average_support).
Qed.

(** Source for [current_kernel_average_unit_cutoff_action]: any
    actual test equal to one on the kernel ball
    has averaging action one, supporting 4.1.18, p. 374. *)
Theorem current_kernel_average_unit_cutoff_action (gamma:DT):
  (forall z,smooth_compact_carrier K z->value gamma z=@zero_form R X R^o 1)->
  action S gamma= 1.
Proof.
move=>hGamma.
have hIntegrand:(fun z=>w z*zero_form_value (value gamma z))=w.
  apply:funext=>z;case:(leP (NX z) epsilon)=>hz.
  - have hKz:smooth_compact_carrier K z by rewrite current_kernel_average_index_carrier.
    by rewrite (hGamma z hKz) zero_formK mulr1.
  - have hZero:family epsilon (-z)=0:=@hOff z hz.
    by rewrite hZero mul0r.
have hAction:=hS gamma;rewrite hIntegrand in hAction.
exact:(congr1 (@fine R) (measure_integral_unique hAction hIntegral)).
Qed.

(** Source for [current_kernel_average_total]: the literal
    compact smooth total is one. This is the
    exact endpoint coefficient of the averaged homotopy
    in 4.1.18, p. 374. *)
Theorem current_kernel_average_total:
  @current_compact_total R h2 n Full hFull S current_kernel_average_compact= 1.
Proof.
have [gamma [W [hW [hKW [hWU hOne]]]]]:=@current_compact_scalar_cutoff R h2 n Full hFull K.
have hValue:=current_kernel_average_unit_cutoff_action
  (fun z hz=>hOne z (hKW z hz)).
have hSupport: @current_support R h2 n Full hFull 0%N S `<=` W.
  exact:subset_trans current_kernel_average_support hKW.
have hTotal:=@current_compact_total_cutoff R h2 n Full hFull S
  current_kernel_average_compact gamma W hW hSupport hWU hOne.
exact:eq_trans (esym hTotal) hValue.
Qed.

(** Source for [current_kernel_average_mass]: the averaging
    zero-current has exact mass one, preserving the
    original constants in 4.1.18, p. 375. *)
Theorem current_kernel_average_mass:
  @CurrentMass.value R h2 n 0%N Full hFull S= 1%:E.
Proof.
have hUpper:(@CurrentMass.value R h2 n 0%N Full hFull S<=1)%E.
  apply:(extended_supremum_least (@CurrentMass.laws R h2 n 0%N Full hFull S))=>a [omega [hOmega <-]].
  have hCoefficient:forall z,zero_form_value (value omega z)<=1.
    move=>z.
    have hBound:=(@current_global_comass_bound R h2 n 0%N Full (value omega) 1).1
      hOmega z Logic.I.
    rewrite current_zero_form_coefficient_norm in hBound.
    exact:le_trans (ler_norm _) hBound.
  apply:(@measure_integral_monotone R X mu hm _ _ _ _ (hS omega) hIntegral).
  apply:(@real_total_pointwise_order_almost R X mu hm)=>z.
  have hBound:=@ler_wpM2l R (w z) (hPositive z)
    (zero_form_value (value omega z)) 1 (hCoefficient z).
  by rewrite mulr1 in hBound.
have [gamma [_ [hRange hOne]]]:=@current_bounded_neighbourhood_test_exists R h2 n
  K Full (@openT (real_norm_metric_space hNX)) (fun _ _=>Logic.I).
have hValue:=current_kernel_average_unit_cutoff_action hOne.
have hGlobal:(@CurrentGlobalComass.value R h2 n 0%N Full (value gamma)<=1)%E.
  apply:((@current_global_comass_bound R h2 n 0%N Full (value gamma) 1).2)=>z _.
  rewrite current_zero_form_coefficient_norm (ger0_norm (andP (hRange z)).1).
  exact:(andP (hRange z)).2.
have hLower:=@current_mass_unit_test_upper R h2 n 0%N Full hFull S gamma hGlobal.
rewrite hValue in hLower.
apply/eqP;by rewrite eq_le hUpper hLower.
Qed.

(** Source for [current_kernel_average_normal]: the original
    compact probability average is a normal zero-current,
    by 4.1.7; no boundary in negative degree is introduced. *)
Theorem current_kernel_average_normal:
  @is_normal_current R h2 n Full hFull 0%N S.
Proof.
split;last exact:current_kernel_average_compact.
split;last exact:Logic.I.
apply:current_finite_mass_representation.
rewrite current_kernel_average_mass;exact:ltry.
Qed.
End CurrentKernelAverageBounds.
