(** Federer (1969), 4.1.18, p. 374: the
    original smoothing homotopy formulas for currents.
    Average the already proved fixed-z identities
    using the independent action of the opaque
    smoothing deformation. All currents are arbitrary;
    zero and positive top degree are separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal ring.
From Federer Require Import Bilinear Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentEvaluation CurrentPointEvaluation CurrentBoundary CurrentTestExteriorDerivative
  CurrentAboveDimension CurrentProbabilityAverageAction CurrentTranslations
  CurrentTranslationChain CurrentTranslationChainHomotopy CurrentSmoothingOperators
  CurrentSmoothingTranslationAverage CurrentSmoothingDeformationUP CurrentSmoothingDeformationSealed
  SmoothingKernelUP SmoothingDilationUP SmoothingReflectedWeight EuclideanLebesgueDimensions
  SummableRealFunctionUP SummableRealArithmetic MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothingHomotopy.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation C:=(fun d=>@current_space R h2 n Full hFull d).
Local Notation DT:=(fun d=>@current_test_space R h2 n Full hFull d).
Local Notation action:=(fun d=>@current_value R h2 n Full hFull d).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation w:=(fun z:X=>family epsilon (-z)).
Local Notation mu:=(@euclidean_lebesgue_measure R n).
Local Notation hm:=(euclidean_lebesgue_is_measure R n).
Local Notation Smooth:=(fun d (T:C d)=>
  @current_smoothing R h2 n d phi family hPhi hFamily T epsilon).
Local Notation H:=(fun d (T:C d)=>
  @CurrentSmoothingDeformation.value R h2 n d phi family hPhi hFamily epsilon hEpsilon T).

(** Source for [current_smoothing_homotopy_positive]:
    T_epsilon−T=boundary(H_epsilon T)
    +H_epsilon(boundary T), the first displayed
    formula of 4.1.18, p. 374. The proof
    in fact works for every positive degree. *)
Theorem current_smoothing_homotopy_positive j (T:C j.+1):
  Smooth j.+1 T-T=
  @current_boundary R h2 n j.+1 Full hFull (H j.+1 T)+
    H j (@current_boundary R h2 n j Full hFull T).
Proof.
apply:(@current_values_extensional R h2 n j.+1 Full hFull)=>omega.
pose B:=@current_boundary R h2 n j Full hFull T.
pose dOmega:=@current_test_exterior_derivative R h2 n j.+1 Full hFull omega.
have hLeft:=@current_probability_average_difference_action R h2 n j.+1 Full hFull X mu hm w
  (fun z=>@current_translation_pushforward R h2 n j.+1 z T) (Smooth j.+1 T) T
  (@smoothing_reflected_weight_integral_one R n phi family hPhi hFamily epsilon hEpsilon)
  (@current_smoothing_translation_average R h2 n j.+1 phi family hPhi hFamily epsilon hEpsilon T)
  omega.
have hFirst:=@CurrentSmoothingDeformation.laws R h2 n j.+1 phi family hPhi hFamily
  epsilon hEpsilon T dOmega.
have hSecond:=@CurrentSmoothingDeformation.laws R h2 n j phi family hPhi hFamily
  epsilon hEpsilon B omega.
have hRight:=@real_total_integral_add R X mu hm _ _ _ _ hFirst hSecond.
have hFunction:(fun z=>w z*action j.+1
    (@current_translation_pushforward R h2 n j.+1 z T-T) omega)=
    (fun z=>w z*action j.+2 (@current_translation_chain R h2 n j.+1 z T) dOmega+
      w z*action j.+1 (@current_translation_chain R h2 n j z B) omega).
  apply:funext=>z;rewrite current_translation_positive_homotopy.
  have hSum:action j.+1
      (@current_boundary R h2 n j.+1 Full hFull
        (@current_translation_chain R h2 n j.+1 z T)+
        @current_translation_chain R h2 n j z B) omega=
      action j.+2 (@current_translation_chain R h2 n j.+1 z T) dOmega+
      action j.+1 (@current_translation_chain R h2 n j z B) omega.
    change (@current_point_evaluation R h2 n j.+1 Full hFull omega
      (@current_boundary R h2 n j.+1 Full hFull
        (@current_translation_chain R h2 n j.+1 z T)+
        @current_translation_chain R h2 n j z B)=
      action j.+2 (@current_translation_chain R h2 n j.+1 z T) dOmega+
      action j.+1 (@current_translation_chain R h2 n j z B) omega).
    by rewrite (Bilinear.linD (hom_linear
      (@current_point_evaluation R h2 n j.+1 Full hFull omega)))
      !current_point_evaluation_values current_boundary_evaluation.
  rewrite hSum;ring.
rewrite hFunction in hLeft.
have hValue:=EFin_inj (measure_integral_unique hLeft hRight).
have hSum:action j.+1
    (@current_boundary R h2 n j.+1 Full hFull (H j.+1 T)+H j B) omega=
    action j.+2 (H j.+1 T) dOmega+action j.+1 (H j B) omega.
  change (@current_point_evaluation R h2 n j.+1 Full hFull omega
    (@current_boundary R h2 n j.+1 Full hFull (H j.+1 T)+H j B)=
    action j.+2 (H j.+1 T) dOmega+action j.+1 (H j B) omega).
  by rewrite (Bilinear.linD (hom_linear
      (@current_point_evaluation R h2 n j.+1 Full hFull omega)))
      !current_point_evaluation_values current_boundary_evaluation.
exact:eq_trans hValue (esym hSum).
Qed.

(** Source for [current_smoothing_homotopy_zero]:
    T_epsilon−T=boundary(H_epsilon T) when m=0,
    Federer 4.1.18, p. 374. This includes
    ambient dimension zero without a negative index. *)
Theorem current_smoothing_homotopy_zero (T:C 0%N):
  Smooth 0%N T-T=@current_boundary R h2 n 0%N Full hFull (H 0%N T).
Proof.
apply:(@current_values_extensional R h2 n 0%N Full hFull)=>omega.
pose dOmega:=@current_test_exterior_derivative R h2 n 0%N Full hFull omega.
have hLeft:=@current_probability_average_difference_action R h2 n 0%N Full hFull X mu hm w
  (fun z=>@current_translation_pushforward R h2 n 0%N z T) (Smooth 0%N T) T
  (@smoothing_reflected_weight_integral_one R n phi family hPhi hFamily epsilon hEpsilon)
  (@current_smoothing_translation_average R h2 n 0%N phi family hPhi hFamily epsilon hEpsilon T)
  omega.
have hRight:=@CurrentSmoothingDeformation.laws R h2 n 0%N phi family hPhi hFamily
  epsilon hEpsilon T dOmega.
have hFunction:(fun z=>w z*action 0%N
    (@current_translation_pushforward R h2 n 0%N z T-T) omega)=
    (fun z=>w z*action 1%N (@current_translation_chain R h2 n 0%N z T) dOmega).
  apply:funext=>z;by rewrite current_translation_zero_homotopy current_boundary_evaluation.
rewrite hFunction in hLeft.
rewrite current_boundary_evaluation.
exact:(EFin_inj (measure_integral_unique hLeft hRight)).
Qed.

(** Source for [current_smoothing_homotopy_top]:
    T_epsilon−T=H_epsilon(boundary T) in positive
    top degree, Federer 4.1.18, p. 374.
    The omitted (n+1)-current is actually zero
    by the preceding dimension theorem, not by
    an extra mass or normality assumption. *)
Theorem current_smoothing_homotopy_top j (hTop:n=j.+1) (T:C j.+1):
  Smooth j.+1 T-T=H j (@current_boundary R h2 n j Full hFull T).
Proof.
rewrite current_smoothing_homotopy_positive.
have hAbove:(n<j.+2)%N by rewrite hTop ltnSn.
have hZero:=@current_above_dimension R h2 n j.+2 hAbove Full hFull (H j.+1 T).
by rewrite hZero linear0 add0r.
Qed.
End CurrentSmoothingHomotopy.
