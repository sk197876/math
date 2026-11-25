(** Federer (1969), 4.1.18, p. 376: passage
    from the original finite-prefix identity to
    T=Lebesgue^n wedge xi+boundary S. Use the already
    proved actual L1 and normal-current series limits,
    boundary continuity and the small flat residual. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces CurrentVectorSpaces
  CurrentBoundary NormalCurrentsUP CurrentMassSealed CurrentNormalMass
  CurrentFlatNorm FlatCurrentsUP SmoothCompactSet EuclideanClosedSupportTube
  CurrentFlatSmoothingBudgets CurrentSmoothingOperators
  CompactSummableMultivectors CompactSummableMultivectorDensity
  SmoothingKernelUP SmoothingDilationUP CurrentFlatSmoothingIterationUP
  CurrentFlatSmoothingIterationLimits CurrentWeakSequenceLinear
  CurrentWeakLimitOperations CurrentLoneFieldWeakLimit
  CurrentWeakSequenceLimit CurrentEvaluation
  CompactSummableMultivectorLinear EuclideanOpenDomainMeasure
  CurrentCoefficientNorms PartialFunctionBasic MeasureLpConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IterationIdentity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation UT:=(current_domain R n Full).
Local Notation KType:=(smooth_compact_set hNX Full).
Local Notation C:=(@current_space R h2 n Full hFull m).
Local Notation Next:=(@current_space R h2 n Full hFull m.+1).
Local Notation V:=(@current_vector_smooth_space R h2 n Full hFull m).
Local Notation vv:=(@current_vector_smooth_value R h2 n Full hFull m).
Local Notation W:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation value:=(@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation size:=(@compact_summable_multivector_size R h2 n m Full hFull).
Local Notation image:=(@compact_summable_multivector_current R h2 n m Full hFull).
Local Notation bd:=(@current_boundary R h2 n m Full hFull).
Local Notation M:=(@CurrentMass.value R h2 n m Full hFull).
Local Notation NextM:=(@CurrentMass.value R h2 n m.+1 Full hFull).
Local Notation N:=(@current_normal_mass R h2 n Full hFull m).
Local Notation F K:=(@current_flat_norm R h2 n m Full hFull K).
Local Notation flat K:=(@is_flat_current_supported_in R h2 n m Full hFull K).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Local Notation Smooth:=(@current_smoothing R h2 n m phi family hPhi hFamily).


Variables (K0:KType) (T0:C) (delta:R).
Variables (K:nat->KType) (T A:nat->C) (S:nat->Next)
  (epsilon:nat->R) (f:nat->V) (xi:nat->W).
Hypothesis hDelta:0<delta.
Hypothesis hIteration:@is_flat_smoothing_iteration R h2 n m phi family hPhi hFamily
  K0 T0 delta K T A S epsilon f xi.
Local Notation mu:=(@euclidean_open_domain_measure R n Full).
Local Notation VN:=(@current_vector_mass R h2 n m).

(** Source for [flat_smoothing_iteration_limit_identity]: the
    original infinite sums represent T exactly, Federer 4.1.18,
    p. 376. Weak convergence is applied only to actual original
    currents and tests; representation of T is the conclusion. *)
Theorem flat_smoothing_iteration_limit_identity (w:W) (Z:Next):
  converges_in_lp_norm mu VN 1
    (fun k=>partial_function_total (value (\sum_(j<k) xi j)))
    (partial_function_total (value w))->
  @is_current_weak_sequence_limit R h2 n m.+1 Full hFull
    (fun k=>\sum_(j<k) S j) Z->
  T0=image w+bd Z.
Proof.
move=>hLone hFilling.
have hField:=@current_lone_field_weak_limit R h2 n m Full hFull
  (fun k=>\sum_(j<k) xi j) w hLone.
have hBoundary:=@current_weak_limit_boundary R h2 n m Full hFull
  (fun k=>\sum_(j<k) S j) Z hFilling.
have hPair:=@current_weak_sequence_limit_linear R h2 n m Full hFull
  (fun k=>image (\sum_(j<k) xi j)) (fun k=>bd (\sum_(j<k) S j))
  (image w) (bd Z) 1 hField hBoundary.
have hPairSequence:
    (fun k=>1*:image (\sum_(j<k) xi j)+bd (\sum_(j<k) S j))=
    (fun k=>image (\sum_(j<k) xi j)+bd (\sum_(j<k) S j)).
  apply:funext=>k;by rewrite scale1r.
rewrite hPairSequence scale1r in hPair.
have hResidual:=@flat_smoothing_iteration_residual_weak_limit R h2 n m phi family
  hPhi hFamily K0 T0 delta K T A S epsilon f xi hDelta hIteration.
have hCombined:=@current_weak_sequence_limit_linear R h2 n m Full hFull
  T (fun k=>image (\sum_(j<k) xi j)+bd (\sum_(j<k) S j))
  0 (image w+bd Z) 1 hResidual hPair.
have hCombinedSequence:
    (fun k=>1*:T k+(image (\sum_(j<k) xi j)+bd (\sum_(j<k) S j)))=
    (fun k=>T k+(image (\sum_(j<k) xi j)+bd (\sum_(j<k) S j))).
  apply:funext=>k;by rewrite scale1r.
rewrite hCombinedSequence scale1r add0r in hCombined.
apply:(@current_values_extensional R h2 n m Full hFull)=>psi;symmetry.
apply:(@current_weak_limit_eventual_value R h2 n m Full hFull
  (fun k=>T k+(image (\sum_(j<k) xi j)+bd (\sum_(j<k) S j)))
  (image w+bd Z) psi (@current_value R h2 n Full hFull m T0 psi) 0 hCombined).
move=>k _;rewrite addrA.
by rewrite -(@flat_smoothing_iteration_prefix_identity R h2 n m phi family hPhi hFamily
  K0 T0 delta K T A S epsilon f xi hIteration k).
Qed.
End IterationIdentity.
