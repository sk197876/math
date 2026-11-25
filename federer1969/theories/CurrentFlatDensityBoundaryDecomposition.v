(** Federer (1969), 4.1.18, p. 376: the first
    stage of the original downward induction represents
    an arbitrary compact flat current as a summable-field
    current plus the boundary of a finite-mass flat current
    in C, the exact closed delta/2 tube of K. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces CurrentVectorSpaces
  CurrentBoundary NormalCurrentsUP CurrentMassSealed CurrentNormalMass
  CurrentFlatNorm FlatCurrentsUP SmoothCompactSet EuclideanClosedSupportTube
  CurrentFlatSmoothingBudgets CurrentSmoothingOperators
  CompactSummableMultivectors CompactSummableMultivectorDensity
  SmoothingKernelUP SmoothingDilationUP CurrentFlatSmoothingIterationExistence
  CurrentFlatSmoothingIterationSeries CurrentFlatSmoothingIterationIdentity
  CurrentCompactTubeIndex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DensityBoundaryDecomposition.
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


(** Source for [current_flat_density_boundary_decomposition]:
    the original infinite sums give T=D xi+boundary S,
    with support in C and joint cost at most F_K(T)+delta/2,
    Federer 4.1.18, p. 376. No mass or representation
    hypothesis on the original flat current is added. *)
Theorem current_flat_density_boundary_decomposition
    (K0:KType) (T0:C) (delta:R):
  flat K0 T0->0<delta->
  let C0:=@current_compact_closed_tube_index R n Full K0 (delta/2)
    (fun _ _=>Logic.I) in
  exists w:W,exists Z:Next,
    (forall x:UT,~smooth_compact_carrier C0 (set_val x)->value w x=0) /\
    @is_flat_current_supported_in R h2 n m.+1 Full hFull C0 Z /\
    T0=image w+bd Z /\
    ((size w)%:E+NextM Z<=F K0 T0+(delta/2)%:E)%E.
Proof.
move=>hFlat hDelta C0.
have[K [T [A [S [epsilon [f [xi hIteration]]]]]]]:=
  @flat_smoothing_iteration_exists R h2 n m phi family hPhi hFamily
    K0 T0 delta hFlat hDelta.
have[w [Z [hOff [hZFlat [hLone [hTail [hAE [hWeak [hMassTail hCost]]]]]]]]]:=
  @flat_smoothing_iteration_series_exists R h2 n m phi family hPhi hFamily
    K0 T0 delta K T A S epsilon f xi hDelta hIteration.
have hIdentity:=@flat_smoothing_iteration_limit_identity R h2 n m phi family hPhi hFamily
  K0 T0 delta K T A S epsilon f xi hDelta hIteration w Z hLone hWeak.
exists w,Z;split;first exact:hOff.
split;first exact:hZFlat.
split;[exact:hIdentity|exact:hCost].
Qed.
End DensityBoundaryDecomposition.
