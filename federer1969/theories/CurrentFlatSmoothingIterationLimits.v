(** Federer (1969), 4.1.18, p. 376: the original
    finite-prefix identity and the vanishing flat residuals.
    Every current is evaluated on its original compact tests;
    no finite mass of the residuals is used. *)
From mathcomp Require Import all_boot all_order all_algebra lra ring
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentDomain CurrentSpaces CurrentVectorSpaces
  CurrentBoundary NormalCurrentsUP CurrentMassSealed CurrentNormalMass
  CurrentFlatNorm FlatCurrentsUP SmoothCompactSet EuclideanClosedSupportTube
  CurrentFlatSmoothingBudgets CurrentSmoothingOperators
  CompactSummableMultivectors CompactSummableMultivectorDensity
  SmoothingKernelUP SmoothingDilationUP CurrentFlatSmoothingIterationUP
  CurrentFlatSmoothingIterationSupport CurrentCompactTubeIndex
  CurrentFlatCompactMonotone CurrentFlatFiniteArithmetic
  FlatCurrentFinite CurrentFlatSequenceLimitUP CurrentFlatSequenceLimits
  CurrentWeakSequenceLimit CurrentPointEvaluation CurrentEvaluation
  CompactSummableMultivectorLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IterationLimits.
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
Local Notation C0:=(@current_compact_closed_tube_index R n Full K0 (delta/2)
  (fun _ _=>Logic.I)).
Local Notation D:=(@compact_summable_multivector_current_hom R h2 n m Full hFull).

(** Source for [flat_smoothing_iteration_prefix_identity]: the
    original identity T=T_i+sum_(j<=i)(D xi_j+boundary S_j),
    Federer 4.1.18, p. 376. The empty prefix is retained. *)
Theorem flat_smoothing_iteration_prefix_identity k:
  T0=T k+image (\sum_(j<k) xi j)+bd (\sum_(j<k) S j).
Proof.
elim:k=>[|k ih].
- rewrite (flat_smoothing_iteration_initial hIteration).2 !big_ord0.
  change (T0=T0+D 0+bd 0).
  by rewrite !linear0 !addr0.
- apply:(@current_values_extensional R h2 n m Full hFull)=>psi.
  pose E:=@current_point_evaluation R h2 n m Full hFull psi.
  have hOld:=congr1 E ih.
  have hNext:=congr1 E (flat_smoothing_iteration_recurrence hIteration k).
  change (E T0=E (T k+D (\sum_(j<k) xi j)+bd (\sum_(j<k) S j))) in hOld.
  change (E (T k.+1)=E (T k-D (xi k)-bd (S k))) in hNext.
  rewrite !(linD (hom_linear E)) in hOld.
  rewrite !(linB (hom_linear E)) in hNext.
  change (E T0=E (T k.+1+D (\sum_(j<k.+1) xi j)+bd (\sum_(j<k.+1) S j))).
  rewrite !big_ord_recr !(linD (hom_linear D)) !(linD (hom_linear bd))
    !(linD (hom_linear E)).
  cbn beta in hOld, hNext |- *;lra.
Qed.

(** Source for [flat_smoothing_iteration_residual_flat_limit]:
    the actual T_i converge to zero in the common F_C
    seminorm, Federer 4.1.18, p. 376. No finite mass
    of any T_i is assumed or inferred from this statement. *)
Theorem flat_smoothing_iteration_residual_flat_limit:
  @is_current_flat_sequence_limit R h2 n m Full hFull C0 T 0.
Proof.
move=>eta hEta.
have[k hk]:=@flat_smoothing_price_small R delta hDelta eta hEta.
exists k.+1=>j hJ.
case:j hJ=>[|j] hJ;first by rewrite leqn0 in hJ.
have hKJ:(k<=j)%N:=hJ.
have hSmall:=flat_smoothing_iteration_residuals hIteration j.
have hInside:=@flat_smoothing_iteration_common_support R h2 n m phi family
  hPhi hFamily K0 T0 delta K T A S epsilon f xi hDelta hIteration j.+1.
have hBound:=@current_flat_compact_monotone R h2 n m Full hFull
  (K j.+1) C0 hInside (T j.+1).
have hPositive:(F C0 (T j.+1)<eta%:E)%E.
  apply:(le_lt_trans hBound).
  apply:(lt_trans hSmall);rewrite lte_fin;exact:hk.
have hFinite:(F C0 (T j.+1)< +oo)%E:=lt_trans hPositive (ltry eta).
rewrite sub0r (@current_flat_finite_negate R h2 n m Full hFull C0 (T j.+1) hFinite).
exact:hPositive.
Qed.

(** Source for [flat_smoothing_iteration_residual_weak_limit]:
    original flat convergence gives convergence of every
    compact-test value of T_i to zero, supporting the limit
    identity in Federer 4.1.18, p. 376. *)
Theorem flat_smoothing_iteration_residual_weak_limit:
  @is_current_weak_sequence_limit R h2 n m Full hFull T 0.
Proof.
exact:(@current_flat_sequence_limit_weak R h2 n m Full hFull C0 T 0
  flat_smoothing_iteration_residual_flat_limit).
Qed.
End IterationLimits.
