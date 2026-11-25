(** Federer (1969), 4.1.18, p. 376: the actual
    costs in the original iteration form a summable series,
    bounded by F_K(T)+delta/2. The previous residual is
    retained as a nonnegative potential; the radius budgets
    telescope. No finite mass of T is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra lra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentDomain CurrentSpaces CurrentVectorSpaces
  CurrentBoundary NormalCurrentsUP CurrentMassSealed CurrentNormalMass
  CurrentFlatNorm FlatCurrentsUP SmoothCompactSet EuclideanClosedSupportTube
  CurrentFlatSmoothingBudgets CurrentSmoothingOperators
  CompactSummableMultivectors CompactSummableMultivectorDensity
  SmoothingKernelUP SmoothingDilationUP CurrentFlatSmoothingIterationUP
  FlatCurrentFinite CurrentFlatDualSeminormBasic CurrentMassBasic
  CompactRepresentedCurrentMass CompactSummableFieldLaws
  NonnegativeSum NonnegativeRealSeriesTelescoping GeometricErrorBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IterationCost.
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
Local Notation c:=(fun k=>fine (F (K k) (T k))).
Local Notation s:=(fun k=>fine (NextM (S k))).
Local Notation a:=(fun k=>size (xi k)+s k).

(** Source for [flat_smoothing_iteration_flat_value]: the
    residual flat norms have actual finite nonnegative values,
    supporting the numerical sum in Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_iteration_flat_value k:
  0<=c k /\F (K k) (T k)=(c k)%:E.
Proof.
have hFlat:=flat_smoothing_iteration_flat hIteration k.
have hFinite:=@flat_current_supported_finite R h2 n m Full hFull (K k) (T k) hFlat.
have hNonnegative:(0<=F (K k) (T k))%E:=
  @current_flat_dual_nonnegative R h2 n m Full hFull (K k)
    (@current_value R h2 n Full hFull m (T k)).
have hNumber:F (K k) (T k) \is a fin_num by rewrite (ge0_fin_numE hNonnegative).
have hValue:F (K k) (T k)=(c k)%:E by rewrite fineK.
split=>//;by rewrite hValue lee_fin in hNonnegative.
Qed.

(** Source for [flat_smoothing_iteration_filling_value]: the
    chosen normal S_i have finite actual masses, supporting
    the original summation in Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_iteration_filling_value k:
  0<=s k /\NextM (S k)=(s k)%:E.
Proof.
have hNormal:=(flat_smoothing_iteration_normal hIteration k).2.1.
have hFinite:=@compact_represented_current_finite_mass R h2 n m.+1 Full hFull
  (S k) hNormal.1.1 hNormal.2.
have hNonnegative:=@current_mass_nonnegative R h2 n m.+1 Full hFull (S k).
have hNumber:NextM (S k) \is a fin_num by rewrite (ge0_fin_numE hNonnegative).
have hValue:NextM (S k)=(s k)%:E by rewrite fineK.
split=>//;by rewrite hValue lee_fin in hNonnegative.
Qed.

(** Source for [flat_smoothing_iteration_cost_nonnegative]:
    every original field-plus-filling cost is nonnegative,
    Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_iteration_cost_nonnegative k:0<=a k.
Proof.
apply:addr_ge0;last exact:(flat_smoothing_iteration_filling_value k).1.
exact:(@real_seminorm_nonnegative R W size
  (@compact_summable_multivector_size_laws R h2 n m Full hFull) (xi k)).
Qed.

(** Source for [flat_smoothing_iteration_cost_step]: the
    original price and residual bounds imply the telescoping
    potential estimate, Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_iteration_cost_step k:
  a k+(c k.+1)<=c k+flat_smoothing_radius_budget delta k.
Proof.
have hPrice:=flat_smoothing_iteration_prices hIteration k.
have hResidual:=flat_smoothing_iteration_residuals hIteration k.
rewrite (flat_smoothing_iteration_filling_value k).2
  (flat_smoothing_iteration_flat_value k).2 -!EFinD lte_fin in hPrice.
rewrite (flat_smoothing_iteration_flat_value k.+1).2 lte_fin in hResidual.
have hRatio:=(@flat_smoothing_budget_ratios R delta k).2.
have h:=lerD (ltW hPrice) (ltW hResidual).
change (is_true (a k+c k.+1<=c k+flat_smoothing_price_budget delta k+
  flat_smoothing_price_budget delta k)) in h.
lra.
Qed.

(** Source for [flat_smoothing_iteration_cost_sum]: the exact
    original numerical series is bounded by F_K(T)+delta/2,
    Federer 4.1.18, p. 376. This proves summability, rather
    than assuming that either original T or its boundary
    has finite mass. *)
Theorem flat_smoothing_iteration_cost_sum:
  (nonnegative_sum setT (fun k=>(a k)%:E)<=F K0 T0+(delta/2)%:E)%E.
Proof.
pose t:=fun k=>c k+geometric_error_tail delta k.
have hT k:0<=t k:=addr_ge0 (flat_smoothing_iteration_flat_value k).1
  (@geometric_error_tail_nonnegative R delta k (ltW hDelta)).
have hStep k:a k<=t k-t k.+1.
  have h:=flat_smoothing_iteration_cost_step k.
  rewrite /flat_smoothing_radius_budget /geometric_error_budget in h.
  change (a k<=c k+geometric_error_tail delta k-
    (c k.+1+geometric_error_tail delta k.+1)).
  cbn beta in h |- *;lra.
have hBound:=@nonnegative_real_series_telescoping_bound R a t
  flat_smoothing_iteration_cost_nonnegative hT hStep.
have hInitial:=(flat_smoothing_iteration_initial hIteration).
have hValue:F K0 T0=(c 0)%:E.
  have h:=(flat_smoothing_iteration_flat_value 0).2.
  rewrite -hInitial.1 -hInitial.2;exact:h.
rewrite hValue -EFinD.
change (nonnegative_sum setT (fun k=>(a k)%:E)<=
  (c 0+delta/2)%:E)%E.
by move:hBound;rewrite /t /geometric_error_tail expr0 mulr1.
Qed.
End IterationCost.
