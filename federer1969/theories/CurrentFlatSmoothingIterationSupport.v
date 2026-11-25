(** Federer (1969), 4.1.18, p. 376: every
    original iterative support is contained in the closed
    delta/2 neighbourhood C of K. Use the literal nested
    closed tubes and the original numerical radius sum.
    The empty compact set needs no selected point. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces CurrentVectorSpaces
  CurrentBoundary NormalCurrentsUP CurrentMassSealed CurrentNormalMass
  CurrentFlatNorm FlatCurrentsUP SmoothCompactSet EuclideanClosedSupportTube
  CurrentFlatSmoothingBudgets CurrentSmoothingOperators
  CompactSummableMultivectors CompactSummableMultivectorDensity
  SmoothingKernelUP SmoothingDilationUP CurrentFlatSmoothingIterationUP
  CurrentCompactTubeIndex GeometricErrorBudget CosetLoneIntegralExistence
  NonnegativeSum NonnegativeSumRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IterationSupport.
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
Local Notation r:=(flat_smoothing_radius_budget delta).
Local Notation p:=(fun k=>\sum_(j<k) r j).
Local Notation C0:=(@current_compact_closed_tube_index R n Full K0 (delta/2)
  (fun _ _=>Logic.I)).

(** Source for [flat_smoothing_iteration_radius_prefix]: each
    original finite radius sum is at most delta/2,
    Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_iteration_radius_prefix k:p k<=delta/2.
Proof.
have hr j:0<=r j:=ltW (@flat_smoothing_budgets_positive R delta j hDelta).1.
have hPrefix:((p k)%:E<=nonnegative_sum setT (fun j=>(r j)%:E))%E.
  rewrite -(@nat_prefix_nonnegative_sum R r k hr).
  apply:nonnegative_sum_subset;by move=>j _.
have hBound:=@flat_smoothing_radius_total R delta hDelta.
by have h:=le_trans hPrefix hBound;rewrite lee_fin in h.
Qed.

(** Source for [flat_smoothing_iteration_nested_support]: the
    exact iterated K_i lie in the tube of radius equal to
    the finite sum of their allowances, Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_iteration_nested_support k:
  smooth_compact_carrier (K k) `<=`
    @euclidean_closed_support_tube R n (smooth_compact_carrier K0) (p k).
Proof.
elim:k=>[|k ih].
- rewrite (flat_smoothing_iteration_initial hIteration).1 /p big_ord0.
  exact:(@euclidean_closed_support_tube_includes R n (smooth_compact_carrier K0) 0 (lexx 0)).
- rewrite (flat_smoothing_iteration_tubes hIteration k).
  move=>x hx.
  have hInner:=@euclidean_closed_support_tube_mono R n
    (smooth_compact_carrier (K k))
    (@euclidean_closed_support_tube R n (smooth_compact_carrier K0) (p k))
    (r k) (r k) ih (lexx (r k)) x hx.
  have hOuter:=@euclidean_closed_support_tube_nested R n
    (smooth_compact_carrier K0) (p k) (r k) x hInner.
  by rewrite /p big_ord_recr /=.
Qed.

(** Source for [flat_smoothing_iteration_common_support]: each
    K_i is contained in the exact original C, not in a
    separately enlarged compact set, Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_iteration_common_support k:
  smooth_compact_carrier (K k) `<=` smooth_compact_carrier C0.
Proof.
move=>x hx.
apply:(@euclidean_closed_support_tube_mono R n (smooth_compact_carrier K0)
  (smooth_compact_carrier K0) (p k) (delta/2) (fun y hy=>hy)
  (flat_smoothing_iteration_radius_prefix k) x).
exact:flat_smoothing_iteration_nested_support hx.
Qed.

(** Source for [flat_smoothing_iteration_fields_common_carrier]:
    every actual xi_i vanishes off the same original C,
    Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_iteration_fields_common_carrier k x:
  ~smooth_compact_carrier C0 (set_val x)->value (xi k) x=0.
Proof.
move=>hx;apply:(flat_smoothing_iteration_coefficients hIteration k).2.2.1.
move=>hy;apply:hx;exact:flat_smoothing_iteration_common_support hy.
Qed.

(** Source for [flat_smoothing_iteration_fillings_common_carrier]:
    the actual S_i are normal currents supported in C,
    as used in their infinite sum, Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_iteration_fillings_common_carrier k:
  @normal_currents_supported_in R h2 n Full hFull m.+1 C0 (S k).
Proof.
have hS:=(flat_smoothing_iteration_normal hIteration k).2.
split;first exact:hS.1.
move=>x hx;apply:flat_smoothing_iteration_common_support.
exact:hS.2 x hx.
Qed.
End IterationSupport.
