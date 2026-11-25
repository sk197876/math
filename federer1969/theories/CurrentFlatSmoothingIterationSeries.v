(** Federer (1969), 4.1.18, p. 376: the two
    original infinite sums exist with common compact carrier C.
    Sum the field sizes and filling masses separately; their
    sum is the actual original pair cost. This preserves the
    sharp total estimate instead of doubling it. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology boolp functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces CurrentVectorSpaces
  CurrentBoundary NormalCurrentsUP CurrentMassSealed CurrentNormalMass
  CurrentFlatNorm FlatCurrentsUP FlatCurrentFinite SmoothCompactSet EuclideanClosedSupportTube
  CurrentFlatSmoothingBudgets CurrentSmoothingOperators
  CompactSummableMultivectors CompactSummableMultivectorDensity
  SmoothingKernelUP SmoothingDilationUP CurrentFlatSmoothingIterationUP
  CurrentFlatSmoothingIterationCost CurrentFlatSmoothingIterationSupport
  CurrentCompactTubeIndex CurrentVectorCompleteness
  CompactSummableFieldSeriesPointwise CompactSummableFieldLaws
  CurrentSummableNormalSeries CurrentWeakSequenceLimit
  EuclideanOpenDomainMeasure CurrentCoefficientNorms
  NonnegativeSum NonnegativeSumAdd NonnegativeSumNatPrefix NonnegativeSequenceTail
  NonnegativeRealSeriesTails IsotropyGroupTopology
  MeasureAlmostUP PartialFunctionBasic PartialFunctionLimitUP MeasureLpConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IterationSeries.
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
Local Notation mu:=(@euclidean_open_domain_measure R n Full).
Local Notation hm:=(proj1 (@euclidean_open_domain_measure_laws R n Full hFull)).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation b:=(fun k=>size (xi k)).
Local Notation s:=(fun k=>fine (NextM (S k))).
Local Notation a:=(fun k=>b k+s k).
Local Notation Ib:=(nonnegative_sum setT (fun k=>(b k)%:E)).
Local Notation Is:=(nonnegative_sum setT (fun k=>(s k)%:E)).
Local Notation Ia:=(nonnegative_sum setT (fun k=>(a k)%:E)).

(** Source for [flat_smoothing_iteration_separate_sums]: the
    two actual cost series are finite and their sum is the
    original combined series, Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_iteration_separate_sums:
  (Ib< +oo)%E /\(Is< +oo)%E /\Ia=(Ib+Is)%E.
Proof.
have hb k:0<=b k:=real_seminorm_nonnegative
  (@compact_summable_multivector_size_laws R h2 n m Full hFull) (xi k).
have hs k:0<=s k:=(@flat_smoothing_iteration_filling_value R h2 n m
  phi family hPhi hFamily K0 T0 delta K T A S epsilon f xi hIteration k).1.
have hCost:=@flat_smoothing_iteration_cost_sum R h2 n m phi family hPhi hFamily
  K0 T0 delta K T A S epsilon f xi hDelta hIteration.
have hFlat0:=flat_smoothing_iteration_flat hIteration 0.
rewrite (flat_smoothing_iteration_initial hIteration).1
  (flat_smoothing_iteration_initial hIteration).2 in hFlat0.
have hFiniteF:=@flat_current_supported_finite R h2 n m Full hFull K0 T0 hFlat0.
have hFiniteIa:(Ia< +oo)%E:=le_lt_trans hCost (lte_add_pinfty hFiniteF (ltry (delta/2))).
have hIb:(Ib<=Ia)%E.
  apply:nonnegative_sum_mono=>k _;rewrite lee_fin lerDl;exact:(hs k).
have hIs:(Is<=Ia)%E.
  apply:nonnegative_sum_mono=>k _;rewrite lee_fin lerDr;exact:(hb k).
split;first exact:le_lt_trans hIb hFiniteIa.
split;first exact:le_lt_trans hIs hFiniteIa.
have hTerms:(fun k=>(a k)%:E)=
    (fun k=>(b k)%:E+(s k)%:E)%E by apply:funext=>k;rewrite EFinD.
rewrite hTerms;apply:nonnegative_sum_add;move=>k _;rewrite lee_fin;[exact:hb|exact:hs].
Qed.

(** Source for [flat_smoothing_iteration_series_exists]: actual
    xi=sum xi_i and S=sum S_i with the printed common C,
    original L1 and weak convergence, and sharp joint cost,
    Federer 4.1.18, p. 376. The whole field series agrees
    almost everywhere with its chosen original representative. *)
Theorem flat_smoothing_iteration_series_exists:
  exists w:W,exists Z:Next,
    (forall x:UT,~smooth_compact_carrier C0 (set_val x)->value w x=0) /\
    @is_flat_current_supported_in R h2 n m.+1 Full hFull C0 Z /\
    converges_in_lp_norm mu VN 1
      (fun k=>partial_function_total (value (\sum_(j<k) xi j)))
      (partial_function_total (value w)) /\
    (forall k,size (w-\sum_(j<k) xi j)<=nonnegative_real_series_tail b k) /\
    measure_almost_everywhere mu (partial_function_limit_locus
      (fun k=>partial_function_total (fun x:UT=>
        (value (\sum_(j<k) xi j) x:real_norm_metric_space hVN)))
      (partial_function_total (fun x:UT=>(value w x:real_norm_metric_space hVN)))) /\
    @is_current_weak_sequence_limit R h2 n m.+1 Full hFull
      (fun k=>\sum_(j<k) S j) Z /\
    (forall k,(NextM (Z-\sum_(j<k) S j)<=
      nonnegative_sequence_tail (fun j=>(s j)%:E) k)%E) /\
    ((size w)%:E+NextM Z<=F K0 T0+(delta/2)%:E)%E.
Proof.
have hSums:=flat_smoothing_iteration_separate_sums.
have hb k:0<=b k:=real_seminorm_nonnegative
  (@compact_summable_multivector_size_laws R h2 n m Full hFull) (xi k).
have hs k:0<=s k:=(@flat_smoothing_iteration_filling_value R h2 n m
  phi family hPhi hFamily K0 T0 delta K T A S epsilon f xi hIteration k).1.
pose Crel:set UT:=set_val @^-1` smooth_compact_carrier C0.
have hCrel:compact Crel.
  exact:(@set_type_compact_preimage (real_norm_metric_space hNX) Full
    (smooth_compact_carrier C0) (smooth_compact_is_compact C0)
    (smooth_compact_in_domain C0)).
have hOff k x:~Crel x->value (xi k) x=0.
  exact:(@flat_smoothing_iteration_fields_common_carrier R h2 n m phi family
    hPhi hFamily K0 T0 delta K T A S epsilon f xi hDelta hIteration k x).
have[w [hWOff [hLone [hTail hPointwise]]]]:=
  @compact_summable_field_pointwise_series R UT (exterior_power X m) VN hVN
    (@current_multivector_mass_complete R h2 n m) mu hm xi b Crel hCrel
    hb hSums.1 (fun k=>lexx (b k)) hOff.
have hNormals k:=@flat_smoothing_iteration_fillings_common_carrier
  R h2 n m phi family hPhi hFamily K0 T0 delta K T A S epsilon f xi
  hDelta hIteration k.
have hMass k:(NextM (S k)<=(s k)%:E)%E.
  rewrite (@flat_smoothing_iteration_filling_value R h2 n m phi family hPhi hFamily
    K0 T0 delta K T A S epsilon f xi hIteration k).2;exact:lexx.
have[Z [hZFlat [hZWeak hZTail]]]:=@current_summable_normal_series_exists
  R h2 n m.+1 Full hFull C0 S s hNormals hs hSums.2.1 hMass.
have hbE k:(0<=(b k)%:E)%E by rewrite lee_fin;exact:hb.
have hsE k:(0<=(s k)%:E)%E by rewrite lee_fin;exact:hs.
have hWSize:((size w)%:E<=Ib)%E.
  have h:=hTail 0;rewrite big_ord0 subr0 in h.
  have hZero:=@nonnegative_sequence_prefix_tail R (fun k=>(b k)%:E) 0
    hbE.
  rewrite nonnegative_sum_nat_prefix_zero add0e in hZero.
  rewrite hZero (@nonnegative_real_series_tail_value R b hSums.1 0) lee_fin.
  exact:h.
have hZMass:(NextM Z<=Is)%E.
  have h:=hZTail 0;rewrite big_ord0 subr0 in h.
  have hZero:=@nonnegative_sequence_prefix_tail R (fun k=>(s k)%:E) 0
    hsE.
  rewrite nonnegative_sum_nat_prefix_zero add0e in hZero.
  by rewrite -hZero in h.
have hTotal:((size w)%:E+NextM Z<=F K0 T0+(delta/2)%:E)%E.
  apply:(le_trans (leeD hWSize hZMass)).
  rewrite -hSums.2.2.
  exact:(@flat_smoothing_iteration_cost_sum R h2 n m phi family hPhi hFamily
    K0 T0 delta K T A S epsilon f xi hDelta hIteration).
exists w,Z;repeat split=>//.
Qed.
End IterationSeries.
