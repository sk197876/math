(** Federer (1969), 4.1.24, p. 382: every
    original flat current is R+boundary S with
    R and S both flat, both of finite mass,
    and both in the original K. Decompose the
    preceding same-K normal series by the already
    attained normal minima and sum its actual mass
    costs. M(T) itself may be infinite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary CurrentMassSealed CurrentMassBasic
  CompactRepresentedCurrentMass NormalCurrentsUP FlatCurrentsUP CurrentFlatNorm
  CurrentWeakSequenceLimit CurrentWeakLimitOperations CurrentWeakSequenceLinear
  CurrentSummableNormalSeries NonnegativeSum NonnegativeSequenceTail
  ModuleQuotient FlatCurrentClosure FlatCurrentBoundary
  FlatCurrentNormalSeriesUP FlatCurrentNormalSeriesExistence NormalCurrentFlatMinimumPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FlatCurrentFiniteMassDecomposition.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation M:=(fun d=>@CurrentMass.value R h2 n d U hU).
Local Notation F:=(@current_flat_norm R h2 n m U hU K).
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation Flat:=(fun d=>@is_flat_current_supported_in R h2 n d U hU K).
Local Notation Normal:=(fun d=>@normal_currents_supported_in R h2 n U hU d K).

(** Source for [flat_normal_series_finite_mass_decomposition]:
    the actual normal series gives a pair of
    finite-mass flat sums in exactly the same K,
    the first final paragraph of 4.1.24, p. 382. *)
Theorem flat_normal_series_finite_mass_decomposition (T:C)
    (v:nat->C) (a:nat->R):
  @is_flat_current_normal_series R h2 n m U hU K T v a->
  exists P:C,exists Q:Next,Flat m P /\Flat m.+1 Q /\
    (M m P< +oo)%E /\(M m.+1 Q< +oo)%E /\T= P+bd Q.
Proof.
move=>hSeries.
have hChoice i:exists A:C,exists B:Next,
    Normal m A /\Normal m.+1 B /\v i=A+bd B /\(M m A+M m.+1 B=F (v i))%E.
  exact:normal_current_flat_minimum_pair (flat_current_normal_series_normal hSeries i).
have[A hChoices]:=choice hChoice.
have[B hData]:=choice hChoices.
have hANormal i:Normal m (A i):=(hData i).1.
have hBNormal i:Normal m.+1 (B i):=(hData i).2.1.
pose r:=fun i=>fine (M m (A i)).
pose s:=fun i=>fine (M m.+1 (B i)).
have hAValue i:0<=r i /\M m (A i)=(r i)%:E.
  have hFinite:=@compact_represented_current_finite_mass R h2 n m U hU (A i)
    (hANormal i).1.1.1 (hANormal i).1.2.
  have[c [hc hC]]:=@current_finite_mass_value R h2 n m U hU (A i) hFinite.
  rewrite /r hC /=;split;[exact:hc|by []].
have hBValue i:0<=s i /\M m.+1 (B i)=(s i)%:E.
  have hFinite:=@compact_represented_current_finite_mass R h2 n m.+1 U hU (B i)
    (hBNormal i).1.1.1 (hBNormal i).1.2.
  have[c [hc hC]]:=@current_finite_mass_value R h2 n m.+1 U hU (B i) hFinite.
  rewrite /s hC /=;split;[exact:hc|by []].
have hJoint i:((r i+s i)%:E<=(a i)%:E)%E.
  rewrite EFinD -(hAValue i).2 -(hBValue i).2 (hData i).2.2.2.
  exact:flat_current_normal_series_bound hSeries i.
have hRFinite:(nonnegative_sum setT (fun i=>(r i)%:E)< +oo)%E.
  apply:(le_lt_trans _ (flat_current_normal_series_summable hSeries)).
  apply:nonnegative_sum_mono=>i _;apply:(le_trans _ (hJoint i)).
  rewrite lee_fin lerDl;exact:(hBValue i).1.
have hSFinite:(nonnegative_sum setT (fun i=>(s i)%:E)< +oo)%E.
  apply:(le_lt_trans _ (flat_current_normal_series_summable hSeries)).
  apply:nonnegative_sum_mono=>i _;apply:(le_trans _ (hJoint i)).
  rewrite lee_fin lerDr;exact:(hAValue i).1.
have hAUpper i:(M m (A i)<=(r i)%:E)%E by rewrite (hAValue i).2.
have hBUpper i:(M m.+1 (B i)<=(s i)%:E)%E by rewrite (hBValue i).2.
have[P [hPFlat [hPWeak hPTail]]]:=@current_summable_normal_series_exists
  R h2 n m U hU K A r hANormal (fun i=>(hAValue i).1) hRFinite
  hAUpper.
have[Q [hQFlat [hQWeak hQTail]]]:=@current_summable_normal_series_exists
  R h2 n m.+1 U hU K B s hBNormal (fun i=>(hBValue i).1) hSFinite
  hBUpper.
have hPMassFinite:(M m P< +oo)%E.
  have h:=hPTail 0%N;rewrite big_ord0 subr0 in h.
  apply:(le_lt_trans (le_trans h _) hRFinite).
  apply:nonnegative_sum_subset=>i _;exact:Logic.I.
have hQMassFinite:(M m.+1 Q< +oo)%E.
  have h:=hQTail 0%N;rewrite big_ord0 subr0 in h.
  apply:(le_lt_trans (le_trans h _) hSFinite).
  apply:nonnegative_sum_subset=>i _;exact:Logic.I.
have hBoundaryWeak:=@current_weak_limit_boundary R h2 n m U hU
  (fun k=>\sum_(i<k) B i) Q hQWeak.
have hWeak:=@current_weak_sequence_limit_linear R h2 n m U hU
  (fun k=>\sum_(i<k) A i) (fun k=>bd (\sum_(i<k) B i)) P (bd Q) 1 hPWeak hBoundaryWeak.
rewrite !scale1r in hWeak.
have hPrefix k:(\sum_(i<k) v i)=(\sum_(i<k) A i)+bd (\sum_(i<k) B i).
  rewrite linear_sum -big_split.
  apply:eq_bigr=>i _;exact:(hData i).2.2.1.
have hFunctions:(fun k=>\sum_(i<k) v i)=
    (fun k=>(\sum_(i<k) A i)+bd (\sum_(i<k) B i)).
  apply:funext=>k;exact:hPrefix k.
have hScale:(fun k=>(\sum_(i<k) A i)+bd (\sum_(i<k) B i))=
    (fun k=>1*:(\sum_(i<k) A i)+bd (\sum_(i<k) B i)).
  by apply:funext=>k;rewrite scale1r.
have hActualWeak:@is_current_weak_sequence_limit R h2 n m U hU (fun k=>\sum_(i<k) v i) (P+bd Q).
  rewrite hFunctions hScale;exact:hWeak.
have hEqual:=@current_weak_sequence_limit_unique R h2 n m U hU
  (fun k=>\sum_(i<k) v i) T (P+bd Q) (flat_current_normal_series_limit hSeries) hActualWeak.
exists P,Q;split;first exact:hPFlat.
split;first exact:hQFlat.
split;first exact:hPMassFinite.
split;[exact:hQMassFinite|exact:hEqual].
Qed.

(** Source for [flat_current_finite_mass_decomposition]: every
    original flat current admits the stated finite-mass
    pair in the same original compact K, 4.1.24,
    p. 382. No finite input mass is assumed. *)
Theorem flat_current_finite_mass_decomposition (T:C):
  Flat m T->exists P:C,exists Q:Next,Flat m P /\Flat m.+1 Q /\
    (M m P< +oo)%E /\(M m.+1 Q< +oo)%E /\T= P+bd Q.
Proof.
move=>hT;have[v [a hSeries]]:=@flat_current_normal_series_exists R h2 n m U hU K T hT.
exact:flat_normal_series_finite_mass_decomposition hSeries.
Qed.

(** Source for [flat_current_finite_mass_decomposition_iff]: the
    full printed set equality in 4.1.24, p. 382,
    with both directions and exactly the same K.
    The reverse implication follows from the original
    flat group and boundary laws. *)
Theorem flat_current_finite_mass_decomposition_iff (T:C):
  Flat m T<->exists P:C,exists Q:Next,Flat m P /\Flat m.+1 Q /\
    (M m P< +oo)%E /\(M m.+1 Q< +oo)%E /\T= P+bd Q.
Proof.
split;first exact:flat_current_finite_mass_decomposition.
move=>[P [Q [hP [hQ [hPMass [hQMass ->]]]]]].
apply:(@subspace_add R C (@flat_current_subspace R h2 n m U hU K));first exact:hP.
exact:(@flat_current_boundary_supported R h2 n m U hU K Q hQ).
Qed.
End FlatCurrentFiniteMassDecomposition.
