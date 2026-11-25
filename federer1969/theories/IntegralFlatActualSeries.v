(** Federer (1969), 4.1.24, p. 382: the
    two chosen original rectifiable mass series have
    actual sums. Their current sum has every literal
    tail bound using exactly M(R_i)+M(S_i), as
    printed, without replacing those costs by a
    geometric majorant. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary CurrentMassSealed CurrentMassBasic
  CurrentMassConvergenceUP CurrentWeakSequenceLimit NonnegativeSum NonnegativeSequenceTail
  RectifiableCurrentApproximationUP RectifiableCurrentBasic IntegralCurrentClassesUP
  IntegralFlatSizeSealed IntegralFlatSeriesDecompositionUP IntegralFlatRectifiablePairSeries.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IntegralFlatActualSeries.
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
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation Rect:=(fun d=>@is_rectifiable_current_supported_in R h2 n d U hU K).
Local Notation IF:=(@is_integral_flat_current_supported_in R h2 n U hU m K).
Local Notation Size:=(@IntegralFlatSize.value R h2 n m U hU K).

(** Source for [integral_flat_actual_series_exists]: the
    original actual sums, their mass convergence and
    every exact chosen-cost tail in 4.1.24, p. 382.
    The resulting current may have infinite mass. *)
Theorem integral_flat_actual_series_exists (v A:nat->C) (B:nat->Next):
  @is_integral_flat_series_decomposition R h2 n m U hU K v A B->
  exists P:C,exists Q:Next,Rect m P /\Rect m.+1 Q /\
    @is_current_mass_sequence_limit R h2 n m U hU (fun k=>\sum_(i<k) A i) P /\
    @is_current_mass_sequence_limit R h2 n m.+1 U hU (fun k=>\sum_(i<k) B i) Q /\
    @is_current_weak_sequence_limit R h2 n m U hU (fun k=>\sum_(i<k) v i) (P+bd Q) /\
    forall k,exists hResidual:IF (P+bd Q-\sum_(i<k) v i),
      ((Size (P+bd Q-\sum_(i<k) v i) hResidual)%:E<=
        nonnegative_sequence_tail (fun i=>M m (A i)+M m.+1 (B i)) k)%E.
Proof.
move=>hData.
pose r:=fun i=>fine (M m (A i)).
pose s:=fun i=>fine (M m.+1 (B i)).
have hAValue i:0<=r i /\M m (A i)=(r i)%:E.
  have[c [hc hC]]:=@current_finite_mass_value R h2 n m U hU (A i)
    (@rectifiable_current_finite_mass R h2 n m U hU K (A i)
      (integral_flat_series_rectifiable_first hData i)).
  rewrite /r hC /=;split;[exact:hc|by []].
have hBValue i:0<=s i /\M m.+1 (B i)=(s i)%:E.
  have[c [hc hC]]:=@current_finite_mass_value R h2 n m.+1 U hU (B i)
    (@rectifiable_current_finite_mass R h2 n m.+1 U hU K (B i)
      (integral_flat_series_rectifiable_second hData i)).
  rewrite /s hC /=;split;[exact:hc|by []].
have hCostFunctions:(fun i=>(r i+s i)%:E)=(fun i=>M m (A i)+M m.+1 (B i))%E.
  by apply:funext=>i;rewrite EFinD -(hAValue i).2 -(hBValue i).2.
have hFinite:(nonnegative_sum setT (fun i=>(r i+s i)%:E)< +oo)%E.
  rewrite hCostFunctions;exact:integral_flat_series_cost_summable hData.
have hAUpper i:(M m (A i)<=(r i)%:E)%E by rewrite (hAValue i).2.
have hBUpper i:(M m.+1 (B i)<=(s i)%:E)%E by rewrite (hBValue i).2.
have[P [Q [hP [hQ [hPLimit [hQLimit [hJoint [hWeak hTail]]]]]]]]:=
  @integral_flat_rectifiable_pair_series_exists R h2 n m U hU K A B r s
    (integral_flat_series_rectifiable_first hData)
    (integral_flat_series_rectifiable_second hData)
    (fun i=>(hAValue i).1) (fun i=>(hBValue i).1) hFinite hAUpper hBUpper.
have hPrefix k:(\sum_(i<k) v i)=(\sum_(i<k) (A i+bd (B i))).
  apply:eq_bigr=>i _;exact:integral_flat_series_decomposition hData i.
have hFunctions:(fun k=>\sum_(i<k) v i)=(fun k=>\sum_(i<k) (A i+bd (B i))).
  apply:funext=>k;exact:hPrefix k.
exists P,Q;split;first exact:hP.
split;first exact:hQ.
split;first exact:hPLimit.
split;first exact:hQLimit.
split;first by rewrite hFunctions.
move=>k;rewrite hPrefix.
have[hResidual hBound]:=hTail k;exists hResidual.
by rewrite hCostFunctions in hBound.
Qed.
End IntegralFlatActualSeries.
