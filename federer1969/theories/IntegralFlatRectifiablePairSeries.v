(** Federer (1969), 4.1.24, p. 382: sum
    both original rectifiable decomposition series with
    one common K. Their actual mass limits give
    an integral-flat current. Preserve the joint total
    cost and every literal chosen-cost tail with
    coefficient one; do not replace the two original
    series by a normal-mass convergence assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary CurrentMassSealed
  CurrentMassConvergenceUP CurrentWeakSequenceLimit CurrentWeakLimitOperations CurrentWeakSequenceLinear
  NonnegativeSum NonnegativeSumAdd NonnegativeSequenceTail
  RectifiableCurrentApproximationUP RectifiableCurrentFiniteSums RectifiableCurrentMassSeries
  IntegralCurrentClassesUP IntegralFlatSizeUP IntegralFlatSizeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IntegralFlatRectifiablePairSeries.
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

(** Source for [integral_flat_rectifiable_pair_series_exists]: the
    full original construction from two summable mass
    series, retaining every chosen nonnegative coefficient
    and the exact common compact K, 4.1.24, p. 382. *)
Theorem integral_flat_rectifiable_pair_series_exists
    (A:nat->C) (B:nat->Next) (a b:nat->R):
  (forall i,Rect m (A i))->(forall i,Rect m.+1 (B i))->
  (forall i,0<=a i)->(forall i,0<=b i)->
  (nonnegative_sum setT (fun i=>(a i+b i)%:E)< +oo)%E->
  (forall i,(M m (A i)<=(a i)%:E)%E)->
  (forall i,(M m.+1 (B i)<=(b i)%:E)%E)->
  exists P:C,exists Q:Next,Rect m P /\Rect m.+1 Q /\
    @is_current_mass_sequence_limit R h2 n m U hU (fun k=>\sum_(i<k) A i) P /\
    @is_current_mass_sequence_limit R h2 n m.+1 U hU (fun k=>\sum_(i<k) B i) Q /\
    (M m P+M m.+1 Q<=nonnegative_sum setT (fun i=>(a i+b i)%:E))%E /\
    @is_current_weak_sequence_limit R h2 n m U hU
      (fun k=>\sum_(i<k) (A i+bd (B i))) (P+bd Q) /\
    forall k,exists hResidual:IF (P+bd Q-\sum_(i<k) (A i+bd (B i))),
      ((Size (P+bd Q-\sum_(i<k) (A i+bd (B i))) hResidual)%:E<=
        nonnegative_sequence_tail (fun i=>(a i+b i)%:E) k)%E.
Proof.
move=>hA hB ha hb hFinite hMassA hMassB.
have hAFull:(nonnegative_sum setT (fun i=>(a i)%:E)< +oo)%E.
  apply:(le_lt_trans _ hFinite);apply:nonnegative_sum_mono=>i _.
  rewrite lee_fin lerDl;exact:hb i.
have hBFull:(nonnegative_sum setT (fun i=>(b i)%:E)< +oo)%E.
  apply:(le_lt_trans _ hFinite);apply:nonnegative_sum_mono=>i _.
  rewrite lee_fin lerDr;exact:ha i.
have[P [hP [hPLimit [hPWeak hPTail]]]]:=@rectifiable_current_mass_series_exists
  R h2 n m U hU K A a hA ha hAFull hMassA.
have[Q [hQ [hQLimit [hQWeak hQTail]]]]:=@rectifiable_current_mass_series_exists
  R h2 n m.+1 U hU K B b hB hb hBFull hMassB.
have hTailAdd k:
    nonnegative_sequence_tail (fun i=>(a i+b i)%:E) k=
      (nonnegative_sequence_tail (fun i=>(a i)%:E) k+
       nonnegative_sequence_tail (fun i=>(b i)%:E) k)%E.
  have hFunctions:(fun i=>(a i+b i)%:E)=
      (fun i=>(a i)%:E+(b i)%:E)%E by apply:funext=>i;rewrite EFinD.
  rewrite /nonnegative_sequence_tail hFunctions.
  apply:nonnegative_sum_add;move=>i _;rewrite lee_fin;[exact:ha i|exact:hb i].
have hJoint:(M m P+M m.+1 Q<=nonnegative_sum setT (fun i=>(a i+b i)%:E))%E.
  have h:=leeD (hPTail 0%N) (hQTail 0%N).
  rewrite !big_ord0 !subr0 -(hTailAdd 0%N) in h.
  have hAll:[set i:nat|(0<=i)%N]=setT.
    apply:funext=>i;apply:propext;split=>// _;exact:leq0n.
  by rewrite /nonnegative_sequence_tail hAll in h.
pose pA:=fun k=>\sum_(i<k) A i.
pose pB:=fun k=>\sum_(i<k) B i.
have hPrefix k:(\sum_(i<k) (A i+bd (B i)))=pA k+bd (pB k).
  by rewrite /pA /pB big_split linear_sum.
have hBoundaryWeak:=@current_weak_limit_boundary R h2 n m U hU pB Q hQWeak.
have hSumWeak:=@current_weak_sequence_limit_linear R h2 n m U hU
  pA (fun k=>bd (pB k)) P (bd Q) 1 hPWeak hBoundaryWeak.
have hScale:(fun i=>1*:pA i+bd (pB i))=(fun k=>pA k+bd (pB k)).
  by apply:funext=>k;rewrite scale1r.
rewrite !scale1r in hSumWeak.
have hFunctions:(fun k=>\sum_(i<k) (A i+bd (B i)))=(fun k=>pA k+bd (pB k)).
  apply:funext=>k;exact:hPrefix k.
exists P,Q;split;first exact:hP.
split;first exact:hQ.
split;first exact:hPLimit.
split;first exact:hQLimit.
split;first exact:hJoint.
split;first by rewrite hFunctions -hScale.
move=>k.
have hResidA:Rect m (P-pA k).
  exact:rectifiable_current_subtract hP (@rectifiable_current_prefix R h2 n m U hU K A hA k).
have hResidB:Rect m.+1 (Q-pB k).
  exact:rectifiable_current_subtract hQ
    (@rectifiable_current_prefix R h2 n m.+1 U hU K B hB k).
have hEqual:P+bd Q-\sum_(i<k) (A i+bd (B i))=(P-pA k)+bd (Q-pB k).
  by rewrite hPrefix (linB (hom_linear bd)) opprD addrACA.
have hResidual:IF (P+bd Q-\sum_(i<k) (A i+bd (B i))).
  exists (P-pA k),(Q-pB k);split;first exact:hResidA.
  split;[exact:hResidB|exact:hEqual].
exists hResidual.
have hLower:=@integral_flat_size_lower R h2 n m U hU K
  (P+bd Q-\sum_(i<k) (A i+bd (B i)))
  (Size (P+bd Q-\sum_(i<k) (A i+bd (B i))) hResidual)
  (@IntegralFlatSize.laws R h2 n m U hU K
    (P+bd Q-\sum_(i<k) (A i+bd (B i))) hResidual)
  (P-pA k) (Q-pB k) hResidA hResidB hEqual.
apply:(le_trans hLower);rewrite hTailAdd.
exact:leeD (hPTail k) (hQTail k).
Qed.
End IntegralFlatRectifiablePairSeries.
