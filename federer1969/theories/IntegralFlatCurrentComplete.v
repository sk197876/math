(** Federer (1969), 4.1.24, p. 382: the
    original integral-flat metric is complete. Select
    a subsequence of finite total length by the
    already specified increasing Cauchy indices. Apply
    the full original rectifiable-series argument, then
    recover the entire Cauchy sequence and every
    proper Cauchy filter. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces AdditiveSubgroupRepresentationUP
  IntegralCurrentClassesUP IntegralCurrentAlgebra IntegralCurrentGroupSpaces
  IntegralFlatSizeUP IntegralFlatSizeSealed IntegralFlatCurrentMetric
  IntegralFlatSequenceLimitUP IntegralFlatFiniteLengthSequence
  NonnegativeSum NonnegativeGeometricBound CauchyIndexSelectionUP
  CauchyIndexSelectionSealed CauchyIndexSelectionLaws
  CompleteMetricUP MetricSequentialCompleteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IntegralFlatCurrentComplete.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation G:=(@integral_flat_current_metric R h2 n m U hU K).
Local Notation inc:=(@integral_flat_current_inclusion R h2 n m U hU K).
Local Notation hG:=(@integral_flat_current_group_laws R h2 n m U hU K).
Local Notation IF:=(@is_integral_flat_current_supported_in R h2 n U hU m K).
Local Notation Size:=(@IntegralFlatSize.value R h2 n m U hU K).

(** Source for [integral_flat_current_sequence_complete]: the full
    original finite-length series argument gives a limit
    for every Cauchy sequence in the actual original
    integral-flat metric, 4.1.24, p. 382. *)
Theorem integral_flat_current_sequence_complete (u:nat->G):
  (forall epsilon:R,0<epsilon->exists N,forall i j,
    (N<=i)%N->(N<=j)%N->mdist (u i) (u j)<epsilon)->
  exists z:G,forall epsilon:R,0<epsilon->exists N,forall i,
    (N<=i)%N->mdist z (u i)<epsilon.
Proof.
move=>hCauchy;pose q:R:=1/2.
have hQ:0<q<1 by rewrite /q;apply/andP;split;lra.
pose d:=fun i j=>(mdist (u i) (u j))%:E.
pose b:=fun i=>q^+i.
have hChoice k:exists N,forall i j,(N<=i)%N->(N<=j)%N->(d i j<(b k)%:E)%E.
  have[N hN]:=hCauchy (b k) (exprn_gt0 k (andP hQ).1).
  exists N=>i j hNi hNj;rewrite /d lte_fin;exact:hN i j hNi hNj.
pose s:=@CauchyIndexSelection.value R d b hChoice.
pose hs:=@CauchyIndexSelection.laws R d b hChoice.
pose v:=fun k=>inc (u (s k)).
have hV k:IF (v k):=additive_subgroup_representation_member hG (u (s k)).
pose hIncrement:=fun k=>@integral_flat_current_subtract_supported R h2 n U hU K m
  (v k.+1) (v k) (hV k.+1) (hV k).
have hStep k:((Size (v k.+1-v k) (hIncrement k))%:E<=(b k)%:E)%E.
  have h:=@cauchy_index_successive_bound R d b s hs k.
  rewrite /d (@integral_flat_current_distance_value R h2 n m U hU K
    (u (s k.+1)) (u (s k)) (hIncrement k)) in h.
  exact:ltW h.
have hGeo:(nonnegative_sum setT (fun k=>(b k)%:E)< +oo)%E.
  have h:=@nonnegative_geometric_bound R 1 q (ler01)
    (ltW (andP hQ).1) (andP hQ).2.
  have hFunctions:(fun k=>(1*q^+k)%:E)=(fun k=>(b k)%:E).
    by apply:funext=>k;rewrite /b mul1r.
  rewrite hFunctions in h;exact:le_lt_trans h (ltry _).
have hLength:(nonnegative_sum setT
    (fun k=>(Size (v k.+1-v k) (hIncrement k))%:E)< +oo)%E.
  apply:(le_lt_trans _ hGeo);apply:nonnegative_sum_mono=>k _;exact:hStep k.
have[A [B [P [Q [T hConclusion]]]]]:=
  @integral_flat_finite_length_sequence_limit R h2 n m U hU K v hV hLength.
have hT:IF T:=hConclusion.2.2.2.2.2.1.
have hLimit:@is_integral_flat_sequence_limit R h2 n m U hU K v T:=
  hConclusion.2.2.2.2.2.2.2.2.
have[z hZ]:=additive_subgroup_representation_full hG hT.
have hSubsequence:forall epsilon:R,0<epsilon->exists N,forall k,
    (N<=k)%N->mdist (z:G) (u (s k))<epsilon.
  move=>epsilon hEpsilon;have[N hN]:=hLimit epsilon hEpsilon.
  exists N=>k hNk;have[hResidual hSmall]:=hN k hNk.
  have hDistance:=@integral_flat_current_distance_specification R h2 n m U hU K z (u (s k)).
  rewrite hZ in hDistance.
  have hValue:=integral_flat_size_unique hDistance
    (@IntegralFlatSize.laws R h2 n m U hU K (T-v k) hResidual).
  by rewrite hValue.
exists z=>epsilon hEpsilon.
have hHalf:0<epsilon/2 by rewrite divr_gt0 //;lra.
have[N hN]:=hCauchy (epsilon/2) hHalf.
have[M hM]:=hSubsequence (epsilon/2) hHalf.
pose k:=maxn N M.
have hNk:(N<=s k)%N:=leq_trans (leq_maxl N M)
  (@strict_index_sequence_dominates s hs.1 k).
have hNear:=hM k (leq_maxr N M).
exists N=>i hNi.
have hCauchyNear:=hN (s k) i hNk hNi.
have hTriangle:=metric_triangle (z:G) (u (s k)) (u i);lra.
Qed.

(** Source for [integral_flat_current_complete]: full completeness
    of the original integral-flat metric, for every
    proper Cauchy filter, Federer 4.1.24, p. 382. *)
Theorem integral_flat_current_complete:is_complete_metric_space G.
Proof.
apply:metric_sequentially_complete_is_complete.
exact:integral_flat_current_sequence_complete.
Qed.
End IntegralFlatCurrentComplete.
