(** Federer (1969), 4.1.24, p. 382: choose
    geometrically close normal approximants in the original
    K and telescope their differences. The preceding
    flat triangle laws give a summable geometric
    majorant. Construction proves the independent series
    laws; it changes no support index and assumes
    no finite M(T). *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentSupportGeometry NormalCurrentsUP NormalCurrentLinear
  FlatCurrentsUP FlatCurrentFinite CurrentFlatNorm CurrentFlatDualSeminormBasic
  CurrentFlatFiniteArithmetic CurrentFlatSequenceLimitUP CurrentFlatSequenceLimits
  CurrentWeakSequenceLimit GeometricUniformTail NonnegativeGeometricBound
  FlatCurrentNormalSeriesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FlatCurrentNormalSeriesExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation F:=(@current_flat_norm R h2 n m U hU K).
Local Notation Normal:=(@normal_currents_supported_in R h2 n U hU m K).

(** Source for [flat_current_normal_series_exists]: every
    original member of F_(m,K) has the specified
    actual same-K normal series, 4.1.24, p. 382.
    This reconstructs the needed earlier dependencies
    rather than using the larger tube of 4.1.18. *)
Theorem flat_current_normal_series_exists (T:C):
  @is_flat_current_supported_in R h2 n m U hU K T->
  exists v:nat->C,exists a:nat->R,
    @is_flat_current_normal_series R h2 n m U hU K T v a.
Proof.
move=>hT;pose q:R:=1/2.
have hQ:0<q<1 by rewrite /q;apply/andP;split;lra.
have hChoice i:exists P:C,Normal P /\(F (T-P)<(q^+i)%:E)%E.
  exact:hT (q^+i) (exprn_gt0 i (andP hQ).1).
have[N hN]:=choice hChoice.
pose v:=fun i:nat=>match i with 0%N=>N 0%N|j.+1=>N j.+1-N j end.
have hV i:Normal (v i).
  case:i=>[|i];first exact:(hN 0%N).1.
  have hLinear:=@normal_current_linear R h2 n U hU m (-1)
    (N i) (N i.+1) (hN i).1.1 (hN i.+1).1.1.
  have hSupport:=@current_support_linear_subset R h2 n m U hU K (-1)
    (N i) (N i.+1) (hN i).1.2 (hN i.+1).1.2.
  rewrite scaleN1r addrC in hLinear hSupport;split;[exact:hLinear|exact:hSupport].
have hN0Finite:=@supported_normal_current_flat_finite R h2 n m U hU K (N 0%N) (hN 0%N).1.
have[c0 [hc0 hC0]]:=@current_flat_dual_finite_value R h2 n m U hU K
  (@current_value R h2 n U hU m (N 0%N)) hN0Finite.
change (F (N 0%N)=c0%:E) in hC0.
pose C0:=c0+4.
have hC0Positive:0<C0 by rewrite /C0;lra.
pose a:=fun i=>C0*q^+i.
have hBound i:(F (v i)<=(a i)%:E)%E.
  case:i=>[|i].
  - rewrite /v /a expr0 mulr1 hC0 lee_fin /C0;lra.
  - have hFirstFinite:(F (T-N i)< +oo)%E:=lt_trans (hN i).2 (ltry _).
    have hSecondFinite:(F (T-N i.+1)< +oo)%E:=lt_trans (hN i.+1).2 (ltry _).
    have hNeg:=@current_flat_finite_negate R h2 n m U hU K (T-N i.+1) hSecondFinite.
    have hNegFinite:(F (-(T-N i.+1))< +oo)%E by rewrite hNeg.
    have hTriangle:=@current_flat_finite_triangle R h2 n m U hU K
      (T-N i) (-(T-N i.+1)) hFirstFinite hNegFinite.
    have hDifference:(T-N i)+(-(T-N i.+1))=N i.+1-N i.
      by rewrite opprB addrAC addrCA subrr addr0.
    rewrite hDifference hNeg in hTriangle.
    have hCap:=le_trans hTriangle (leeD (ltW (hN i).2) (ltW (hN i.+1).2)).
    apply:(le_trans hCap);rewrite -EFinD lee_fin /a exprS.
    have hPower:0<=q^+i:=exprn_ge0 i (ltW (andP hQ).1).
    have hHalfIdentity:1+q= 3*q by rewrite /q;lra.
    have hLeft:q^+i+q*q^+i=(1+q)*q^+i by rewrite mulrDl mul1r.
    have hScalar:q^+i+q*q^+i= 3*(q*q^+i).
      by rewrite hLeft hHalfIdentity mulrA.
    rewrite hScalar.
    apply:ler_wpM2r;first exact:mulr_ge0 (ltW (andP hQ).1) hPower.
    rewrite /C0;lra.
have hFlatLimit:@is_current_flat_sequence_limit R h2 n m U hU K N T.
  move=>epsilon hEpsilon.
  have[J hJ]:=@geometric_uniform_tail R q 1 epsilon hQ (ler01) hEpsilon.
  exists J=>i hJi.
  apply:(lt_trans (hN i).2);rewrite lte_fin.
  have h:=hJ i hJi;by rewrite mulr1 in h.
have hWeakN:=@current_flat_sequence_limit_weak R h2 n m U hU K N T hFlatLimit.
have hPrefix i:(\sum_(j<i.+1) v j)=N i.
  elim:i=>[|i hPrefix];first by rewrite big_ord1 /v.
  rewrite big_ord_recr hPrefix.
  change (N i+(N i.+1-N i)=N i.+1).
  by rewrite addrC subrK.
exists v,a;constructor.
- exact:hV.
- move=>i;exact:mulr_ge0 (ltW hC0Positive) (exprn_ge0 i (ltW (andP hQ).1)).
- have hGeo:=@nonnegative_geometric_bound R C0 q (ltW hC0Positive)
    (ltW (andP hQ).1) (andP hQ).2.
  exact:le_lt_trans hGeo (ltry _).
- exact:hBound.
- move=>phi epsilon hEpsilon;have[J hJ]:=hWeakN phi epsilon hEpsilon.
  exists J.+1=>i;case:i=>[|i] hJi;first by rewrite leqn0 in hJi.
  rewrite hPrefix;exact:hJ i hJi.
Qed.
End FlatCurrentNormalSeriesExistence.
