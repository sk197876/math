(** Supporting Federer (1969), 3.4.8(5), p. 328:
    continuity into the abstract finite normed product
    is determined by its coordinates. The sum norm
    and linear projections are those of 3.1.1(4),
    p. 210. The proof includes the empty product. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormedFamilyUP NormedFamilyLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_family_continuous_assembly]: finite
    coordinate continuity gives continuity for the specified
    product norm, supporting 3.4.8(5), p. 328,
    and the product of 3.1.1(4), p. 210. *)
Theorem normed_family_continuous_assembly (R:realType) m
  (V:'I_m->lmodType R) (N:forall i,V i->R)
  (hN:forall i,is_real_norm (N i)) (P:lmodType R)
  (coordinate:forall i,Hom P (V i)) (PN:P->R)
  (hP:is_normed_family N coordinate PN) (T:topologicalType) (f:T->P):
  (forall i,continuous (fun t:T=>(coordinate i (f t):real_norm_metric_space (hN i)))) ->
  continuous (fun t:T=>(f t:real_norm_metric_space (@normed_family_is_norm R m V N hN P coordinate PN hP))).
Proof.
move=>hContinuous t U hU.
pose hPN:=@normed_family_is_norm R m V N hN P coordinate PN hP.
have [epsilon hEpsilon hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (f t:real_norm_metric_space hPN) U) hU.
pose delta:=epsilon/(m.+1)%:R.
have hDenominator:0<((m.+1)%:R:R) by rewrite ltr0n.
have hDelta:0<delta:=divr_gt0 hEpsilon hDenominator.
have hNear (i:'I_m):nbhs t [set s:T|N i (coordinate i (f t)-coordinate i (f s))<delta].
  have hBallN:nbhs (coordinate i (f t):real_norm_metric_space (hN i))
      [set z:real_norm_metric_space (hN i)|N i (coordinate i (f t)-z)<delta].
    apply:(proj2 (metricType_numDomainType.nbhs_mdistP
    (coordinate i (f t):real_norm_metric_space (hN i)) _)).
    exists delta;first exact:hDelta.
    by move=>z hz.
  exact:(hContinuous i t _ hBallN).
have hAll:=@filter_forall T (Finite.clone 'I_m _) _ (nbhs t) (nbhs_filter t) hNear.
apply:filterS hAll=>s hs;apply:hBall.
change (is_true (PN (f t-f s)<epsilon)).
rewrite (normed_family_norm hP).
apply:(le_lt_trans (y:=m%:R*delta)).
- have hConst:(\sum_(i<m) delta) = m%:R*delta by rewrite sumr_const card_ord mulr_natl.
  rewrite -hConst.
  apply:ler_sum=>i _;rewrite linearB /=.
  exact:ltW (hs i).
- rewrite /delta mulrA (mulrC m%:R epsilon) ltr_pdivrMr //.
  by rewrite ltr_pM2l // ltr_nat ltnSn.
Qed.
