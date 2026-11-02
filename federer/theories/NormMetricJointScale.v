(** Federer (1969), 2.5.20, p. 114: pointwise scalar multiplication
    preserves continuous vector families. This supporting general
    normed-space fact is proved from the supplied norm laws and the induced
    metric. It supports the radial splitting required by 2.5.12(4), p. 103.
    Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology ring lra.
From Federer Require Import RealNormUP NormMetric RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_norm_metric_joint_scale_continuous]:
    joint scalar multiplication continuity supporting Q in
    Federer 2.5.20, p. 114, and its radial splitting
    under hypothesis (4) of 2.5.12, p. 103. *)
Lemma real_norm_metric_joint_scale_continuous (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) :
  continuous (fun p : real_line_metric R * real_norm_metric_space hN =>
    (p.1*:p.2 : real_norm_metric_space hN)).
Proof.
move=> [a b] U hU.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP (a*:b : real_norm_metric_space hN) U) hU.
pose C := `|a|+N b+1.
have hC : 0<C by have h0 := normr_ge0 a; have h1 := real_seminorm_nonnegative hN.1 b; rewrite /C; lra.
pose d := Order.min 1 (e/(2*C)).
have hden : 0<2*C by rewrite mulr_gt0 // ltr0n.
have hd : 0<d by rewrite /d lt_min ltr01 divr_gt0.
have hd1 : d<=1 by rewrite /d ge_min lexx.
have hde : d<=e/(2*C) by rewrite /d ge_min lexx orbT.
exists ([set c : real_line_metric R | mdist a c<d],
        [set v : real_norm_metric_space hN | mdist b v<d]).
- split.
  + apply: (proj2 (metricType_numDomainType.nbhs_mdistP a _)).
    exists d=> // c hc; exact hc.
  + apply: (proj2 (metricType_numDomainType.nbhs_mdistP b _)).
    exists d=> // v hv; exact hv.
- move=> [c v] [hc hv]; apply: hb.
  change (N (a*:b-c*:v)<e).
  have hcd : `|a-c|<=d := ltW hc.
  have hvd : N (b-v)<=d := ltW hv.
  have hv0 := real_seminorm_nonnegative hN.1 v.
  have hnv : N v<=N b+1.
    have ht := real_seminorm_triangle hN.1 (v-b) b.
    rewrite subrK (real_seminorm_subtract hN.1 v b) in ht.
    have hbd := le_trans hvd hd1; lra.
  have heq : a*:b-c*:v=a*:(b-v)+(a-c)*:v.
    by rewrite scalerBr scalerBl addrA subrK.
  rewrite heq; apply: le_lt_trans (real_seminorm_triangle hN.1 _ _) _.
  rewrite !(real_seminorm_scale hN.1).
  have hfirst := ler_wpM2l (normr_ge0 a) hvd.
  have hsecond := le_trans (ler_wpM2r hv0 hcd) (ler_wpM2l (ltW hd) hnv).
  have hsum := lerD hfirst hsecond.
  have halg : `|a|*d+d*(N b+1)=C*d by rewrite /C; ring.
  rewrite halg in hsum; apply: le_lt_trans hsum _.
  have hm := ler_wpM2l (ltW hC) hde.
  have hcalc : C*(e/(2*C))=e/2.
    by rewrite invfM [C * _]mulrC !mulrA divfK ?gt_eqF.
  rewrite hcalc in hm; apply: le_lt_trans hm _.
  by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
Qed.
