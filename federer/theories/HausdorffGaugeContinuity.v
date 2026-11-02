(** Supporting continuity of the integer-degree normalized diameter gauge in
    Federer (1969), 2.10.2, p. 171. It permits arbitrarily small positive
    enlargements of covering sets. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology normedtype realfun.
From mathcomp Require Import lra.
From Federer Require Import HausdorffDiameterCost RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_real_gauge_continuous]: supporting
    polynomial continuity of the printed integer-degree cost
    in Federer 2.10.2, p. 171, including degree zero. *)
Lemma hausdorff_real_gauge_continuous (R : realType) (m : nat) :
  continuous (fun d : R => hausdorff_normalisation R m*d^+m).
Proof.
move=> d; apply: (@continuousM R R^o
  (fun _ => hausdorff_normalisation R m) (fun z => z^+m) d).
- exact: cst_continuous.
- exact: exprn_continuous.
Qed.

(** Source for [hausdorff_real_gauge_small_enlargement]:
    supporting positive enlargement with cost below any
    strict upper bound for the open-cover replacement in
    Federer 2.10.2(1), p. 171. The diameter cap is
    enforced simultaneously; the starting diameter may be zero. *)
Lemma hausdorff_real_gauge_small_enlargement (R : realType) (m : nat) (d t b : R) :
  d<t -> hausdorff_normalisation R m*d^+m<b ->
  exists r : R, 0<r /\ d+r+r<t /\ hausdorff_normalisation R m*(d+r+r)^+m<b.
Proof.
move=> hdt hb.
pose f (z : real_line_metric R) : real_line_metric R := hausdorff_normalisation R m*z^+m.
have hf : continuous f := @hausdorff_real_gauge_continuous R m.
have hn : nbhs (f d) [set z : real_line_metric R | mdist (f d) z<b-f d].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (f d) _)).
  exists (b-f d); first by rewrite /= subr_gt0.
  by move=> z hz.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (d : real_line_metric R) _) (hf d _ hn).
pose r := Order.min (e/4) ((t-d)/4).
have h4 : (0<(4:R))%R by rewrite ltr0n.
have hr : 0<r by rewrite /r lt_min !divr_gt0 // subr_gt0.
have hre : r<=e/4 by rewrite /r ge_min lexx.
have hrt : r<=(t-d)/4 by rewrite /r ge_min lexx orbT.
have hdist : mdist (d : real_line_metric R) (d+r+r)<e.
  rewrite real_line_metric_distanceE; have hh : d-(d+r+r)=-(r+r) by lra.
  rewrite hh normrN ger0_norm; lra.
have hh := hball (d+r+r) hdist.
change (is_true (`|f d-f (d+r+r)|<b-f d)) in hh.
have hbound := ler_norm (f (d+r+r)-f d).
rewrite distrC in hbound.
exists r; split=> //; split; first lra.
change (is_true (f (d+r+r)<b)); lra.
Qed.
