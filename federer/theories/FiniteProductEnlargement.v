(** Federer (1969), 2.10.39, printed p. 199: the printed subdivision starts
    with positive box widths. This supporting continuity lemma permits small
    positive enlargements of all widths, then recovers zero-width boxes by a
    limit of their finite side products. It expands the degenerate case
    rather than adding a positive-width hypothesis to the corollary. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  topology num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_width_product_continuous]: supporting
    finite-product continuity for the small positive
    box enlargements in 2.10.39, p. 199.
    The finite index type may be empty. *)
Lemma finite_width_product_continuous (R : realType) (I : finType) (c : I -> R) (a : R) :
  continuous (fun e : R=>a*\prod_i (c i+e)).
Proof.
move=> e; apply: continuousM; first exact: cst_continuous.
apply: continuous_big; first exact: mul_continuous.
move=> i _ z; apply: continuousD; [exact: cst_continuous|exact: cvg_id].
Qed.

(** Source for [finite_width_product_small_enlargement]: supporting
    limiting passage from positive-width to degenerate
    boxes for 2.10.39, p. 199. A single positive
    increment respects a prescribed mesh margin and
    keeps the enlarged product below any strict upper bound. *)
Lemma finite_width_product_small_enlargement (R : realType) (I : finType)
    (c : I -> R) (a cap b : R) :
  0<cap -> a*\prod_i c i<b ->
  exists e : R, 0<e /\ e<cap /\ a*\prod_i (c i+e)<b.
Proof.
move=> hcap hb.
pose f (e : real_line_metric R) : real_line_metric R := a*\prod_i (c i+e).
have hf : continuous f := @finite_width_product_continuous R I c a.
have hf0 : f 0=a*\prod_i c i.
  rewrite /f; congr (a*_); apply: eq_bigr=> i _; exact: addr0.
have hgap : 0<b-f 0 by rewrite subr_gt0 hf0.
have hn : nbhs (f 0) [set y : real_line_metric R | mdist (f 0) y<b-f 0].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (f 0) _)).
  exists (b-f 0)=> // y hy; exact hy.
have [r hr hball] := proj1 (metricType_numDomainType.nbhs_mdistP
  (0 : real_line_metric R) _) (hf 0 _ hn).
pose e := Order.min (r/2) (cap/2).
have he : 0<e by rewrite /e lt_min !divr_gt0 // ltr0n.
have her : e<=r/2 by rewrite /e ge_min lexx.
have hec : e<=cap/2 by rewrite /e ge_min lexx orbT.
have hdist : mdist (0 : real_line_metric R) e<r.
  rewrite real_line_metric_distanceE sub0r normrN ger0_norm; lra.
have hh := hball e hdist.
change (is_true (`|f 0-f e|<b-f 0)) in hh.
have hnorm := ler_norm (f e-f 0); rewrite distrC in hnorm.
exists e; split=> //; split; first lra.
change (is_true (f e<b)); lra.
Qed.
