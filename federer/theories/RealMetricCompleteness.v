(** Federer (1969), 2.2.9, p. 65, applicability to R. The completeness and
    absence of isolated points of the standard real line are background
    hypotheses for the special case. The narrow complete_normed_module
    import supplies only the standard real completeness theorem, proved
    there from the supremum property of the existing real-field interface.
    No descriptive-set or embedding theorem is imported. Source context:
    NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology complete_normed_module.
From Federer Require Import RealMetricBackground CompleteMetricUP NoIsolatedPoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_line_metric_complete]: supporting standard
    real completeness for the special case X=R in Federer 2.2.9,
    p. 65. The adapter preserves the standard real topology,
    so every proper Cauchy filter has a real limit. *)
Lemma real_line_metric_complete (R : realType) :
  is_complete_metric_space [the metricType R of real_line_metric R].
Proof.
move=> F hF hC; have hc := @R_complete R F hF hC.
have [x hx] := proj1 (@cvg_ex [the pnbhsType of R^o] F) hc.
exists x; exact hx.
Qed.

(** Source for [real_line_has_no_isolated_points]: supporting
    hypothesis for Federer 2.2.9, p. 65: every real ball
    of positive radius contains a different point, obtained by
    moving half its radius to the right. *)
Lemma real_line_has_no_isolated_points (R : realType) :
  has_no_isolated_points [the metricType R of real_line_metric R].
Proof.
apply: punctured_balls_no_isolated_points=> x r hr.
have hhalf : 0 < r/2 by rewrite divr_gt0 // ltr0n.
have hsmall : r/2 < r.
  by rewrite ltr_pdivrMr ?ltr0n // -{1}[r]mulr1 (ltr_pM2l hr) ltr1n.
exists ((x : R)+r/2); rewrite real_line_metric_distanceE opprD addrA subrr add0r normrN.
by rewrite ger0_norm ?(ltW hhalf); split.
Qed.
