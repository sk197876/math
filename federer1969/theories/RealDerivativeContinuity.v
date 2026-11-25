(** Federer (1969), 3.2.7, p. 246:
    scalar regularity supporting the oscillatory example.
    A finite actual derivative gives continuity by its
    finite point-growth bound, using no external calculus. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealMetricBackground RealCurveDerivativeUP ScalarDifferentiabilityCover MetricLocalLipschitzCenters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_derivative_continuous_at]: supporting
    continuity at every nonzero parameter point of
    the third example in Federer 3.2.7, p. 246.
    The derivative remains an actual finite limit,
    not a chosen total derivative representative. *)
Lemma real_derivative_continuous_at (R:realType) (f:R->R) (a v:R):
  has_real_curve_derivative f a v ->
  (f:real_line_metric R->real_line_metric R) @ a --> f a.
Proof.
move=>hD U /nbhs_ballP[e he hU].
have [j hj]:=scalar_derivative_growth_center hD.
pose M:=(j.+1%:R:R); pose r:=(M^-1)%R.
have hM:0<M by rewrite /M ltr0n.
have hr:0<r by rewrite /r invr_gt0.
have hEM:0<e/M by rewrite divr_gt0.
change (nbhs (a:real_line_metric R) [set x|U (f x)]).
have hDelta:0<Num.min r (e/M) by rewrite lt_min hr hEM.
apply/nbhs_ballP; exists (Num.min r (e/M)); first exact hDelta.
move=>x hx; apply:hU.
have hx':mdist (a:real_line_metric R) x<Num.min r (e/M):=hx.
have hMinR:Num.min r (e/M)<=r by rewrite ge_min lexx.
have hMinE:Num.min r (e/M)<=e/M by rewrite ge_min lexx orbT.
have hxr:mdist (a:real_line_metric R) x<r.
  exact (lt_le_trans hx' hMinR).
have hxe:mdist (a:real_line_metric R) x<e/M.
  exact (lt_le_trans hx' hMinE).
have hG:=hj.2 x hxr.
have hStrict:M*mdist (x:real_line_metric R) a<e.
  rewrite !real_line_metric_distanceE distrC.
  change (is_true (`|a-x|<e/M)) in hxe.
  by move:hxe; rewrite ltr_pdivlMr // mulrC.
have hh:=le_lt_trans hG.2 hStrict.
move:hh; by rewrite !real_line_metric_distanceE /ball /= distrC.
Qed.
