(** Supporting localisation for Federer (1969), 2.9.21, p. 166: the
    change-of-variable identities depend only on the curve on [a,b]. Reuse
    the project's nondecreasing segment retraction from 2.5.18(2), p. 112,
    to obtain a globally continuous representative from relative segment
    continuity. The retraction is only a proof witness, not an added global
    continuity assumption. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground StieltjesSubstitution CurveVariationUP
  CurveArcLength SegmentContinuityControl.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [segment_retraction_continuous]: supporting topology
    law for the localisation used in Federer 2.9.21, p. 166,
    using the retraction already introduced for 2.5.18(2), p. 112.
    Minimum and maximum are continuous in the standard real topology;
    no measure or calculus result is imported. *)
Lemma segment_retraction_continuous (R : realType) (a b : R) :
  continuous (@segment_retraction R a b : real_line_metric R -> real_line_metric R).
Proof.
move=> x; rewrite /segment_retraction.
apply (@continuous_max R [the topologicalType of real_line_metric R]
  (fun _ => a) (fun y => Order.min y b) x); first exact: cvg_cst.
apply (@continuous_min R [the topologicalType of real_line_metric R]
  (fun y => y) (fun _ => b) x); [exact: cvg_id|exact: cvg_cst].
Qed.

(** Source for [segment_retracted_curve_continuous]: supporting localisation
    in Federer 2.9.21, p. 166 A curve continuous only relative to [a,b]
    becomes globally continuous after composition with the segment
    retraction. *)
Lemma segment_retracted_curve_continuous (R : realType) (g : R -> R) (a b : R) :
  a<=b -> {within (`[a,b] : set (real_line_metric R)),
    continuous (g : real_line_metric R -> real_line_metric R)} ->
  continuous (g \o @segment_retraction R a b : real_line_metric R -> real_line_metric R).
Proof.
move=> hab hg x; apply/cvg_ballP=> e he.
pose c := @segment_retraction R a b.
have /andP[hacx hcxb] := @segment_retraction_bounds R a b x hab.
have [d [hd hcontrol]] := @segment_continuity_epsilon_control R g a b (c x) e hg hacx hcxb he.
have hcvg : (c : real_line_metric R -> real_line_metric R) @
    (x : real_line_metric R) --> (c x : real_line_metric R).
  exact: segment_retraction_continuous a b x.
have hb : \forall y \near (x : real_line_metric R), ball (c x : real_line_metric R) d (c y).
  exact: (cvg_ballP _ _).1 hcvg d hd.
apply: (filterS _ hb)=> y hy.
have /andP[hacy hcyb] := @segment_retraction_bounds R a b y hab.
have hclose : `|c y-c x|<d by move: hy; rewrite /ball /= distrC.
have hvalue := hcontrol (c y) hacy hcyb hclose.
by rewrite /ball /= distrC.
Qed.

(** Source for [segment_retracted_curve_locally_finite_variation]: supporting
    localisation in Federer 2.9.21, p. 166, using the variation
    composition bound of 2.5.16, p. 109, as applied in 2.5.18(2),
    p. 112. Nondecreasing reparametrisation preserves locally finite
    variation. This does not use continuity or differentiation. *)
Lemma segment_retracted_curve_locally_finite_variation (R : realType)
    (g : R -> R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  curve_locally_finite_variation (g \o @segment_retraction R a b : R -> real_line_metric R).
Proof.
move=> hg u v huv.
have hmono := @segment_retraction_monotone R a b.
apply: le_lt_trans (@curve_variation_comp_le R g (@segment_retraction R a b) u v hmono huv) _.
exact: hg (hmono u v huv).
Qed.
