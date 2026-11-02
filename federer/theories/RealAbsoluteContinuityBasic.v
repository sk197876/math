(** Federer (1969), 2.9.20, pp. 165–166: elementary consequences of
    condition (3), in particular continuity on the closed interval in (4).
    Source context and erratum check: RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import OrderedIntervalFamilyUP RealAbsoluteContinuityUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_absolute_continuity_restrict]: supporting restriction
    consequence of Federer 2.9.20(3), p. 165. Every eligible family
    in a closed subinterval remains eligible in the original segment. *)
Lemma real_absolute_continuity_restrict (R : realType) (g : R -> R)
    (a u v b : R) : a<=u -> v<=b ->
  is_absolutely_continuous_real_curve g a b ->
  is_absolutely_continuous_real_curve g u v.
Proof.
move=> hau hvb hg e he; have [d [hd hfamily]] := hg e he.
exists d; split=> // s hs hlen; apply: hfamily=> //.
apply: ordered_real_interval_family_lower_bound hau _.
exact: ordered_real_interval_family_upper_bound hvb hs.
Qed.

(** Source for [real_absolute_continuity_increment_control]: supporting
    single-cell consequence of Federer 2.9.20(3), p. 165, used for the
    continuity assertion on p. 166 Both orientations and coincident
    endpoints are included while the definition retains strict nonempty
    cells. *)
Lemma real_absolute_continuity_increment_control (R : realType) (g : R -> R)
    (a b : R) : is_absolutely_continuous_real_curve g a b ->
  forall e : R, 0<e -> exists d : R, 0<d /\ forall x y : R,
    a<=x -> x<=b -> a<=y -> y<=b -> `|y-x|<=d -> `|g y-g x|<=e.
Proof.
move=> hg e he; have [d [hd hs]] := hg e he.
exists d; split=> // x y hax hxb hay hyb hxy.
case: (ltgtP x y)=> horder.
- have hf : is_ordered_real_interval_family a b [:: (x,y)] by [].
  have hlen : real_interval_family_length [:: (x,y)]<=d.
    by move: hxy; rewrite ger0_norm ?subr_ge0 ?(ltW horder) // /real_interval_family_length big_seq1.
  have := hs _ hf hlen.
  by rewrite /real_interval_family_increment_sum big_seq1.
- have hf : is_ordered_real_interval_family a b [:: (y,x)] by [].
  have hlen : real_interval_family_length [:: (y,x)]<=d.
    move: hxy; rewrite distrC /real_interval_family_length big_seq1.
    by rewrite ger0_norm ?subr_ge0 ?(ltW horder).
  have := hs _ hf hlen.
  by rewrite /real_interval_family_increment_sum big_seq1 distrC.
- by rewrite horder subrr normr0; exact: ltW he.
Qed.

(** Source for [real_absolute_continuity_continuous]: direct continuity
    conclusion in the implication (3)=>(4) of Federer 2.9.20, p. 166
    Continuity is relative to [a,b], so no condition outside the segment or
    global continuity at its endpoints is imposed. *)
Theorem real_absolute_continuity_continuous (R : realType) (g : R -> R)
    (a b : R) : is_absolutely_continuous_real_curve g a b ->
  {within (`[a,b] : set (real_line_metric R)),
    continuous (g : real_line_metric R -> real_line_metric R)}.
Proof.
move=> hg; apply/subspace_continuousP=> x hx; apply/cvg_ballP=> e he.
have he2 : (0<e/2 :> R) by rewrite divr_gt0 // ltr0n.
have [d [hd hcontrol]] := real_absolute_continuity_increment_control hg he2.
change (nbhs (x : real_line_metric R)
  [set y | `[a,b] y -> ball (g x : real_line_metric R) e (g y)]).
apply: (filterS _ (nbhsx_ballx (x : real_line_metric R) d hd))=> y hy hyA.
move: hx hyA; rewrite /= !in_itv /= => /andP[hax hxb] /andP[hay hyb].
have hxy : `|y-x|<=d.
  by apply: ltW; move: hy; rewrite /ball /= distrC.
have hb := hcontrol x y hax hxb hay hyb hxy.
change (`|g x-g y|<e); rewrite distrC.
apply: le_lt_trans hb _.
by rewrite ltr_pdivrMr ?ltr0n // mulr_natr ltrDl.
Qed.

(** Source for [constant_real_curve_absolutely_continuous]: supporting
    zero-increment boundary case of Federer 2.9.20(3), p. 165.
    A constant curve satisfies the stated epsilon law on any segment. *)
Lemma constant_real_curve_absolutely_continuous (R : realType) (c a b : R) :
  is_absolutely_continuous_real_curve (fun _ : R => c) a b.
Proof.
move=> e he; exists 1; split; first exact: ltr01.
move=> s hs hlen; rewrite /real_interval_family_increment_sum.
have -> : \sum_(uv <- s) `|c-c| = (0 : R).
  by rewrite subrr normr0 big1.
exact: ltW he.
Qed.
