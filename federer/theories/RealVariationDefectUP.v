(** Federer (1969), 2.9.19, p. 165: the sets C_m used to identify s' with
    |g'|. Natural index n represents the printed positive index m=n+1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength LebesgueScalarMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_variation_defect]: direct increment
    s(b)-s(a)-|g(b)-g(a)| in Federer 2.9.19, p. 165 It measures the gap
    between arc-length increment and endpoint distance, using the
    established arc-length function from 2.5.16. *)
Definition real_variation_defect (R : realType) (g : R -> real_line_metric R) (a b : R) :=
  arc_length g b-arc_length g a-`|g b-g a|.

(** Source for [real_variation_defect_locus]: direct C_m in Federer 2.9.19,
    p. 165. At every containing nondegenerate interval of length below 1/m,
    the defect exceeds the length divided by m. Index n denotes m=n+1
    without including m=0. *)
Definition real_variation_defect_locus (R : realType) (g : R -> real_line_metric R) (n : nat) :=
  [set x : real_line_metric R | forall a b : R, a<=x<=b ->
    0<b-a<((n.+1)%:R : R)^-1 ->
    (b-a)/(n.+1)%:R<real_variation_defect g a b].

(** Source for [real_variation_defect_nonnegative]: supporting nonnegativity
    used to enlarge the sum over K to the full partition sum in Federer
    2.9.19, p. 165 The distance/variation inequality of 2.5.16 gives
    |g(b)-g(a)|<=s(b)-s(a). *)
Lemma real_variation_defect_nonnegative (R : realType) (g : R -> real_line_metric R) :
  curve_locally_finite_variation g -> forall a b : R, a<=b ->
  0<=real_variation_defect g a b.
Proof.
move=> hg a b hab; rewrite /real_variation_defect subr_ge0.
have h := @arc_length_distance R [the metricType R of real_line_metric R] g hg a b hab.
by rewrite real_line_metric_distanceE distrC in h.
Qed.

(** Source for [real_variation_defect_self]: zero-width boundary case for
    the finite-partition representation supporting Federer 2.9.19, p. 165.
    Repeated endpoints contribute zero defect and zero interval length. *)
Lemma real_variation_defect_self (R : realType) (g : R -> real_line_metric R) (a : R) :
  real_variation_defect g a a=0.
Proof. by rewrite /real_variation_defect !subrr normr0 subr0. Qed.

(** Source for [real_variation_defect_locus_cell_bound]: supporting cellwise
    estimate in Federer 2.9.19, p. 165 If a short positive-width cell meets
    C_m, its length is at most m times its defect. A cell missing C_m has
    zero restricted mass, bounded by the same nonnegative cost. Zero-width
    cells also have zero mass and zero defect. Summing all cells implements
    the printed K-sum followed by its nonnegative enlargement to all
    indices. We follow Federer's correctly grouped formula, with m
    multiplying the whole defect. *)
Lemma real_variation_defect_locus_cell_bound (R : realType)
    (g : R -> real_line_metric R) (n : nat) (a b : R) :
  curve_locally_finite_variation g -> a<=b -> b-a<((n.+1)%:R : R)^-1 ->
  (lebesgue_scalar_measure (real_variation_defect_locus g n `&` `[a,b])<=
    ((n.+1)%:R*real_variation_defect g a b)%:E)%E.
Proof.
move=> hg hab hwidth; have hm := lebesgue_scalar_is_measure R.
have hmono := @measure_mono R (real_line_metric R) (@lebesgue_scalar_measure R) hm
  (real_variation_defect_locus g n `&` `[a,b]) `[a,b] (fun x hx => hx.2).
case: (eqVneq a b)=> [heq|hne].
- by move: hmono; rewrite heq (@lebesgue_scalar_segment R b b (lexx _)) subrr real_variation_defect_self mulr0.
- have hab' : a<b by rewrite lt_neqAle hne hab.
  case: (pselect (exists x, real_variation_defect_locus g n x /\ `[a,b] x))=> [[x [hx hxI]]|hempty].
  + have haxb : a<=x<=b by move: hxI; rewrite /= in_itv.
    have hw : 0<b-a<((n.+1)%:R : R)^-1 by apply/andP; split=> //; rewrite subr_gt0.
    have hdef := hx a b haxb hw.
    have hcoef : (0<(n.+1)%:R :> R) by rewrite ltr0n.
    rewrite ltr_pdivrMr // mulrC in hdef.
    apply: le_trans hmono _; rewrite (@lebesgue_scalar_segment R a b hab) lee_fin.
    exact: ltW hdef.
  + have heq : real_variation_defect_locus g n `&` `[a,b]=set0.
      apply/seteqP; split=> x; last by move=> [].
      by move=> hx; apply: hempty; exists x.
    rewrite heq (measure_empty hm) lee_fin.
    apply: mulr_ge0; first by rewrite ler0n.
    exact (@real_variation_defect_nonnegative R g hg a b hab).
Qed.
