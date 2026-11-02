(** Federer (1969), 2.9.22, pp. 167–168: extend the variation conclusion of
    2.9.19 to normed targets. This module expands the metric part of the
    fine near-maximal-partition argument on p. 165; it is valid for every
    metric target, independently of reflexivity. The scalar proof remains
    unchanged. No relevant Federer erratum entry applies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength LebesgueScalarMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.


(** Source for [metric_variation_defect]: supporting extension in Federer
    2.9.22, pp. 167–168, of the partition argument in 2.9.19, p. 165 The
    defect is arc-length increment minus endpoint metric distance, before
    any vector derivative is used. *)
Definition metric_variation_defect (R : realType) (Y : metricType R) (g : R -> Y) (a b : R) :=
  arc_length g b-arc_length g a-mdist (g a) (g b).


(** Source for [metric_variation_defect_locus]: supporting extension in
    Federer 2.9.22, pp. 167–168, of the partition argument in 2.9.19, p.
    165. At every short interval containing x, the metric defect exceeds its
    width divided by the positive index n+1. *)
Definition metric_variation_defect_locus (R : realType) (Y : metricType R) (g : R -> Y) (n : nat) :=
  [set x : real_line_metric R | forall a b : R, a<=x<=b ->
    0<b-a<((n.+1)%:R : R)^-1 ->
    (b-a)/(n.+1)%:R<metric_variation_defect g a b].


(** Source for [metric_variation_defect_nonnegative]: supporting extension
    in Federer 2.9.22, pp. 167–168, of the partition argument in 2.9.19, p.
    165 The metric distance/variation bound makes every ordered cell cost
    nonnegative. *)
Lemma metric_variation_defect_nonnegative (R : realType) (Y : metricType R) (g : R -> Y) :
  curve_locally_finite_variation g -> forall a b : R, a<=b ->
  0<=metric_variation_defect g a b.
Proof.
move=> hg a b hab; rewrite /metric_variation_defect subr_ge0.
exact (@arc_length_distance R Y g hg a b hab).
Qed.


(** Source for [metric_variation_defect_self]: supporting extension in
    Federer 2.9.22, pp. 167–168, of the partition argument in 2.9.19, p. 165
    A repeated endpoint has zero defect and zero width in any metric target. *)
Lemma metric_variation_defect_self (R : realType) (Y : metricType R) (g : R -> Y) (a : R) :
  metric_variation_defect g a a=0.
Proof. by rewrite /metric_variation_defect !subrr mdistxx subr0. Qed.


(** Source for [metric_variation_defect_locus_cell_bound]: supporting
    extension in Federer 2.9.22, pp. 167–168, of the partition argument in
    2.9.19, p. 165 A short cell meeting the defect locus has its restricted
    Lebesgue mass bounded by the whole defect times n+1. Empty and
    zero-width cells contribute zero. *)
Lemma metric_variation_defect_locus_cell_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (n : nat) (a b : R) :
  curve_locally_finite_variation g -> a<=b -> b-a<((n.+1)%:R : R)^-1 ->
  (lebesgue_scalar_measure (metric_variation_defect_locus g n `&` `[a,b])<=
    ((n.+1)%:R*metric_variation_defect g a b)%:E)%E.
Proof.
move=> hg hab hwidth; have hm := lebesgue_scalar_is_measure R.
have hmono := @measure_mono R (real_line_metric R) (@lebesgue_scalar_measure R) hm
  (metric_variation_defect_locus g n `&` `[a,b]) `[a,b] (fun x hx => hx.2).
case: (eqVneq a b)=> [heq|hne].
- by move: hmono; rewrite heq (@lebesgue_scalar_segment R b b (lexx _)) subrr metric_variation_defect_self mulr0.
- have hab' : a<b by rewrite lt_neqAle hne hab.
  case: (pselect (exists x, metric_variation_defect_locus g n x /\ `[a,b] x))=> [[x [hx hxI]]|hempty].
  + have haxb : a<=x<=b by move: hxI; rewrite /= in_itv.
    have hw : 0<b-a<((n.+1)%:R : R)^-1 by apply/andP; split=> //; rewrite subr_gt0.
    have hdef := hx a b haxb hw.
    have hcoef : (0<(n.+1)%:R :> R) by rewrite ltr0n.
    rewrite ltr_pdivrMr // mulrC in hdef.
    apply: le_trans hmono _; rewrite (@lebesgue_scalar_segment R a b hab) lee_fin.
    exact: ltW hdef.
  + have heq : metric_variation_defect_locus g n `&` `[a,b]=set0.
      apply/seteqP; split=> x; last by move=> [].
      by move=> hx; apply: hempty; exists x.
    rewrite heq (measure_empty hm) lee_fin.
    apply: mulr_ge0; first by rewrite ler0n.
    exact (@metric_variation_defect_nonnegative R Y g hg a b hab).
Qed.
