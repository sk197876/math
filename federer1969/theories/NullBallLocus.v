(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureDerivationContext CoveringFamilyUP CoveringRelationUP CoveringRelationFineness
  MetricClosedBalls MetricDiameterUP MetricDiameter VitaliNullFibers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [measure_null_ball_points]: direct set P in
    Federer 2.9.15, p. 160. A point belongs to P when
    some positive-radius centered closed ball has zero phi mass. *)
Definition measure_null_ball_points (R : realType) (X : metricType R)
    (phi : set X -> \bar R) : set X :=
  [set x | exists r : R, (0<r)%R /\ phi (metric_closed_ball x r)=0].

(** Source for [measure_null_ball_points_open]: direct openness
    assertion for P in Federer 2.9.15, p. 160. A half-
    radius neighbourhood stays within the zero-mass ball; only
    the measure law and metric triangle inequality are required. *)
Lemma measure_null_ball_points_open (R : realType) (X : metricType R)
    (phi : set X -> \bar R) :
  is_measure phi -> open (measure_null_ball_points phi).
Proof.
move=> hm; rewrite openE=> a [r [hr hz]].
have he : (0<r/2)%R by rewrite divr_gt0 // ltr0n.
apply: (metricType_numDomainType.nbhs_mdistP a _).2.
exists (r/2)%R=> // x hx; exists (r/2)%R; split=> //.
apply: (@measure_null_subset R X phi hm _ (metric_closed_ball a r) _ hz).
move=> z hzball.
have htri := metric_triangle a x z.
have hh := le_trans htri (lerD (ltW hx) hzball).
rewrite /metric_closed_ball /=; by lra.
Qed.

(** Source for [measure_null_ball_points_null]: direct nullity
    of P in the proof of Federer 2.9.15, p. 160, by
    2.9.5, p. 154. Keep the existing Vitali relation from
    the section's standing context: every sufficiently small
    related cell inside a null ball is itself null. Its fine
    null-cell locus has zero measure by the selection law. *)
Lemma measure_null_ball_points_null (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> phi (measure_null_ball_points phi)=0.
Proof.
move=> hc; have hm := derivation_measure_law (derivation_context_measure hc).
have hv := derivation_context_vitali hc.
apply: (@measure_null_subset R X phi hm _
  [set x | covering_relation_fine_at (fun x S => V x S /\ phi S=0) x] _
  (@vitali_null_fine_points_null R X phi V hm hv)).
move=> x [r [hr hz]].
apply: (covering_relation_fine_iff_small_diameter _ x).2=> e he.
pose d := (Num.min e r)%R.
have hd : (0<d)%R by rewrite /d lt_min he hr.
have [S [hS hdiam]] := (covering_relation_fine_iff_small_diameter V x).1
  (vitali_relation_fine hv x) d hd.
have hde : extended_metric_diameter S<e%:E.
  apply: lt_le_trans hdiam _; by rewrite lee_fin /d ge_min lexx.
have hdr : extended_metric_diameter S<r%:E.
  apply: lt_le_trans hdiam _; by rewrite lee_fin /d ge_min lexx orbT.
have hsub : S `<=` metric_closed_ball x r.
  move=> z hzS.
  have hxS := @vitali_relation_covering R X phi V hv x S hS.
  have hdist := metric_diameter_upper (extended_metric_diameter_specification S) hxS hzS.
  have hh := le_lt_trans hdist hdr; rewrite lte_fin in hh; exact: ltW hh.
have hzS := @measure_null_subset R X phi hm S (metric_closed_ball x r) hsub hz.
exists S; split=> //; by split.
Qed.

(** Source for [outside_null_ball_points_positive]: supporting
    positive denominators on X minus P in Federer 2.9.15,
    p. 160. This is positivity of every positive-radius
    centered ball at the specified point, without asserting
    positivity on balls centered elsewhere. *)
Lemma outside_null_ball_points_positive (R : realType) (X : metricType R)
    (phi : set X -> \bar R) x (r : R) :
  is_measure phi -> ~ measure_null_ball_points phi x -> (0<r)%R ->
  0<phi (metric_closed_ball x r).
Proof.
move=> hm hx hr; rewrite lt_def (measure_nonnegative hm) andbT.
apply/negP=> /eqP hz; apply: hx; by exists r.
Qed.
