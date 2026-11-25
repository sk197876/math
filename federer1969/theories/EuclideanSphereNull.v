(** Federer (1969), 2.7.16, p. 135, supporting 3.1.15, pp. 227–228: every
    Euclidean sphere is Lebesgue null, since the closed and the open ball of
    the same positive radius have the same measure alpha(n) r^n; hence the
    complement of the union of the open annuli about the origin, which is
    the union of the spheres of integer radius together with the origin, is
    null. This is the null exceptional set of the exhaustion in 3.1.15. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  topology constructive_ereal.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  InnerNormedTopology MetricClosedBalls TopologicalBorel MeasureUP MeasureBasic MeasureAlmostBasic
  EuclideanLebesgueDimensions EuclideanBallVolume EuclideanClosedBallVolume EuclideanLebesgueBoxes
  ApproximateDifferentialAffine OpenAnnuliClosedUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SphereNull.
Variable R : realType.
Variable m : nat.
Local Notation hB := (@euclidean_inner_productP R m.+1).
Local Notation E := (inner_metric_space hB).
Local Notation Leb := (@euclidean_lebesgue_measure R m.+1).

(** Source for [euclidean_sphere_null]: Federer 2.7.16, p. 135, supporting
    3.1.15, pp. 227–228: the sphere of radius r > 0 is the closed ball
    minus the open ball; both are Borel, with the same measure
    alpha(n) r^n, so the difference is null. *)
Theorem euclidean_sphere_null (r : R) : 0<r ->
  Leb [set x : R_n R m.+1 | inner_norm hB x=r]=0.
Proof.
move=> hr.
have hm := euclidean_lebesgue_is_measure R m.+1.
pose Bo : set E := [set x : E | `|x - 0| < r].
pose Bc : set E := metric_closed_ball (0 : E) r.
have hS : [set x : R_n R m.+1 | inner_norm hB x = r] = Bc `\` Bo.
  apply/seteqP; split=> x /=.
  - move=> hx; split.
    + by rewrite /Bc /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN hx.
    + by rewrite /Bo /= subr0 inner_norm_topologyE hx ltxx.
  - move=> [hc ho]; apply/eqP; rewrite eq_le; apply/andP; split.
    + by move: hc; rewrite /Bc /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN.
    + move: ho; rewrite /Bo /= subr0 inner_norm_topologyE=> ho.
      by rewrite leNgt; apply/negP.
have hBoE : Bo = [set x : E | mdist (0 : E) x < r].
  by apply/seteqP; split=> x /=; rewrite inner_metric_normE.
have hBo_meas : measure_measurable Leb Bo.
  by apply: euclidean_borel_measurable; apply: open_borel_set; rewrite hBoE; exact: metric_open_ball_open.
have hBoBc : Bo `<=` Bc.
  by move=> x hx; rewrite /Bc /metric_closed_ball /= inner_metric_normE; exact: ltW hx.
have hI : Bc `&` Bo = Bo by apply/setIidPr.
pose v : \bar R := (euclidean_unit_ball_volume R m.+1 * r ^+ m.+1)%:E.
have hfin : v \is a fin_num by [].
have hBov : Leb Bo = v by exact: (euclidean_ball_measure (0 : E) hr).
have hBcv : Leb Bc = v by exact: (euclidean_closed_ball_normalized_volume (0 : E) (ltW hr)).
have h := hBo_meas Bc.
rewrite hI hBov hBcv in h.
rewrite hS -[Leb (Bc `\` Bo)](addeK _ hfin) (addeC _ v) -h; exact: subee hfin.
Qed.

(** Source for [euclidean_annuli_complement_null]: supporting 3.1.15,
    pp. 227–228: a point outside every open annulus about the origin has
    norm equal to its integer part, so it lies on a sphere of integer
    radius; the sphere of radius zero is the origin. The countable union
    of these null sets is null. *)
Theorem euclidean_annuli_complement_null :
  Leb (~` \bigcup_i open_annulus (0 : E) i)=0.
Proof.
have hm := euclidean_lebesgue_is_measure R m.+1.
pose S (i : nat) : set E := [set x : R_n R m.+1 | inner_norm hB x = i%:R].
have hsub : (~` \bigcup_i open_annulus (0 : E) i) `<=` \bigcup_i S i.
  move=> x hx.
  have /andP [hn1 hn2] := truncn_itv (inner_norm_nonnegative hB x).
  exists (Num.truncn (inner_norm hB x))=> //.
  rewrite /S /=; apply/eqP; rewrite eq_le; apply/andP; split=> //.
  rewrite leNgt; apply/negP=> hlt; apply: hx.
  exists (Num.truncn (inner_norm hB x))=> //.
  by rewrite /open_annulus /= inner_metric_distanceE sub0r inner_normN; apply/andP; split.
have hnull : Leb (\bigcup_i S i) = 0.
  apply: (measure_null_countable_union hm (countableP _))=> i _.
  case: i=> [|i].
  - have h0 : S 0%N = [set (0 : E)].
      apply/seteqP; split=> x /=.
      + by move=> hx; apply/eqP; rewrite -(inner_norm_eq0 hB) hx eqxx.
      + by move=> hx; rewrite /S /= hx inner_norm0.
    by rewrite h0; exact: (positive_euclidean_singleton_null (0 : E)).
  - exact: (euclidean_sphere_null (ltr0Sn R i)).
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT -hnull.
exact: (measure_mono hm hsub).
Qed.

End SphereNull.
