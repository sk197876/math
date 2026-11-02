(** Federer (1969), 3.2.37, pp. 273--274: finite sources in
    degree zero. Small balls around distinct finite source points
    are disjoint, including the ambient-zero unit atom. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNormedTopology EuclideanLebesgueDimensions
  EuclideanBallVolume MetricOpenThickening FiniteMetricSeparation MetricClosedBalls
  MeasureUP MeasureBasic MeasureFiniteAdditivity BorelRegularMeasureUP TopologicalBorel.
From mathcomp Require Import num_normedtype pseudometric_normed_Zmodule normed_module.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_point_tube_volume]: supporting exact finite
    tube mass for the degree-zero boundary of Federer 3.2.37,
    pp. 273--274. At sufficiently small positive radii, a finite
    source has one full Euclidean ball per point. Empty sources,
    singleton sources and ambient dimension zero are retained. *)
Theorem finite_point_tube_volume (R:realType) n
    (B:{fset inner_metric_space (@euclidean_inner_productP R n)}):
  exists e:R,(0<e)%R /\ forall r:R,(0<r<e)%R ->
    @euclidean_lebesgue_measure R n (metric_open_thickening [set` B] r)=
      (#|` B|%:R*(euclidean_unit_ball_volume R n*r^+n))%:E.
Proof.
have [d [hd hSeparated]]:=finite_metric_points_separated (R:=R) B.
exists (d/2)%R; split; first by rewrite divr_gt0 // ltr0n.
move=>r /andP[hr hrd].
pose X:=[the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose F:=fun a:X=>[set x:X|(mdist a x<r)%R].
have hMeasurable a:measure_measurable (@euclidean_lebesgue_measure R n) (F a).
  apply:(@borel_regular_borel_measurable R X (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_borel_regular R n)).
  exact:open_borel_set (metric_open_ball_open a r).
have hDisjoint a b: a \in B -> b \in B -> a!=b ->
    forall x,F a x ->F b x ->False.
  move=>ha hb hab x hax hbx.
  have hs:=hSeparated a b ha hb hab.
  have ht:=metric_triangle a x b.
  rewrite (metric_sym x b) in ht.
  change (is_true (mdist a x<r)%R) in hax.
  change (is_true (mdist b x<r)%R) in hbx.
  have hbad:(d<d)%R by lra.
  by rewrite ltxx in hbad.
have hVolume a:@euclidean_lebesgue_measure R n (F a)=
    (euclidean_unit_ball_volume R n*r^+n)%:E.
  have hMetric (x:X):(mdist a x=`|x-a|)%R.
    by rewrite inner_metric_normE.
  have hE:F a=[set x:X|(`|x-a|<r)%R].
    apply/seteqP; split=>x.
    + change ((mdist a x<r)%R ->(`|x-a|<r)%R); by rewrite hMetric.
    + change ((`|x-a|<r)%R ->(mdist a x<r)%R); by rewrite hMetric.
  rewrite hE; exact:euclidean_ball_measure hr.
rewrite /metric_open_thickening
  (@measure_finite_disjoint_additivity R X X _ (euclidean_lebesgue_is_measure R n)
    F B (fun a _=>hMeasurable a) hDisjoint).
rewrite (eq_bigr (fun _=>(euclidean_unit_ball_volume R n*r^+n)%:E)); last by move=>a _; exact:hVolume.
rewrite sumEFin big_seq_fsetE sumr_const cardT cardfE cardE.
exact (congr1 (@EFin R) (esym (mulr_natl
  (euclidean_unit_ball_volume R n*r^+n)%R _))).
Qed.
