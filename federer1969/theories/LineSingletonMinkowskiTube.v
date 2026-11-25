(** Federer (1969), 3.2.38, p. 275: the constant term in
    the actual Steiner tube polynomial is indispensable even for
    a constant affine map. The actual line point tube has length 2r. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNormedTopology
  EuclideanLebesgueDimensions EuclideanBallVolume MetricOpenThickening MinkowskiContents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [line_singleton_minkowski_tube_quotient]: the
    exact singleton tube in the line, supporting the correction
    of the first displayed estimate in Federer 3.2.38, p. 275.
    The printed sum there starts at j= 1 and would bound this
    positive quantity by zero. The actual j=0 term gives 2r. *)
Lemma line_singleton_minkowski_tube_quotient (R:realType)
    (a:inner_metric_space (@euclidean_inner_productP R 1)) (r:R):
  0<r ->minkowski_tube_quotient 1 [set a] r=(2*r)%:E.
Proof.
move=>hr.
have hTube:metric_open_thickening [set a] r=
    [set x:inner_metric_space (@euclidean_inner_productP R 1) | `|x-a|<r].
  apply/seteqP; split=>x.
  - move=>[b -> hb]; change (is_true (mdist a x<r)) in hb.
    by move:hb; rewrite inner_metric_normE.
  - move=>hx; exists a=>//; change (is_true (mdist a x<r)).
    by rewrite inner_metric_normE.
rewrite /minkowski_tube_quotient hTube subnn euclidean_unit_ball_volume0 expr0 mulr1.
rewrite inve1 mule1 (@euclidean_ball_measure R 1 a r hr).
by rewrite euclidean_unit_ball_volume1.
Qed.
