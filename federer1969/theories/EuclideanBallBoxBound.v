(** Federer (1969), 3.1.4, p. 215: the containing coordinate
    box gives alpha(k)<=2^k in the exceptional-set estimate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology ring lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerNormedTopology EuclideanCoordinateMetric EuclideanLebesgueDimensions
  EuclideanBallVolume EuclideanLebesgueBoxes EuclideanLebesgueHaar MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_unit_ball_box_bound]: the estimate
    alpha(k)<=2^k used in Federer 3.1.4, p. 215, second
    inequality for the measures of S_i. Empty coordinates are included. *)
Lemma euclidean_unit_ball_box_bound (R : realType) n :
  euclidean_unit_ball_volume R n<= 2^+n.
Proof.
pose E := inner_metric_space (@euclidean_inner_productP R n).
have hsub : [set x : E | `|x|<1] `<=` [set x : E | forall i, -1<x i<1].
  move=> x hx i; rewrite -ltr_norml.
  apply: le_lt_trans (@euclidean_coordinate_norm_bound R n i x) _; exact hx.
have hh := measure_mono (euclidean_lebesgue_is_measure R n) hsub.
rewrite (euclidean_unit_ball_volumeE R n).1
  (@euclidean_open_box R n (fun _=>-1) (fun _=>1)) in hh; last by move=> i; lra.
move: hh; rewrite lee_fin.
have he : (\prod_(i<n) (1- -1 : R)) = 2^+n.
  have he2 : (1- -1 : R) = 2 by ring.
  by rewrite he2 prodr_const card_ord.
by rewrite he.
Qed.
