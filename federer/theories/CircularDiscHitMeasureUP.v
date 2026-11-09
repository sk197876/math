(** Federer (1969), 3.3.19, p. 303: the
    original family psi_n is specified independently by
    its literal radius-weighted original disc-hit counts. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals classical_sets constructive_ereal.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesSealed FiniteCellHitMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.

(** Source for [is_circular_disc_hit_measures]: literal
    original values psi_n(T)=rho_n card{B in G_n:
    B meets T}, 3.3.19, p. 303. The
    specification assumes no measure law, monotonicity,
    normalization, measurability or limiting identity. *)
Definition is_circular_disc_hit_measures (R:realType)
    (H:nat->{fset inner_metric_space (@euclidean_inner_productP R 2)})
    (psi:nat->set (inner_metric_space (@euclidean_inner_productP R 2))->\bar R):Prop:=
  forall j,is_finite_cell_hit_measure (H j)
    (fun z=>metric_closed_ball z (@FactorialDiscScales.radius R j))
    (@FactorialDiscScales.radius R j) (psi j).
