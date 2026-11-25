(** Federer (1969), 3.3.20, p. 308:
    independent literal original square-hit measure laws. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals classical_sets constructive_ereal.
From Federer Require Import EuclideanInnerProduct InnerMetric CompactIntervalGauge
  EuclideanIntervalRectangles FiniteCellHitMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_critical_square_hit_measures]: the
    original psi_j(S)=sqrt(2)/4^j times the number
    of original level squares meeting S in 3.3.20,
    p. 308. No outer-measure, monotonicity, total
    mass, diameter estimate or limit identity is an
    assumed specification field. The auxiliary family stays local. *)
Definition is_critical_square_hit_measures (R:realType)
    (G:nat->{fset (compact_real_intervals R*compact_real_intervals R)})
    (psi:nat->set (inner_metric_space (@euclidean_inner_productP R 2))->\bar R):Prop:=
  forall j,is_finite_cell_hit_measure (G j)
    (fun P=>euclidean_interval_rectangle P.1 P.2) (Num.sqrt 2/(4:R)^+j) (psi j).
