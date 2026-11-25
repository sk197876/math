(** Federer (1969), 3.3.4, p. 289:
    the original one-coordinate costs and
    positive-radius suprema defining B_j and
    C_j. Frames stay local parameters. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  StructureCoordinateCones StructureRadialCostLimits PositiveRadiusLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_coordinate_cost]: the
    original value phi[I_j(r,g,s)] r^(-m)s^(-m)
    in Federer 3.3.4, p. 289. The
    frame inverse is supplied as the actual
    linear coordinate map; radius and aperture
    remain the original real variables. *)
Definition structure_coordinate_cost (R:realType) m k
    (phi:set (inner_metric_space (@euclidean_inner_productP R (m+k)))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R (m+k))))
    (a:inner_metric_space (@euclidean_inner_productP R (m+k)))
    (f:{linear R_n R (m+k)->R_n R (m+k)}) (j:'I_k) (r s:R): \bar R:=
  (phi (structure_coordinate_cone A a f j r%:E s)*
    ((r^-1)^+m)%:E*((s^-1)^+m)%:E)%E.

(** Source for [structure_coordinate_radial_supremum]:
    the literal sup over 0<r<delta
    defining B_j and C_j in Federer
    3.3.4, p. 289. The actual arbitrary
    original source and measure are retained. *)
Definition structure_coordinate_radial_supremum (R:realType) m k
    (phi:set (inner_metric_space (@euclidean_inner_productP R (m+k)))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R (m+k))))
    (a:inner_metric_space (@euclidean_inner_productP R (m+k)))
    (f:{linear R_n R (m+k)->R_n R (m+k)}) (j:'I_k) (delta s:R):=
  structure_radial_cost_supremum
    (fun g r t=>structure_coordinate_cost phi A a g j r t) delta f s.
