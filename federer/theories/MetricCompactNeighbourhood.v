(** General topology supporting Federer (1969), 2.10.4(2), p. 172. An open
    neighbourhood of a compact metric set contains a uniform positive-radius
    thickening. This is the one-coordinate case of the finite-power result
    used in 2.10.3, p. 172; compactness is the finite-cover principle of
    2.2.5, p. 63. Source context and the role of the support argument:
    CompactCoordinateNeighbourhood.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import MetricOpenThickening CompactCoordinateNeighbourhood
  ProductCoordinateNeighborhoods.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Import ArrowAsProduct.

(** Source for [compact_metric_open_thickening]: supporting
    uniform image neighbourhood for the open convex
    comparison of Federer 2.10.4(2), p. 172.
    Empty compact sets are allowed. *)
Theorem compact_metric_open_thickening (R : realType) (X : metricType R)
    (K U : set X) : compact K -> open U -> K `<=` U ->
  exists r : R, 0<r /\ metric_open_thickening K r `<=` U.
Proof.
move=> hK hU hKU.
pose O : set ((unit : Type) -> X) := [set p | U (p tt)].
have hO : open O := @coordinate_cylinder_open [the choiceType of (unit : Type)]
  (fun _ => X) tt U hU.
have hin p : (forall i, K (p i)) -> O p by move=> hp; exact: hKU _ (hp tt).
have [r [hr hb]] := @compact_finite_power_neighbourhood R [the finType of (unit : Type)] X K O hK hO hin.
exists r; split=> // x hx; exact (hb (fun _ => x) (fun _ => hx)).
Qed.
