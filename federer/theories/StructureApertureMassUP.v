(** Federer (1969), 3.3.7, p. 294: original uniform
    conical mass bounds at all positive small apertures. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureCone StructureProjectionKernel EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_structure_aperture_mass_bound]: the displayed
    hypothesis of Federer 3.3.7, p. 294. The original conical outer
    mass is at most lambda alpha(m) r to power m s to power m for
    every original source centre, every positive real radius and
    every positive aperture at most sigma. No projected mass or
    source measurability conclusion is built into this predicate. *)
Definition is_structure_aperture_mass_bound (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))-> \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (sigma lam:R):Prop:=
  forall x,A x ->forall r:R,0<r ->forall s:R,0<s ->s<=sigma ->
    (phi (A `&` structure_cone (structure_projection_kernel hmn p) x r%:E s)<=
      (lam*euclidean_unit_ball_volume R m*r^+m*s^+m)%:E)%E.
