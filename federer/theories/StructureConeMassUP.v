(** Federer (1969), 3.3.6, p. 293: independent statement
    of the original uniform conical outer-mass hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureCone StructureProjectionKernel EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_structure_uniform_cone_mass_bound]: supporting extended-radius version of the first
    display of Federer 3.3.6, p. 293: the ORIGINAL conical mass is at
    most lambda alpha(m) r to power m s to power m for every original
    source centre and every positive radius at most xi. The radius
    and cutoff may be infinite; the complete numbered theorem needs only
    the finite-radius instances. This predicate assumes neither the
    cylinder bound nor its upper-density consequence. *)
Definition is_structure_uniform_cone_mass_bound (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))-> \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (s lam:R) (xi: \bar R):Prop:=
  forall x,A x ->forall r: \bar R,(0<r)%E ->(r<=xi)%E ->
    (phi (A `&` structure_cone (structure_projection_kernel hmn p) x r s)<=
      lam%:E*(euclidean_unit_ball_volume R m)%:E*r^+m*(s^+m)%:E)%E.
