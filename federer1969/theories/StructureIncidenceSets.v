(** Federer (1969), 3.3.10, p. 296: the three original
    incidence sets in A times G(n,n-m). Their definitions use
    only the original alternatives, without conclusion fields. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct InnerMetric
  FiniteCoordinates HomInner HomSpaceTopology GrassmannHomogeneousSpace StructurePlaneGrowth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section Incidences.
Variable R:realType.
Variables n m:nat.
Variable phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R.
Variable A:set (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R n)).
Local Notation W:=(grassmann_space (@euclidean_inner_productP R (n-m))
  (@euclidean_inner_productP R n) (@coordinate_basisP R (n-m)) (@coordinate_basisP R n)).

(** Source for [structure_first_incidence]: ORIGINAL S1 in
    Federer 3.3.10, p. 296: pairs in A times the actual Grassmann
    space satisfying ordinary zero growth in condition (1) of
    3.3.4, p. 288, for the original A and original phi. *)
Definition structure_first_incidence:set (X*W):=
  [set z|A z.1 /\structure_plane_zero_growth m phi A z.1 z.2].

(** Source for [structure_second_incidence]: ORIGINAL S2 in
    Federer 3.3.10, p. 296: pairs in A times the actual Grassmann
    space satisfying infinite upper growth in condition (2) of
    3.3.4, p. 288, at every positive original radial cutoff. *)
Definition structure_second_incidence:set (X*W):=
  [set z|A z.1 /\structure_plane_infinite_growth m phi A z.1 z.2].

(** Source for [structure_third_incidence]: ORIGINAL S3 in
    Federer 3.3.10, p. 296: pairs in A times the actual Grassmann
    space satisfying punctured affine-plane accumulation in
    condition (3) of 3.3.4, p. 288. No original fibre infinitude
    or projected-nullity conclusion is part of the definition. *)
Definition structure_third_incidence:set (X*W):=
  [set z|A z.1 /\structure_plane_accumulation A z.1 z.2].
End Incidences.
