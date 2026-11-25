(** Federer (1969), 3.3.1, p. 287, uses gamma_(n,k) from
    2.7.16(6), p. 139. Specify that probability independently
    by the original invariant-integral representation and total
    mass one; neither a chosen plane nor the kernel map occurs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom HomInner InnerMetric HomSpaceTopology GrassmannSubspaces
  EuclideanInnerProduct FiniteCoordinates
  EuclideanOrthogonalInvariantMeasures GrassmannHomogeneousSpace
  CompactGroupHomogeneousMeasures SubtypeCompactHausdorff HomSpaceTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_euclidean_grassmann_probability]: the actual
    normalized O(n)-invariant probability on G(n,k) in the last
    sentence of Federer 3.3.1, p. 287, defined in 2.7.16(6),
    p. 139. The action on planes is independent of the choice
    of restricted orthogonal group operations. *)
Definition is_euclidean_grassmann_probability (R:realType) n k
    (gamma:set (euclidean_grassmann_space R n k)->\bar R):Prop:=
  @is_normalised_invariant_measure R _
    [the topologicalType of grassmann_space
      (@euclidean_inner_productP R k) (@euclidean_inner_productP R n)
      (@coordinate_basisP R k) (@coordinate_basisP R n)]
    (grassmann_action (@euclidean_inner_productP R k)
      (@euclidean_inner_productP R n) (@coordinate_basisP R k)
      (@coordinate_basisP R n)) gamma.
