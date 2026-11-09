(** Public cone-density upper limit of Federer (1969),
    3.3.2, pp. 287–288. Later proofs use only the
    sealed independent order laws. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeDensityUP StructureConeDensitySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [structure_cone_density]: the actual
    extended-valued function of (a,p) in Federer 3.3.2,
    p. 287, with every positive aperture cutoff retained. *)
Definition structure_cone_density (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (delta:R):=
  @StructureConeDensity.value R n m hmn phi A delta.

(** Source for [structure_cone_density_specification]:
    independent order laws of the upper limit in Federer
    3.3.2, pp. 287–288, with no Borel conclusion assumed. *)
Lemma structure_cone_density_specification (R:realType) n m (hmn:(m<=n)%N)
    phi A delta:
  @is_structure_cone_density R n m hmn phi A delta
    (@structure_cone_density R n m hmn phi A delta).
Proof. exact:StructureConeDensity.laws. Qed.
