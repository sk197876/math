(** Opaque actual upper limit for Federer (1969), 3.3.2,
    pp. 287–288. Only its independently stated order laws
    are exposed; the existence witness remains private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeDensityUP StructureConeDensityConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type StructureConeDensitySignature.
(** Source for [value]: actual cone-density upper limit of
    Federer 3.3.2, pp. 287–288, specified before existence. *)
Parameter value:forall (R:realType) n m (hmn:(m<=n)%N),
  (set (inner_metric_space (@euclidean_inner_productP R n))->\bar R) ->
  set (inner_metric_space (@euclidean_inner_productP R n)) ->R ->
  inner_metric_space (@euclidean_inner_productP R n)*
    euclidean_projection_space R n m ->\bar R.
(** Source for [laws]: independent upper-limit order laws
    of Federer 3.3.2, pp. 287–288, for the public value. *)
Parameter laws:forall (R:realType) n m (hmn:(m<=n)%N) phi A delta,
  is_structure_cone_density hmn phi A delta (@value R n m hmn phi A delta).
End StructureConeDensitySignature.

Module StructureConeDensity:StructureConeDensitySignature.
(** Source for [value]: private realization of proved
    existence for Federer 3.3.2, pp. 287–288. *)
Definition value (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (delta:R):=
  projT1 (cid (structure_cone_density_exists hmn phi A delta)).
(** Source for [laws]: the realization satisfies exactly
    the prior specification of Federer 3.3.2, pp. 287–288. *)
Lemma laws (R:realType) n m (hmn:(m<=n)%N) phi A delta:
  is_structure_cone_density hmn phi A delta (@value R n m hmn phi A delta).
Proof. exact:projT2 (cid (structure_cone_density_exists hmn phi A delta)). Qed.
End StructureConeDensity.
