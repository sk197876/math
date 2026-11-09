(** Federer (1969), 3.3.4, pp. 289–290:
    the original punctured-fibre accumulation
    locus D is Suslin under an actual
    continuous projection-parameter map, by
    3.3.3, p. 288. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureFibreAccumulation StructureFibreSuslin SuslinSetUP SuslinPreimages
  TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_parameter_accumulation_suslin]:
    the original D of Federer 3.3.4,
    pp. 289–290, is Suslin by 3.3.3,
    p. 288. Continuous inverse images
    preserve Suslinness on arbitrary topological
    parameter spaces. No replacement group
    metric, closed source or measure premise
    is needed for this original locus. *)
Theorem structure_parameter_accumulation_suslin (R:realType) n m (hmn:(m<=n)%N)
    (P:topologicalType) (p:P->euclidean_projection_space R n m)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)):
  continuous p ->is_suslin_set R A ->
  is_suslin_set R [set g:P|structure_fibre_accumulation hmn A (a,p g)].
Proof.
move=>hP hA.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose Q:=euclidean_projection_space R n m.
have hPair:continuous (fun g:P=>(a,p g):E*Q).
  apply:topological_pair_continuous; first exact:cst_continuous.
  exact:hP.
exact:(@continuous_preimage_suslin R P (E*Q)%type (fun g:P=>(a,p g))
  (structure_fibre_accumulation hmn A) hPair (structure_fibre_accumulation_suslin hmn hA)).
Qed.
