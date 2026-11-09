(** Federer (1969), 3.3.4, pp. 290–291:
    independent laws for the partial direction map
    T composed with normalization and the actual
    active coordinate projection. Values off the
    nonzero projection domain are auxiliary only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric InnerUnitNormalization SymmetricSquareGeometry
  StructureProjectiveSpace BorelFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_structure_projective_direction_map]:
    the Borel map f=T composed with w composed
    with q in Federer 3.3.4, pp. 290–291.
    The specification retains its exact value
    wherever the original projection is nonzero;
    it specifies no value outside that domain. *)
Definition is_structure_projective_direction_map (R:realType) (X:metricType R)
    m (q:X->inner_metric_space (@euclidean_inner_productP R m.+1))
    (f:X->structure_projective_space R m):=
  is_borel_function f /\ forall x,0<inner_norm (@euclidean_inner_productP R m.+1) (q x) ->
    val (f x)=inner_projective_square
      (inner_unit_normalization (@euclidean_inner_productP R m.+1) (q x)).
