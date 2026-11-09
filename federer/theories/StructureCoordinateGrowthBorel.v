(** Federer (1969), 3.3.4, p. 289:
    the actual one-coordinate upper growth
    is Borel in a continuous frame
    family, by the published corrected
    3.3.2 argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  StructureConeUP StructureCoordinateGrowth StructureCoordinateCostOpen
  StructureRadialCostLimits StructureLimsupLevels StructureLimsupBorel
  StructureBorelValueFibres TopologicalBorel BorelFunctionUP PositiveRadiusLimits ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_coordinate_upper_growth_borel]:
    supporting the Borel B_j and C_j
    assertion in Federer 3.3.4, p. 289.
    Apply the corrected strict-margin and
    reciprocal-cutoff formula of 3.3.2,
    erratum pp. 5–6, to the original
    coordinate-cone costs. Arbitrary A and
    all extended density values remain. *)
Theorem structure_coordinate_upper_growth_borel (R:realType) m k
    (P:topologicalType) (f:P->{linear R_n R (m+k)->R_n R (m+k)})
    (phi:set (inner_metric_space (@euclidean_inner_productP R (m+k)))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R (m+k))))
    (a:inner_metric_space (@euclidean_inner_productP R (m+k))) (j:'I_k) (delta:R):
  continuous (fun z:P*inner_metric_space (@euclidean_inner_productP R (m+k))=>
    (f z.1 (z.2-a):inner_metric_space (@euclidean_inner_productP R (m+k)))) ->
  is_structure_measure phi ->
  is_borel_function (fun p:P=>
    (positive_radius_upper_limit (structure_coordinate_radial_supremum phi A a (f p) j delta)
      :extended_real_line R)).
Proof.
move=>hF hPhi.
have hEqual:(fun p:P=>positive_radius_upper_limit
    (structure_coordinate_radial_supremum phi A a (f p) j delta))=
    (fun p:P=>structure_tail_upper_limit
      (fun p r s=>structure_coordinate_cost phi A a (f p) j r s) delta p).
  apply:funext=>p; exact:structure_radial_cost_upper_limitE.
rewrite hEqual; apply:structure_tail_upper_limit_borel=>r s hr hs b.
exact:(@structure_coordinate_cost_superlevel_open R m k P f phi A a j r s b hF hPhi hr hs).
Qed.

(** Source for [structure_coordinate_upper_growth_value_borel]:
    Borelness of each exact density value
    used in B_j/C_j, Federer 3.3.4,
    p. 289. Zero and infinity are
    genuine value fibres of the original
    extended-real Borel growth function. *)
Theorem structure_coordinate_upper_growth_value_borel (R:realType) m k
    (P:topologicalType) (f:P->{linear R_n R (m+k)->R_n R (m+k)})
    (phi:set (inner_metric_space (@euclidean_inner_productP R (m+k)))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R (m+k))))
    (a:inner_metric_space (@euclidean_inner_productP R (m+k))) (j:'I_k) (delta:R) (c: \bar R):
  continuous (fun z:P*inner_metric_space (@euclidean_inner_productP R (m+k))=>
    (f z.1 (z.2-a):inner_metric_space (@euclidean_inner_productP R (m+k)))) ->
  is_structure_measure phi ->
  borel_set [set p:P|
    positive_radius_upper_limit (structure_coordinate_radial_supremum phi A a (f p) j delta)=c].
Proof.
move=>hF hPhi; apply:structure_borel_value_fibre.
exact:(@structure_coordinate_upper_growth_borel R m k P f phi A a j delta hF hPhi).
Qed.
