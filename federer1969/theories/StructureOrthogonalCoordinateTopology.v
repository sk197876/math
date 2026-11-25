(** Federer (1969), 3.3.4, p. 289:
    actual orthogonal inverse-frame coordinates
    are jointly continuous, and the original
    B_j/C_j are Borel on the actual
    orthogonal group. All topology premises
    of the generic cost argument are discharged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import Hom HomInner HomSpaceTopology GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric InnerNormedTopology EuclideanOrthogonalInvariantMeasures
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure EuclideanOrthogonalBlockExtension
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed TopologicalGroupUP TopologicalProductMaps
  StructureConeUP StructureCoordinateAlternatives StructureCoordinateAlternativesBorel TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Coordinates.
Variable R:realType.
Variables m k:nat.
Local Notation O:=(euclidean_orthogonal_group R (m+k)).
Local Notation P:=[the topologicalType of set_type O].
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R (m+k))).
Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction
  (linear_group_mul (@euclidean_inner_productP R (m+k)) (@coordinate_basisP R (m+k)))
  (linear_group_inv (@euclidean_inner_productP R (m+k)) (@coordinate_basisP R (m+k)))
  (linear_group_unit (@euclidean_inner_productP R (m+k)) (@coordinate_basisP R (m+k)))
  O mulS invS eS.
Variable a:E.

(** Source for [structure_orthogonal_inverse_coordinates_continuous]:
    the actual continuous inverse-frame
    evaluation used for B_j and C_j
    in Federer 3.3.4, p. 289.
    Original group inversion and evaluation
    are continuous, as is subtraction of
    the fixed original centre. *)
Theorem structure_orthogonal_inverse_coordinates_continuous:
  continuous (fun z:P*E=>(orthogonal_element_map (invS z.1) (z.2-a):E)).
Proof.
have hInverse:=topological_group_inv_continuous (lch_group_topological (orthogonal_group_lch hS)).
have hPair:continuous (fun z:P*E=>(invS z.1,z.2-a):P*E).
  apply:topological_pair_continuous.
  - move=>z; exact:(continuous_comp (@first_projection_continuous P E z) (hInverse z.1)).
  - move=>z; apply:cvgB; first exact:(@second_projection_continuous P E z).
    exact:cvg_cst.
move=>z; exact:(continuous_comp (hPair z)
  (@euclidean_orthogonal_evaluation_continuous R (m+k) (invS z.1,z.2-a))).
Qed.

(** Source for [structure_orthogonal_coordinate_B_borel]:
    B_j is Borel on the actual O(n),
    Federer 3.3.4, p. 289. The
    original inverse frame and centre are
    used, with no continuity premise left
    for the numbered theorem to discharge. *)
Theorem structure_orthogonal_coordinate_B_borel (phi:set E->\bar R) (A:set E) (j:'I_k):
  is_structure_measure phi ->borel_set [set g:P|
    structure_coordinate_zero_growth phi A a (hom_as_linear (orthogonal_element_map (invS g))) j].
Proof.
move=>hPhi.
exact:(@structure_coordinate_B_borel R m k P
  (fun g:P=>hom_as_linear (orthogonal_element_map (invS g))) phi A a j
  structure_orthogonal_inverse_coordinates_continuous hPhi).
Qed.

(** Source for [structure_orthogonal_coordinate_C_borel]:
    C_j is Borel on the actual O(n),
    Federer 3.3.4, p. 289. Every
    original positive radial cutoff and
    infinite upper limit remains in its
    exact actual inverse-frame condition. *)
Theorem structure_orthogonal_coordinate_C_borel (phi:set E->\bar R) (A:set E) (j:'I_k):
  is_structure_measure phi ->borel_set [set g:P|
    structure_coordinate_infinite_growth phi A a (hom_as_linear (orthogonal_element_map (invS g))) j].
Proof.
move=>hPhi.
exact:(@structure_coordinate_C_borel R m k P
  (fun g:P=>hom_as_linear (orthogonal_element_map (invS g))) phi A a j
  structure_orthogonal_inverse_coordinates_continuous hPhi).
Qed.
End Coordinates.
