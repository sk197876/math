(** Federer (1969), 3.4.12, p. 339: original unitary and
    coordinate-fixing groups inherit countable relative open bases.
    Apply the existing orthogonal-group and initial-topology base
    theorems; no new separability proof is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  HermitianUP HermitianRealImaginary HermitianComplexLinearity InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  OrthogonalMaps OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  UnitaryGroup UnitaryComplexMapSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
From Federer Require Import HomSpaceTopology TopologicalGroupUP IsotropyGroupTopology TopologicalProductMaps
  SubtypeCompactHausdorff HomogeneousSpaceUP CompactGroupHomogeneousMeasures UnitaryGroupClosed
  UnitaryCoordinateFixing UnitaryCoordinateFixingHaar UnitarySphereTransitivity UnitaryHermitianPreservation.
From Federer Require Import OrthogonalCoordinateCountableBase CountableOpenBaseUP InitialCountableOpenBase.
Section Bases.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Variable N:nat.
Variable r:'I_N->XR.
Variable hr:is_basis r.
Local Notation O:=(@orthogonal_group R XR B hB N r hr).
Local Notation U:=(@unitary_group R X H hH N r hr).
Local Notation L:=(fun g:U=>@UnitaryComplexMap.value R X H hH N r hr g).


(** Source for [unitary_group_countable_base]: the original
    relative topology of U(n) has a countable open base,
    supporting complex Haar/Fubini, 3.4.12, p. 339. *)
Lemma unitary_group_countable_base:exists V:nat->set U,is_countable_open_base V.
Proof.
have [V hV]:=@finite_orthogonal_group_countable_base R XR B hB N r hr.
exists (fun i=>set_val @^-1` V i).
exact:(@initial_countable_open_base [the choiceType of set_type U] O set_val V hV).
Qed.

(** Source for [unitary_coordinate_fixing_countable_base]: every
    original coordinate-fixing unitary subgroup has a countable
    relative open base, 3.4.12, p. 339. *)
Lemma unitary_coordinate_fixing_countable_base n (e:'I_n->X) (J:set 'I_n):
  exists V:nat->set (@unitary_coordinate_fixing_group R X H hH N r hr n e J),is_countable_open_base V.
Proof.
have [V hV]:=unitary_group_countable_base.
exists (fun i=>set_val @^-1` V i).
exact:(@initial_countable_open_base
  [the choiceType of set_type (@unitary_coordinate_fixing_group R X H hH N r hr n e J)] U set_val V hV).
Qed.
End Bases.
