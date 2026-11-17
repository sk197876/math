(** Federer (1969), 3.4.8(7), p. 329:
    the actual O(n) and its coordinate-fixing
    subgroups have countable open bases. Restrict
    the existing finite-dimensional Hilbert Hom base;
    no new separability theorem is developed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology subtype_topology.
From Federer Require Import Hom InnerProductUP InnerNorm InnerMetric LinearBasis HilbertFormCompactness
  HomInner HomCompositionDeterminant HomSpaceTopology LinearGroupTopology OrthogonalGroupTopology
  InnerSpaceCountableBase CountableOpenBaseUP InitialCountableOpenBase OpenSubspaceMeasure OrthogonalCoordinateFixing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Bases.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation O:=(@orthogonal_group R X B hB n e he).

(** Source for [finite_orthogonal_group_countable_base]: the
    actual ambient group has a countable base,
    supporting product Borel measurability in
    3.4.8(7), p. 329. Apply the existing
    inner-space and relative-topology base theorems. *)
Lemma finite_orthogonal_group_countable_base:
  exists U:nat->set O,is_countable_open_base U.
Proof.
pose hHom:=hom_inner_productP hB hB he.
pose HT:=inner_metric_space hHom.
pose GL:=linear_group hB he.
pose OSet:=orthogonal_group hB he.
pose b:=@hom_rank_one_base R X X n n e he e.
have hBasis:=@hom_rank_one_baseP R X X n n e he e he.
have [U hU]:=@inner_space_countable_open_base R (Hom X X) _ hHom _ b hBasis.
have hGL:=@open_subspace_countable_open_base R HT GL U hU.
have hO:=@open_subspace_countable_open_base R [the pseudoMetricType R of set_type GL] OSet
  (fun i=>set_val @^-1` U i) hGL.
exists (fun i=>set_val @^-1` (set_val @^-1` U i));exact:hO.
Qed.

(** Source for [orthogonal_coordinate_fixing_countable_base]:
    each actual H_j and Q_m has a countable
    relative base, supporting the Haar/Fubini step
    in 3.4.8(7), p. 329. *)
Lemma orthogonal_coordinate_fixing_countable_base (J:set 'I_n):
  exists U:nat->set (@orthogonal_coordinate_fixing_group R X B hB n e he J),is_countable_open_base U.
Proof.
have [U hU]:=finite_orthogonal_group_countable_base.
exists (fun i=>set_val @^-1` U i).
exact:(@initial_countable_open_base
  [the choiceType of set_type (@orthogonal_coordinate_fixing_group R X B hB n e he J)]
  O set_val U hU).
Qed.
End Bases.
