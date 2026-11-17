(** Federer (1969), 3.4.8(4), p. 326:
    the original H_j and Q_m carry Haar measures.
    Closedness and compactness are proved from their
    actual fixed-vector equations before Haar existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  HomInner LinearGroupTopology LinearGroupSealed TopologicalGroupUP IsotropyGroupTopology OrthogonalGroupTopology
  OrthogonalCoordinateFixing HaarIntegralUP CompactGroupHaarNormalisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Haar.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation O:=(@orthogonal_group R X B hB n e he).
Variable J:set 'I_n.
Local Notation S:=(@orthogonal_coordinate_fixing_group R X B hB n e he J).

(** Source for [orthogonal_coordinate_fixing_compact]: the
    original fixed-coordinate subgroup is compact in
    its own relative topology, supporting 3.4.8(4), p. 326. *)
Lemma orthogonal_coordinate_fixing_compact:compact [set: S].
Proof.
have hClosed:=@orthogonal_coordinate_fixing_closed R X B hB n e he J.
have hCompact:compact S.
  have hSame:S = [set: O] `&` S by rewrite setTI.
  rewrite hSame;exact:(compact_closedI (@orthogonal_group_compact_space R X B hB n e he) hClosed).
have hSame:[set: S] = (set_val @^-1` S:set S).
  apply/seteqP;split=>g _;first exact:set_valP.
  exact:Logic.I.
rewrite hSame;exact:(@set_type_compact_preimage O S S hCompact (@subset_refl O S)).
Qed.

Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.
Variables (mulS:S->S->S) (invS:S->S) (unitS:S).
Hypothesis hS:is_subgroup_restriction mulO invO unitO S mulS invS unitS.

(** Source for [orthogonal_coordinate_fixing_lch]: the
    original H_j and Q_m satisfy the standing
    locally compact Hausdorff group laws,
    3.4.8(4), p. 326. *)
Lemma orthogonal_coordinate_fixing_lch:is_locally_compact_hausdorff_group mulS invS unitS.
Proof.
exact:(@subgroup_restriction_locally_compact_hausdorff O mulO invO unitO S mulS invS unitS hS
  (@orthogonal_group_lch R X B hB n e he mulO invO unitO hO)
  (@orthogonal_coordinate_fixing_closed R X B hB n e he J)).
Qed.

(** Source for [orthogonal_coordinate_fixing_haar_exists]: an
    actual Haar measure exists on each original
    fixed-coordinate subgroup, 3.4.8(4), p. 326.
    Normalisation is a permissible local witness choice. *)
Theorem orthogonal_coordinate_fixing_haar_exists:
  exists mu:set S->\bar R,is_normalised_haar_measure mulS mu.
Proof.
exact:(normalised_haar_measure_exists R orthogonal_coordinate_fixing_lch
  orthogonal_coordinate_fixing_compact).
Qed.
End Haar.
