(** Federer (1969), 3.4.12, p. 339:
    the actual original U(n) carries Haar measure.
    Prove its compactness and local compact Hausdorff
    group structure before applying the existing Haar theorem.
    Every group operation is constructed inside existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  HermitianUP HermitianRealImaginary InnerMetric LinearBasis HomInner
  LinearGroupTopology LinearGroupSealed OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  TopologicalGroupUP IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  UnitaryGroup UnitaryGroupClosed UnitaryGroupSubgroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Haar.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Variable N:nat.
Variable e:'I_N->XR.
Variable he:is_basis e.
Local Notation O:=(@orthogonal_group R XR B hB N e he).
Local Notation S:=(@unitary_group R X H hH N e he).

(** Source for [unitary_group_compact]: the actual
    unitary group is compact in its original relative
    topology, as needed in 3.4.12, p. 339. *)
Theorem unitary_group_compact:compact [set:S].
Proof.
have hClosed:=@unitary_group_closed R X H hH N e he.
have hCompact:compact S.
  have hSame:S=[set:O] `&` S by rewrite setTI.
  rewrite hSame;exact:(compact_closedI (@orthogonal_group_compact_space R XR B hB N e he) hClosed).
have hSame:[set:S]=(set_val @^-1` S:set S).
  apply/seteqP;split=>g _;first exact:set_valP;exact:Logic.I.
rewrite hSame;exact:(@set_type_compact_preimage O S S hCompact (@subset_refl O S)).
Qed.

(** Source for [unitary_group_haar_exists]: construct
    the original unitary group operations and its Haar
    measure, 3.4.12, p. 339. The returned
    operation equations refer to the actual orthogonal maps;
    no compactness or group-existence premise is added. *)
Theorem unitary_group_haar_exists:
  exists (mulO:O->O->O) (invO:O->O) (unitO:O),
    is_subgroup_restriction (@linear_group_mul R XR B hB N e he)
      (@linear_group_inv R XR B hB N e he) (@linear_group_unit R XR B hB N e he)
      O mulO invO unitO /\
    exists (mulS:S->S->S) (invS:S->S) (unitS:S),
      is_subgroup_restriction mulO invO unitO S mulS invS unitS /\
      is_locally_compact_hausdorff_group mulS invS unitS /\
      exists mu:set S->\bar R,is_normalised_haar_measure mulS mu.
Proof.
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R XR B hB N e he.
have hSub:=@unitary_group_subgroup R X H hH N e he mulO invO unitO hO.
have [mulS [invS [unitS hS]]]:=subgroup_restriction_exists hSub.
have hLocally:=@subgroup_restriction_locally_compact_hausdorff O mulO invO unitO
  S mulS invS unitS hS (@orthogonal_group_lch R XR B hB N e he mulO invO unitO hO)
  (@unitary_group_closed R X H hH N e he).
exists mulO,invO,unitO;split;first exact:hO.
exists mulS,invS,unitS;split;first exact:hS.
split;first exact:hLocally.
exact:(normalised_haar_measure_exists R hLocally unitary_group_compact).
Qed.
End Haar.
