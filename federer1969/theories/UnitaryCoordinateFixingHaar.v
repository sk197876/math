(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(4),
    p. 326: every original unitary coordinate-fixing group
    is compact and has Haar measure. Actual closedness and
    subgroup restriction discharge every existence premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner InnerMetric ScalarRestriction ComplexScalarSealed HermitianUP HermitianRealImaginary LinearBasis
  LinearGroupTopology LinearGroupSealed OrthogonalGroupTopology TopologicalGroupUP IsotropyGroupTopology
  UnitaryGroup UnitaryGroupHaar UnitaryCoordinateFixing HaarIntegralUP CompactGroupHaarNormalisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Haar.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable N:nat.
Variable r:'I_N->restricted_space (ComplexScalars.embed R) X.
Variable hr:is_basis r.
Variable n:nat.
Variable e:'I_n->X.
Variable J:set 'I_n.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Local Notation O:=(@orthogonal_group R XR B hB N r hr).
Local Notation U:=(@unitary_group R X H hH N r hr).
Local Notation S:=(@unitary_coordinate_fixing_group R X H hH N r hr n e J).

(** Source for [unitary_coordinate_fixing_compact]: the actual
    fixing group is compact in its own relative topology,
    3.4.12, p. 339, including empty fixed-vector families. *)
Lemma unitary_coordinate_fixing_compact:compact [set:S].
Proof.
have hClosed:=@unitary_coordinate_fixing_closed R X H hH N r hr n e J.
have hCompact:compact S.
  have hSame:S=[set:U] `&` S by rewrite setTI.
  rewrite hSame;exact:(compact_closedI (@unitary_group_compact R X H hH N r hr) hClosed).
have hSame:[set:S]=(set_val @^-1` S:set S).
  apply/seteqP;split=>g _;first exact:set_valP;exact:Logic.I.
rewrite hSame;exact:(@set_type_compact_preimage U S S hCompact (@subset_refl U S)).
Qed.

(** Source for [unitary_coordinate_fixing_haar_exists]: construct
    actual original unitary and fixing-group operations and a
    normalized Haar witness, 3.4.12, p. 339. No abstract
    group, compactness or Haar existence conclusion is a premise. *)
Theorem unitary_coordinate_fixing_haar_exists:
  exists (mulO:O->O->O) (invO:O->O) (unitO:O),
    is_subgroup_restriction (@linear_group_mul R XR B hB N r hr)
      (@linear_group_inv R XR B hB N r hr) (@linear_group_unit R XR B hB N r hr)
      O mulO invO unitO /\
    exists (mulU:U->U->U) (invU:U->U) (unitU:U),
      is_subgroup_restriction mulO invO unitO U mulU invU unitU /\
      is_locally_compact_hausdorff_group mulU invU unitU /\
      exists (mulS:S->S->S) (invS:S->S) (unitS:S),
        is_subgroup_restriction mulU invU unitU S mulS invS unitS /\
        is_locally_compact_hausdorff_group mulS invS unitS /\
        exists mu:set S->\bar R,is_normalised_haar_measure mulS mu.
Proof.
have [mulO [invO [unitO [hO [mulU [invU [unitU [hU [hLocalU hHaarU]]]]]]]]]:=
  @unitary_group_haar_exists R X H hH N r hr.
have hSub:=@unitary_coordinate_fixing_subgroup R X H hH N r hr n e mulO invO unitO hO mulU invU unitU hU J.
have [mulS [invS [unitS hS]]]:=subgroup_restriction_exists hSub.
have hLocalS:=@subgroup_restriction_locally_compact_hausdorff U mulU invU unitU S mulS invS unitS hS hLocalU
  (@unitary_coordinate_fixing_closed R X H hH N r hr n e J).
exists mulO,invO,unitO;split;first exact:hO.
exists mulU,invU,unitU;split;first exact:hU.
split;first exact:hLocalU.
exists mulS,invS,unitS;split;first exact:hS.
split;first exact:hLocalS.
exact:(normalised_haar_measure_exists R hLocalS unitary_coordinate_fixing_compact).
Qed.
End Haar.
