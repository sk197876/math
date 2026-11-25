(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(4),
    p. 326: original unitary prefix and suffix groups fix
    the prescribed complex basis vectors. The existing opaque
    pointwise-fixing laws specify their actual members. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals topology subtype_topology.
From Federer Require Import Hom HomInner InnerMetric RealNormUP ScalarRestriction ComplexScalarSealed HermitianUP HermitianRealImaginary
  InnerNorm HilbertFormCompactness NormMetric RealMetricBackground LinearBasis LinearGroupTopology LinearGroupSealed
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure TopologicalGroupUP IsotropyGroupTopology
  AnalyticOrthogonalJointContinuity UnitaryGroup PointwiseFixingLocusUP PointwiseFixingLocusSealed
  PointwiseFixingSubgroup PointwiseFixingClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Fixing.
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
Local Notation XT:=(real_norm_metric_space (inner_norm_real_norm hB)).
Local Notation action:=(fun g:U=>@orthogonal_element_map R XR B hB N r hr (set_val g)).
Variable n:nat.
Variable e:'I_n->X.

(** Source for [unitary_coordinate_fixing_group]: the actual
    original coordinate-fixing subset of U(n), 3.4.12, p. 339. *)
Definition unitary_coordinate_fixing_group (J:set 'I_n):set U:=
  @PointwiseFixingLocus.value U X action n e J.

(** Source for [holomorphic_prefix_rotation_group]: the original
    unitary H_j fixes every complex e_i with i>j,
    using zero-based array indices, 3.4.12, p. 339. *)
Definition holomorphic_prefix_rotation_group j:=unitary_coordinate_fixing_group [set i:'I_n|(j<=i)%N].

(** Source for [holomorphic_suffix_rotation_group]: the original
    unitary Q_m fixes the first m complex basis vectors,
    3.4.12, p. 339. *)
Definition holomorphic_suffix_rotation_group m:=unitary_coordinate_fixing_group [set i:'I_n|(i<m)%N].

(** Source for [unitary_coordinate_fixing_membership]: the exact
    original fixed-vector membership equation, 3.4.12, p. 339. *)
Lemma unitary_coordinate_fixing_membership J g:
  unitary_coordinate_fixing_group J g <->forall i,J i ->action g (e i)=e i.
Proof. exact:(@PointwiseFixingLocus.laws U X action n e J g). Qed.

(** Source for [unitary_fixed_vector_continuous]: actual unitary
    evaluation is continuous in the original relative topology,
    supporting the Haar argument, 3.4.12, p. 339. *)
Lemma unitary_fixed_vector_continuous x:continuous (fun g:U=>(action g x:XT)).
Proof.
move=>g;apply:(@continuous_comp U O XT set_val (fun h=>@orthogonal_element_map R XR B hB N r hr h x)).
- exact:set_type_val_continuous.
- exact:(@orthogonal_germ_fixed_vector_continuous R XR B hB N r hr x).
Qed.

(** Source for [unitary_coordinate_fixing_closed]: the actual
    original fixing groups are closed in U(n), 3.4.12, p. 339. *)
Theorem unitary_coordinate_fixing_closed J:closed (unitary_coordinate_fixing_group J).
Proof.
exact:(@pointwise_fixing_closed U XT (fun g x=>action g x) n e J
  (unitary_coordinate_fixing_group J) (@PointwiseFixingLocus.laws U X action n e J)
  (@metric_hausdorff R XT) unitary_fixed_vector_continuous).
Qed.

Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB N r hr)
  (@linear_group_inv R XR B hB N r hr) (@linear_group_unit R XR B hB N r hr) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.

(** Source for [unitary_coordinate_fixing_subgroup]: the original
    fixing groups are actual subgroups of U(n), 3.4.12, p. 339. *)
Theorem unitary_coordinate_fixing_subgroup J:
  is_subgroup mulU invU unitU (unitary_coordinate_fixing_group J).
Proof.
apply:(@pointwise_fixing_subgroup U X mulU invU unitU action n e J
  (unitary_coordinate_fixing_group J) (@PointwiseFixingLocus.laws U X action n e J)).
- move=>x;rewrite /action (subgroup_restriction_unit hU).
  exact:(@orthogonal_element_unit R XR B hB N r hr mulO invO unitO hO x).
- move=>g h x;rewrite /action (subgroup_restriction_mul hU).
  exact:(@orthogonal_element_mulE R XR B hB N r hr mulO invO unitO hO (set_val g) (set_val h) x).
- move=>g x;rewrite /action (subgroup_restriction_inv hU).
  exact:(@orthogonal_element_inv R XR B hB N r hr mulO invO unitO hO (set_val g)).1 x.
Qed.
End Fixing.
