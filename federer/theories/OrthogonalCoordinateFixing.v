(** Federer (1969), 3.4.8(4), p. 326:
    the actual orthogonal coordinate-fixing groups H_j
    and Q_m retain the original basis and topology.
    All fixed-vector sets use their opaque exact laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology subtype_topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground InnerProductUP InnerNorm InnerMetric
  HilbertFormCompactness LinearBasis HomInner LinearGroupTopology LinearGroupSealed TopologicalGroupUP IsotropyGroupTopology
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure AnalyticOrthogonalJointContinuity
  PointwiseFixingLocusUP PointwiseFixingLocusSealed PointwiseFixingSubgroup PointwiseFixingClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Fixing.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation action:=(fun g:O=>@orthogonal_element_map R X B hB n e he g).

(** Source for [orthogonal_coordinate_fixing_group]: the
    exact original pointwise fixing set for specified
    basis indices, 3.4.8(4), p. 326. *)
Definition orthogonal_coordinate_fixing_group (J:set 'I_n):set O:=
  @PointwiseFixingLocus.value O X action n e J.

(** Source for [analytic_prefix_rotation_group]: original
    H_j fixes e_i for i>j, 3.4.8(4), p. 326.
    Zero-based indices make this i>=j. *)
Definition analytic_prefix_rotation_group j:=
  orthogonal_coordinate_fixing_group [set i:'I_n|(j<=i)%N].

(** Source for [analytic_suffix_rotation_group]: original
    Q_m fixes e_i for i<=m, 3.4.8(4), p. 326.
    Zero-based indices make this i<m. *)
Definition analytic_suffix_rotation_group m:=
  orthogonal_coordinate_fixing_group [set i:'I_n|(i<m)%N].

(** Source for [orthogonal_coordinate_fixing_membership]: the
    original exact fixed-vector equation,
    3.4.8(4), p. 326. *)
Lemma orthogonal_coordinate_fixing_membership J g:
  orthogonal_coordinate_fixing_group J g <->forall i,J i ->action g (e i) = e i.
Proof. exact:(@PointwiseFixingLocus.laws O X action n e J g). Qed.

(** Source for [orthogonal_coordinate_fixing_closed]: the
    original coordinate-fixing sets are closed in O(n),
    supporting Haar measures in 3.4.8(4), p. 326. *)
Theorem orthogonal_coordinate_fixing_closed J:closed (orthogonal_coordinate_fixing_group J).
Proof.
exact:(@pointwise_fixing_closed O XT (fun g x=>action g x) n e J
  (orthogonal_coordinate_fixing_group J)
  (@PointwiseFixingLocus.laws O X action n e J)
  (@metric_hausdorff R XT) (@orthogonal_germ_fixed_vector_continuous R X B hB n e he)).
Qed.

Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.

(** Source for [orthogonal_coordinate_fixing_subgroup]: the
    original coordinate-fixing sets are subgroups,
    3.4.8(4), p. 326. *)
Theorem orthogonal_coordinate_fixing_subgroup J:
  is_subgroup mulO invO unitO (orthogonal_coordinate_fixing_group J).
Proof.
apply:(@pointwise_fixing_subgroup O X mulO invO unitO action n e J
  (orthogonal_coordinate_fixing_group J)
  (@PointwiseFixingLocus.laws O X action n e J)).
- exact:(@orthogonal_element_unit R X B hB n e he mulO invO unitO hO).
- exact:(@orthogonal_element_mulE R X B hB n e he mulO invO unitO hO).
- move=>g;exact:(@orthogonal_element_inv R X B hB n e he mulO invO unitO hO g).1.
Qed.
End Fixing.
