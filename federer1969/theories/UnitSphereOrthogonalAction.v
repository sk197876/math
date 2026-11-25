(** Federer (1969), 3.2.13, p. 251: the unit sphere
    is a homogeneous space of O(m). The action is its
    actual orthogonal evaluation, with compactness and transitivity proved. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets functions
  constructive_ereal topology subtype_topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  InnerNormedTopology Hom HomInner HomSpaceTopology OrthogonalMaps OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  LinearGroupTopology LinearGroupSealed EuclideanOrthogonalInvariantMeasures UnitSphereSpace UnitVectorOrthogonalMap
  IsotropyGroupTopology TopologicalProductMaps TopologicalGroupUP HomogeneousSpaceUP CompactGroupHomogeneousMeasures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SphereAction.
Variable R:realType.
Variable m:nat.
Local Notation V:=(R_n R m).
Local Notation B:=(@euclidean_inner_product R m).
Local Notation hB:=(@euclidean_inner_productP R m).
Local Notation b:=(@coordinate_basis R m).
Local Notation hb:=(@coordinate_basisP R m).
Local Notation E:=(inner_metric_space hB).
Local Notation O:=(set_type (euclidean_orthogonal_group R m)).
Local Notation S:=(euclidean_unit_sphere_space R m).
Local Notation H:=(inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation om:=(@orthogonal_element_map R V B hB m b hb).

(** Source for [orthogonal_element_preserves_norm]: orthogonal
    elements preserve the unit sphere, 1.7.2, p. 28, used
    for the sphere action in Federer 3.2.13, p. 251. *)
Lemma orthogonal_element_preserves_norm (g:O) (x:V):
  inner_norm hB (om g x)=inner_norm hB x.
Proof.
have h:=orthogonal_map_norm hB hB (orthogonal_element_orthogonal g) x.
by rewrite hom_as_linearE in h.
Qed.

(** Source for [unit_sphere_action_member]: orthogonal evaluation
    has unit norm on a unit vector, Federer 3.2.13, p. 251. *)
Lemma unit_sphere_action_member (g:O) (u:S):
  @euclidean_unit_sphere_set R m (om g (set_val u)).
Proof. rewrite /euclidean_unit_sphere_set /= orthogonal_element_preserves_norm; exact:(set_valP u). Qed.

(** Source for [unit_sphere_action]: the action g(u) of
    O(m) on S^(m-1), Federer 3.2.13, p. 251. *)
Definition unit_sphere_action (g:O) (u:S):S:=
  exist _ (om g (set_val u)) (mem_set (unit_sphere_action_member g u)).

(** Source for [unit_sphere_action_value]: the sphere action
    is the actual orthogonal linear map, Federer 3.2.13, p. 251. *)
Lemma unit_sphere_action_value (g:O) (u:S):
  set_val (unit_sphere_action g u)=om g (set_val u).
Proof. by []. Qed.

(** Source for [unit_sphere_action_continuous]: continuity of
    the sphere action, required by the homogeneous-space statement
    in Federer 3.2.13, p. 251, follows from continuous evaluation. *)
Lemma unit_sphere_action_continuous:
  continuous (fun p:O*S=>unit_sphere_action p.1 p.2).
Proof.
apply:set_type_continuous_into.
have hp:continuous (fun p:O*S=>((om p.1:H),(set_val p.2:E))).
  apply:topological_pair_continuous.
  - move=>p; exact:continuous_comp (@first_projection_continuous O S p)
      (@orthogonal_element_continuous R V B hB m b hb p.1).
  - move=>p; exact:continuous_comp (@second_projection_continuous O S p)
      (@set_type_val_continuous E (@euclidean_unit_sphere_set R m) p.2).
have he:(set_val\o (fun p:O*S=>unit_sphere_action p.1 p.2))=
    (fun q:H*E=>((q.1:Hom V V) q.2:E))\o(fun p:O*S=>((om p.1:H),(set_val p.2:E))).
  by [].
rewrite he=>p; apply:continuous_comp; first exact:hp.
exact:(@hom_evaluation_continuous R V V B B hB hB m b hb _).
Qed.

(** Source for [unit_sphere_action_transitive]: O(m) is
    transitive on S^(m-1), Federer 3.2.13, p. 251. *)
Lemma unit_sphere_action_transitive:
  (0<m)%N ->forall u v:S,exists g,unit_sphere_action g u=v.
Proof.
move=>hm u v.
have [f [hf hF]]:=unit_vector_orthogonal_map_exists hm (set_valP u) (set_valP v).
exists (orthogonal_element_of hB hb hf); apply:val_inj.
change (om (orthogonal_element_of hB hb hf) (set_val u)=set_val v).
rewrite orthogonal_element_ofE; exact:hF.
Qed.

Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb)
  (linear_group_unit hB hb) (euclidean_orthogonal_group R m) mulS invS eS.

(** Source for [unit_sphere_action_compatible]: composition of
    sphere actions is orthogonal multiplication, Federer 2.7.1,
    p. 121, used in 3.2.13, p. 251. *)
Lemma unit_sphere_action_compatible g h u:
  unit_sphere_action (mulS g h) u=unit_sphere_action g (unit_sphere_action h u).
Proof.
apply:val_inj; change (om (mulS g h) (set_val u)=om g (om h (set_val u))).
exact:(@orthogonal_element_mulE R V B hB m b hb mulS invS eS hS g h (set_val u)).
Qed.

(** Source for [unit_sphere_homogeneous]: the sphere is a
    homogeneous space of O(m), Federer 3.2.13, p. 251.
    Openness of orbit maps follows from the already proved compact
    transitive action theorem. *)
Theorem unit_sphere_homogeneous:
  (0<m)%N ->is_homogeneous_space mulS unit_sphere_action.
Proof.
move=>hm.
exact (@compact_transitive_homogeneous [the topologicalType of O] S mulS invS eS unit_sphere_action
  (lch_group_topological (orthogonal_group_lch hS))
  (@orthogonal_group_compact_space R V B hB m b hb) (@euclidean_unit_sphere_space_hausdorff R m)
  unit_sphere_action_continuous (fun g h u=>unit_sphere_action_compatible g h u)
  (fun u v=>unit_sphere_action_transitive hm u v)).
Qed.
End SphereAction.
