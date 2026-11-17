(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),(8),
    pp. 328–330: the original coordinate-fixing unitary group acts
    transitively on the unit sphere perpendicular to its fixed vectors.
    Reuse actual Hermitian isometry and the proved rank-one alignment. *)
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
Section Sphere.
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

Variable n:nat.
Variable e:'I_n->X.
Variable J:set 'I_n.
Local Notation S:=(@unitary_coordinate_fixing_group R X H hH N r hr n e J).
Local Notation XT:=(inner_metric_space hB).
Local Notation HT:=(inner_metric_space (hom_inner_productP hB hB hr)).

(** Source for [unitary_fixing_sphere]: the original sphere
    perpendicular to the prescribed fixed complex coordinates,
    3.4.12, p. 339. *)
Definition unitary_fixing_sphere:set XT:=
  [set v|inner_norm hB v= 1 /\forall i,J i ->H v (e i)=0].
Local Notation V:=unitary_fixing_sphere.
Local Notation action:=(fun g:S=>L (set_val g)).

(** Source for [unitary_fixing_sphere_action_member]: original
    fixing transformations preserve the actual sphere,
    3.4.12, p. 339. *)
Lemma unitary_fixing_sphere_action_member (g:S) (u:V):V (action g (set_val u)).
Proof.
have [hUnit hPerpendicular]:=set_valP u;split.
- rewrite (@UnitaryComplexMap.laws R X H hH N r hr (set_val g))
    (@unitary_element_norm R X H hH N r hr (set_val g));exact:hUnit.
- move=>i hi.
  have hFixed:=(@unitary_coordinate_fixing_membership R X H hH N r hr n e J (set_val g)).1 (set_valP g) i hi.
  have hFixedC:L (set_val g) (e i)=e i.
    by rewrite (@UnitaryComplexMap.laws R X H hH N r hr (set_val g)).
  rewrite -hFixedC (@unitary_element_hermitian R X H hH N r hr (set_val g)).
  exact:hPerpendicular.
Qed.

(** Source for [unitary_fixing_sphere_action]: the original
    unitary map restricted to its fixed-coordinate sphere,
    3.4.12, p. 339. *)
Definition unitary_fixing_sphere_action (g:S) (u:V):V:=
  exist _ (action g (set_val u)) (mem_set (unitary_fixing_sphere_action_member g u)).

(** Source for [unitary_fixing_sphere_action_value]: the
    restricted action retains its actual ambient unitary values,
    3.4.12, p. 339. *)
Lemma unitary_fixing_sphere_action_value (g:S) (u:V):
  set_val (unitary_fixing_sphere_action g u)=action g (set_val u).
Proof. by []. Qed.

(** Source for [unitary_fixing_sphere_action_transitive]: actual
    unitary alignment fixes every prescribed perpendicular coordinate,
    3.4.12, p. 339, without a transitivity premise. *)
Lemma unitary_fixing_sphere_action_transitive (u v:V):
  exists g:S,unitary_fixing_sphere_action g u=v.
Proof.
have [hU hUP]:=set_valP u;have [hV hVP]:=set_valP v.
have [g [hG hFix]]:=@unitary_sphere_fixing_transitive R X H hH N r hr (set_val u) (set_val v) hU hV.
have hMember:S g.
  apply/(@unitary_coordinate_fixing_membership R X H hH N r hr n e J g)=>i hi.
  exact:hFix (e i) (hUP i hi) (hVP i hi).
exists (exist _ g (mem_set hMember));apply:val_inj.
change (L g (set_val u)=set_val v).
rewrite (@UnitaryComplexMap.laws R X H hH N r hr g);exact:hG.
Qed.

(** Source for [unitary_fixing_sphere_action_continuous]: the
    actual joint action in the relative group and sphere topologies,
    3.4.12, p. 339. *)
Lemma unitary_fixing_sphere_action_continuous:
  continuous (fun q:S*V=>unitary_fixing_sphere_action q.1 q.2).
Proof.
apply:set_type_continuous_into.
pose realAction:=fun g:S=>@orthogonal_element_map R XR B hB N r hr (set_val (set_val g)).
have hMap:continuous (fun g:S=>(realAction g:HT)).
  have hUMap:continuous (fun g:U=>(@orthogonal_element_map R XR B hB N r hr (set_val g):HT)).
    move=>g;exact:(continuous_comp (@set_type_val_continuous O U g)
      (@orthogonal_element_continuous R XR B hB N r hr (set_val g))).
  move=>g;exact:(continuous_comp (@set_type_val_continuous U S g) (hUMap (set_val g))).
have hPair:continuous (fun q:S*V=>((realAction q.1,set_val q.2):HT*XT)).
  apply:topological_pair_continuous.
  - move=>q;exact:(continuous_comp (@first_projection_continuous S V q) (hMap q.1)).
  - move=>q;exact:(continuous_comp (@second_projection_continuous S V q) (@set_type_val_continuous XT V q.2)).
have hValues:(fun q:S*V=>set_val (unitary_fixing_sphere_action q.1 q.2))=
    (fun q:S*V=>realAction q.1 (set_val q.2)).
  apply:funext=>q;exact:(@UnitaryComplexMap.laws R X H hH N r hr (set_val q.1) (set_val q.2)).
change (continuous (fun q:S*V=>set_val (unitary_fixing_sphere_action q.1 q.2))).
rewrite hValues=>q;exact:(continuous_comp (hPair q)
  (@hom_evaluation_continuous R XR XR B B hB hB N r hr (realAction q.1,set_val q.2))).
Qed.

Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB N r hr)
  (@linear_group_inv R XR B hB N r hr) (@linear_group_unit R XR B hB N r hr) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.
Variables (mulS:S->S->S) (invS:S->S) (unitS:S).
Variable hS:is_subgroup_restriction mulU invU unitU S mulS invS unitS.

(** Source for [unitary_fixing_sphere_action_compatible]: actual
    restricted multiplication agrees with composition on the sphere,
    3.4.12, p. 339. *)
Lemma unitary_fixing_sphere_action_compatible g h u:
  unitary_fixing_sphere_action (mulS g h) u=
    unitary_fixing_sphere_action g (unitary_fixing_sphere_action h u).
Proof.
apply:val_inj.
change (L (set_val (mulS g h)) (set_val u)=L (set_val g) (L (set_val h) (set_val u))).
rewrite !(@UnitaryComplexMap.laws R X H hH N r hr)
  (subgroup_restriction_mul hS) (subgroup_restriction_mul hU).
exact:(@orthogonal_element_mulE R XR B hB N r hr mulO invO unitO hO
  (set_val (set_val g)) (set_val (set_val h)) (set_val u)).
Qed.

(** Source for [unitary_fixing_group_lch]: actual closed fixing
    subgroups have the required local compact Hausdorff structure,
    3.4.12, p. 339. *)
Lemma unitary_fixing_group_lch:is_locally_compact_hausdorff_group mulS invS unitS.
Proof.
have hLocalU:=@subgroup_restriction_locally_compact_hausdorff O mulO invO unitO U mulU invU unitU hU
  (@orthogonal_group_lch R XR B hB N r hr mulO invO unitO hO) (@unitary_group_closed R X H hH N r hr).
exact:(@subgroup_restriction_locally_compact_hausdorff U mulU invU unitU S mulS invS unitS hS
  hLocalU (@unitary_coordinate_fixing_closed R X H hH N r hr n e J)).
Qed.

(** Source for [unitary_fixing_sphere_homogeneous]: the actual
    compact transitive action is a homogeneous space; openness of
    each orbit map is proved by the existing compact-action theorem,
    3.4.12, p. 339. *)
Theorem unitary_fixing_sphere_homogeneous:is_homogeneous_space mulS unitary_fixing_sphere_action.
Proof.
have hCompact:=@unitary_coordinate_fixing_compact R X H hH N r hr n e J.
have hHausdorff:hausdorff_space V by apply:set_type_hausdorff;exact:(@metric_hausdorff R XT).
exact:(@compact_transitive_homogeneous S V mulS invS unitS unitary_fixing_sphere_action
  (lch_group_topological unitary_fixing_group_lch) hCompact hHausdorff
  unitary_fixing_sphere_action_continuous unitary_fixing_sphere_action_compatible unitary_fixing_sphere_action_transitive).
Qed.
End Sphere.
