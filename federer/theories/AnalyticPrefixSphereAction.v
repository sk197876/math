(** Federer (1969), 3.4.8(6), pp. 328–329:
    H_p acts continuously and transitively on the
    original prefix unit sphere. Both the action
    and the sphere retain their actual ambient maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalMaps HomInner HomSpaceTopology
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology TopologicalProductMaps SubtypeCompactHausdorff
  HomogeneousSpaceUP CompactGroupHomogeneousMeasures PointwiseFixingLocusUP PointwiseFixingLocusSealed
  OrthogonalCoordinateFixing OrthogonalCoordinateFixingHaar OrthogonalPrefixFixingTransitivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_prefix_unit_sphere]: the original
    S of unit vectors orthogonal to e_i for
    i>p in the proof of 3.4.8(6), p. 328. *)
Definition analytic_prefix_unit_sphere (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) p:set (inner_metric_space hB):=
  [set v|inner_norm hB v = 1 /\forall i:'I_n,(p<=i)%N ->B v (e i) = 0].

Section Action.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable p:nat.
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation H:=(@analytic_prefix_rotation_group R X B hB n e he p).
Local Notation XT:=(inner_metric_space hB).
Local Notation S:=(@analytic_prefix_unit_sphere R X B hB n e p).
Local Notation HT:=(inner_metric_space (hom_inner_productP hB hB he)).
Local Notation action:=(fun g:O=>@orthogonal_element_map R X B hB n e he g).

(** Source for [analytic_prefix_sphere_action_member]: each
    original H_p element preserves the prefix sphere,
    3.4.8(6), p. 328. *)
Lemma analytic_prefix_sphere_action_member (g:H) (u:S):S (action (set_val g) (set_val u)).
Proof.
have [hUnit hTail]:=set_valP u;split.
- have hNorm:=@orthogonal_map_norm R X X B B hB hB
    (hom_as_linear (action (set_val g))) (orthogonal_element_orthogonal (set_val g)) (set_val u).
  rewrite hom_as_linearE in hNorm;by rewrite hNorm.
- move=>i hi.
  have hFixed:=((@orthogonal_coordinate_fixing_membership R X B hB n e he
    [set k:'I_n|(p<=k)%N] (set_val g)).1 (set_valP g)) i hi.
  rewrite -hFixed (orthogonal_element_inner (set_val g));exact:hTail.
Qed.

(** Source for [analytic_prefix_sphere_action]: original
    orthogonal evaluation restricted to H_p and S,
    3.4.8(6), p. 328. *)
Definition analytic_prefix_sphere_action (g:H) (u:S):S:=
  exist _ (action (set_val g) (set_val u)) (mem_set (analytic_prefix_sphere_action_member g u)).

(** Source for [analytic_prefix_sphere_action_value]: the
    restricted action is the actual ambient map,
    3.4.8(6), p. 328. *)
Lemma analytic_prefix_sphere_action_value (g:H) (u:S):
  set_val (analytic_prefix_sphere_action g u) = action (set_val g) (set_val u).
Proof. by []. Qed.

(** Source for [analytic_prefix_sphere_action_continuous]: the
    original joint action is continuous in the
    relative group and sphere topologies,
    3.4.8(6), p. 328. *)
Lemma analytic_prefix_sphere_action_continuous:
  continuous (fun q:H*S=>analytic_prefix_sphere_action q.1 q.2).
Proof.
apply:set_type_continuous_into.
have hMap:continuous (fun g:H=>(action (set_val g):HT)).
  move=>g;exact:(continuous_comp (@set_type_val_continuous O H g)
    (@orthogonal_element_continuous R X B hB n e he (set_val g))).
have hPair:continuous (fun q:H*S=>((action (set_val q.1),set_val q.2):HT*XT)).
  apply:topological_pair_continuous.
  - move=>q;exact:(continuous_comp (@first_projection_continuous H S q) (hMap q.1)).
  - move=>q;exact:(continuous_comp (@second_projection_continuous H S q)
      (@set_type_val_continuous XT S q.2)).
move=>q;exact:(continuous_comp (hPair q)
  (@hom_evaluation_continuous R X X B B hB hB n e he (action (set_val q.1),set_val q.2))).
Qed.

(** Source for [analytic_prefix_sphere_action_transitive]: the
    original transitivity of H_p on S,
    3.4.8(6), p. 328, from actual frame extension. *)
Lemma analytic_prefix_sphere_action_transitive:
  orthonormal_family B e ->(p<=n)%N ->forall u v:S,
    exists g:H,analytic_prefix_sphere_action g u = v.
Proof.
move=>hON hPN u v.
have [hU hUTail]:=set_valP u.
have [hV hVTail]:=set_valP v.
have hUU:B (set_val u) (set_val u) = 1 by rewrite -(inner_norm_sqr hB) hU expr1n.
have hVV:B (set_val v) (set_val v) = 1 by rewrite -(inner_norm_sqr hB) hV expr1n.
have [g [hG hUV]]:=@orthogonal_prefix_fixing_transitive R X B hB n e he hON p hPN
  (set_val u) (set_val v) hUU hVV hUTail hVTail.
exists (exist _ g (mem_set hG));apply:val_inj;exact:hUV.
Qed.

Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.
Variables (mulH:H->H->H) (invH:H->H) (unitH:H).
Hypothesis hH:is_subgroup_restriction mulO invO unitO H mulH invH unitH.

(** Source for [analytic_prefix_sphere_action_compatible]: the
    original sphere action respects restricted group
    multiplication, 3.4.8(6), p. 328. *)
Lemma analytic_prefix_sphere_action_compatible g h u:
  analytic_prefix_sphere_action (mulH g h) u =
  analytic_prefix_sphere_action g (analytic_prefix_sphere_action h u).
Proof.
apply:val_inj.
change (action (set_val (mulH g h)) (set_val u) =
  action (set_val g) (action (set_val h) (set_val u))).
rewrite (subgroup_restriction_mul hH).
exact:(@orthogonal_element_mulE R X B hB n e he mulO invO unitO hO (set_val g) (set_val h) (set_val u)).
Qed.

(** Source for [analytic_prefix_sphere_homogeneous]: the
    original S is a homogeneous space of H_p,
    3.4.8(6), p. 328. Compact transitivity proves
    openness of every original orbit map. *)
Theorem analytic_prefix_sphere_homogeneous:
  orthonormal_family B e ->(p<=n)%N ->
  is_homogeneous_space mulH analytic_prefix_sphere_action.
Proof.
move=>hON hPN.
have hLCH:=@orthogonal_coordinate_fixing_lch R X B hB n e he [set i:'I_n|(p<=i)%N]
  mulO invO unitO hO mulH invH unitH hH.
have hCompact:=@orthogonal_coordinate_fixing_compact R X B hB n e he [set i:'I_n|(p<=i)%N].
have hHausdorff:hausdorff_space S by apply:set_type_hausdorff;exact:(@metric_hausdorff R XT).
exact:(@compact_transitive_homogeneous H S mulH invH unitH analytic_prefix_sphere_action
  (lch_group_topological hLCH) hCompact hHausdorff analytic_prefix_sphere_action_continuous
  analytic_prefix_sphere_action_compatible (analytic_prefix_sphere_action_transitive hON hPN)).
Qed.
End Action.
