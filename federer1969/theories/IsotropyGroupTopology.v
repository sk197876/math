(** Federer (1969), 2.7.10, printed p. 127: "To each x in X and each left
    Haar integral mu of the isotropy group G^x corresponds ...". The
    isotropy subgroup G^x = G cap {g: A(g,x) = x} of 2.7.1, pp. 121–122, is
    closed in G, and the phrase "left Haar integral of the isotropy group"
    regards G^x as a topological group in its own right, with the relative
    topology and the restricted operations. Here a subset S of G is the type
    set_type S of its elements, with MathComp's topology of set_type S, the
    initial topology of the inclusion set_val. A group structure on set_type
    S is specified by the predicate is_subgroup_restriction: the inclusion
    carries the multiplication, the inversion and the identity of set_type S
    to those of G. Such a structure exists for every subgroup and is unique.
    The restricted structure is a topological group, and it is a locally
    compact Hausdorff group when G is one and S is closed, because the
    inclusion of a closed subset is a proper map. For the isotropy subgroup
    of a homogeneous space X with X Hausdorff this gives a locally compact
    Hausdorff group G^x, which has a left Haar integral by 2.7.5, p. 125. *)
From mathcomp Require Import all_boot boolp classical_sets functions reals topology.
From Federer Require Import TopologicalProductMaps ProperMapUP SubtypeCompactHausdorff
  TopologicalGroupUP HomogeneousSpaceUP HomogeneousSpaceLaws HaarIntegralUP HaarIntegralExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section SubsetTopology.
Variable T : topologicalType.
Variable S : set T.

(** Source for [set_type_val_continuous]: the inclusion of G^x into G
    is continuous for the relative topology, supporting "the isotropy
    group G^x", Federer 2.7.10, p. 127. *)
Lemma set_type_val_continuous : continuous (set_val : set_type S -> T).
Proof. exact: initial_continuous. Qed.

(** Source for [set_type_continuous_into]: a map into G^x is
    continuous when its composition with the inclusion is continuous,
    by the definition of the relative topology; supporting "the
    isotropy group G^x", Federer 2.7.10, p. 127. *)
Lemma set_type_continuous_into (Y : topologicalType) (f : Y -> set_type S) :
  continuous (set_val \o f) -> continuous f.
Proof. exact: (@continuous_comp_initial (set_type S) Y T set_val f). Qed.

(** Source for [set_type_compact_preimage]: a compact subset C of G
    contained in S is compact in the relative topology of S, supporting
    "u(gs) ... s in G^x", Federer 2.7.10, pp. 127–128. A proper filter
    on set_type S containing the inverse image of C pushes forward to a
    proper filter on T containing C; a cluster point of the image lies
    in C, hence in S. *)
Lemma set_type_compact_preimage (C : set T) :
  compact C -> C `<=` S -> compact (set_val @^-1` C : set (set_type S)).
Proof.
move=> hC hCS F PF hF.
pose G : set_system T := set_val @ F.
have PG : ProperFilter G by exact: fmap_proper_filter.
have GC : G C by [].
have [x [hxC hx]] := hC G PG GC.
exists (exist _ x (mem_set (hCS x hxC))); split=> //.
move=> B N hB; rewrite (@nbhsE (set_type S))=> -[W [[O hO <-] hWy] hWN].
have hGB : G (set_val @` B).
  by rewrite /G /fmap /=; move: hB; apply: filterS=> b hb; exists b.
have [t [himg hOt]] := hx _ _ hGB (open_nbhs_nbhs (conj hO hWy)).
have [b hb hbt] : exists2 b : set_type S, B b & set_val b = t by exact: himg.
by exists b; split=> //; apply: hWN; rewrite /= hbt.
Qed.

(** Source for [set_type_val_proper]: the inclusion of a closed subset
    is a proper map, supporting the compactness of the supports of the
    functions s |-> u(gs) on G^x, Federer 2.7.10, pp. 127–128. The
    inverse image of a compact set C equals that of the compact set
    C cap S. *)
Lemma set_type_val_proper : closed S -> is_proper_map (set_val : set_type S -> T).
Proof.
move=> hS C hC.
have -> : set_val @^-1` C = set_val @^-1` (C `&` S) :> set (set_type S).
  by apply/seteqP; split=> a /= h; [split=> //; exact: set_valP|exact: h.1].
by apply: set_type_compact_preimage; [exact: compact_closedI|exact: subIsetr].
Qed.

(** Source for [set_type_locally_compact]: a closed subset of a
    locally compact Hausdorff space is locally compact in the relative
    topology, supporting "left Haar integral mu of the isotropy group
    G^x", Federer 2.7.10, p. 127, where Haar integrals are those of the
    locally compact Hausdorff groups of 2.7.1–2.7.2, pp. 121–122. The
    inverse image of a closed compact neighbourhood of a point is a
    closed compact neighbourhood. *)
Lemma set_type_locally_compact :
  locally_compact [set: T] -> closed S -> locally_compact [set: set_type S].
Proof.
move=> hl hS a _.
have [N hN [hNc hNcl]] := hl (set_val a) I; rewrite withinET in hN.
exists (set_val @^-1` N); last split.
- by rewrite withinET; exact: set_type_val_continuous hN.
- exact: set_type_val_proper.
- by apply: preimage_closed hNcl=> b _; exact: set_type_val_continuous.
Qed.

End SubsetTopology.

(** Source for [is_subgroup_restriction]: "the isotropy group G^x",
    Federer 2.7.10, p. 127, regarded as a group: the operations of
    set_type S are carried by the inclusion to the multiplication, the
    inversion and the identity of G. Definition by these laws; with the
    relative topology this is the topological group G^x. *)
Record is_subgroup_restriction (G : Type) (mul : G -> G -> G) (inv : G -> G) (e : G) (S : set G)
    (mulS : S -> S -> S) (invS : S -> S) (eS : S) : Prop := {
  (** Source for [subgroup_restriction_mul]: the multiplication of G^x
      is that of G, Federer 2.7.10, p. 127. *)
  subgroup_restriction_mul : forall a b, set_val (mulS a b) = mul (set_val a) (set_val b);
  (** Source for [subgroup_restriction_inv]: the inversion of G^x is
      that of G, Federer 2.7.10, p. 127. *)
  subgroup_restriction_inv : forall a, set_val (invS a) = inv (set_val a);
  (** Source for [subgroup_restriction_unit]: the identity of G^x is
      e, Federer 2.7.10, p. 127. *)
  subgroup_restriction_unit : set_val eS = e
}.

Arguments is_subgroup_restriction [G] mul inv e S mulS invS eS.

Section SubgroupRestriction.
Variable G : Type.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (S : set G).
Hypothesis hS : is_subgroup mul inv e S.

(** Source for [subgroup_restriction_exists]: the restricted
    operations of "the isotropy group G^x", Federer 2.7.10, p. 127,
    exist for every subgroup. Existence proof for
    is_subgroup_restriction. *)
Theorem subgroup_restriction_exists :
  exists mulS invS eS, is_subgroup_restriction mul inv e S mulS invS eS.
Proof.
exists (fun a b => exist _ (mul (set_val a) (set_val b))
  (mem_set (subgroup_mul hS (set_valP a) (set_valP b)))).
exists (fun a => exist _ (inv (set_val a)) (mem_set (subgroup_inv hS (set_valP a)))).
by exists (exist _ e (mem_set (subgroup_unit hS))).
Qed.

(** Source for [subgroup_restriction_complete]: a multiplication of
    set_type S carried by the inclusion to that of G extends to the
    group structure of G^x, Federer 2.7.10, p. 127. Supporting lemma:
    the inversion and the identity are those of
    subgroup_restriction_exists. *)
Lemma subgroup_restriction_complete (mulS : S -> S -> S) :
  (forall a b, set_val (mulS a b) = mul (set_val a) (set_val b)) ->
  exists invS eS, is_subgroup_restriction mul inv e S mulS invS eS.
Proof.
move=> hm; have [mulS' [invS [eS [_ hi hu]]]] := subgroup_restriction_exists.
by exists invS, eS.
Qed.

End SubgroupRestriction.

(** Source for [subgroup_restriction_unique]: the restricted
    operations of "the isotropy group G^x", Federer 2.7.10, p. 127, are
    unique, since the inclusion is injective. Supporting lemma. *)
Lemma subgroup_restriction_unique (G : Type) (mul : G -> G -> G) (inv : G -> G) (e : G)
    (S : set G) mulS invS eS mulS' invS' eS' :
  is_subgroup_restriction mul inv e S mulS invS eS ->
  is_subgroup_restriction mul inv e S mulS' invS' eS' ->
  [/\ mulS = mulS', invS = invS' & eS = eS'].
Proof.
move=> [hm hi hu] [hm' hi' hu']; split.
- by apply: funext=> a; apply: funext=> b; apply: val_inj; rewrite /= -!set_valE hm hm'.
- by apply: funext=> a; apply: val_inj; rewrite /= -!set_valE hi hi'.
- by apply: val_inj; rewrite /= -!set_valE hu hu'.
Qed.

Section SubgroupTopology.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (S : set G).
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hR : is_subgroup_restriction mul inv e S mulS invS eS.

(** Source for [subgroup_restriction_topological]: "the isotropy
    group G^x", Federer 2.7.10, p. 127, is a topological group with the
    relative topology. The group laws are transported along the
    injective inclusion, and the continuity of the restricted
    operations follows from that of the operations of G and of the
    inclusion. Supporting theorem. *)
Theorem subgroup_restriction_topological :
  is_topological_group mul inv e -> is_topological_group mulS invS eS.
Proof.
move=> hT; have hG := topological_group_laws hT.
have [hm hi hu] := hR.
have hv := @set_type_val_continuous G S.
constructor.
- constructor.
  + by move=> a b c; apply: val_inj; rewrite /= -!set_valE !hm (group_mulA hG).
  + by move=> a; apply: val_inj; rewrite /= -!set_valE hm hu (group_mul1g hG).
  + by move=> a; apply: val_inj; rewrite /= -!set_valE hm hi hu (group_mulVg hG).
- apply: set_type_continuous_into.
  have -> : set_val \o (fun p : S * S => mulS p.1 p.2) =
      (fun q : G * G => mul q.1 q.2) \o (fun p : S * S => (set_val p.1, set_val p.2)).
    by apply: funext=> p; rewrite /= hm.
  have hp : continuous (fun p : S * S => (set_val p.1, set_val p.2)).
    apply: (@topological_pair_continuous (S * S)%type G G).
    + move=> q; exact: continuous_comp (@first_projection_continuous S S q) (hv q.1).
    + move=> q; exact: continuous_comp (@second_projection_continuous S S q) (hv q.2).
  have hmc := topological_group_mul_continuous hT.
  by move=> p; apply: continuous_comp; [exact: hp|exact: hmc].
- apply: set_type_continuous_into.
  have -> : set_val \o invS = inv \o set_val by apply: funext=> a; rewrite /= hi.
  have hic := topological_group_inv_continuous hT.
  by move=> a; apply: continuous_comp; [exact: hv|exact: hic].
Qed.

(** Source for [subgroup_restriction_locally_compact_hausdorff]: a
    closed subgroup of a locally compact Hausdorff topological group,
    in particular "the isotropy group G^x" of Federer 2.7.10, p. 127,
    is a locally compact Hausdorff topological group, as required for
    its Haar integrals (2.7.2, p. 122). Supporting theorem. *)
Theorem subgroup_restriction_locally_compact_hausdorff :
  is_locally_compact_hausdorff_group mul inv e -> closed S ->
  is_locally_compact_hausdorff_group mulS invS eS.
Proof.
move=> [hT hH hl] hS; constructor.
- exact: subgroup_restriction_topological.
- exact: set_type_hausdorff.
- exact: set_type_locally_compact.
Qed.

End SubgroupTopology.

Section IsotropyGroup.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (x : X).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hX : hausdorff_space X.

(** Source for [isotropy_group_exists]: "the isotropy group G^x",
    Federer 2.7.10, p. 127: the isotropy subgroup of 2.7.1, p. 121,
    with the relative topology and the restricted operations, is a
    locally compact Hausdorff topological group. Supporting theorem,
    combining the closedness of G^x (2.7.1, pp. 121–122) with
    subgroup_restriction_locally_compact_hausdorff. *)
Theorem isotropy_group_exists :
  exists mulS invS eS, is_subgroup_restriction mul inv e (isotropy_subgroup A x) mulS invS eS /\
    is_locally_compact_hausdorff_group mulS invS eS.
Proof.
have hgl := topological_group_laws (lch_group_topological hG).
have hS := isotropy_subgroup_subgroup hgl hA x.
have [mulS [invS [eS hR]]] := subgroup_restriction_exists hS.
exists mulS, invS, eS; split=> //.
exact: (subgroup_restriction_locally_compact_hausdorff hR hG (isotropy_subgroup_closed hA hX)).
Qed.

(** Source for [isotropy_left_haar_integral_exists]: "each left Haar
    integral mu of the isotropy group G^x", Federer 2.7.10, p. 127:
    such integrals exist, by 2.7.5, p. 125, applied to the locally
    compact Hausdorff group G^x. Supporting theorem. *)
Theorem isotropy_left_haar_integral_exists (R : realType)
    (mulS : isotropy_subgroup A x -> isotropy_subgroup A x -> isotropy_subgroup A x)
    (invS : isotropy_subgroup A x -> isotropy_subgroup A x) (eS : isotropy_subgroup A x) :
  is_subgroup_restriction mul inv e (isotropy_subgroup A x) mulS invS eS ->
  exists mu : (isotropy_subgroup A x -> R) -> R, is_left_haar_integral mulS mu.
Proof.
move=> hR; apply: left_haar_integral_exists.
exact: (subgroup_restriction_locally_compact_hausdorff hR hG (isotropy_subgroup_closed hA hX)).
Qed.

End IsotropyGroup.
