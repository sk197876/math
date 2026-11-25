(** Federer (1969), 2.7.1, printed p. 121: "we assume that X is a
    homogeneous space of G through the transitive left action A: G x X -> X;
    this means that A is continuous, that A(gh,x) = A[g,A(h,x)] ..., and
    that for each x in X the map A^x: G -> X ... is open with im A^x = X",
    and "X is a locally compact Hausdorff space". Two facts used in 2.7.16,
    examples (4) and (5), printed p. 138, are proved here; Federer leaves
    both implicit. First, if a subgroup S of G, with the relative topology,
    acts on X by the restriction of A and its orbit maps are open, then the
    orbit maps of G are open: for g in an open set U of G the set {s in S :
    s g in U} is open in S, and its image under the orbit map of S at A(g,
    x) is an open set containing A(g, x) and contained in A^x(U). This gives
    the openness of the orbit maps of GL(V) on G(V, m) from that of O(V),
    and of the affine group on the space of affine subspaces from that of
    the isometry group. Second, a Hausdorff homogeneous space of a locally
    compact Hausdorff group is locally compact: the image of a compact
    neighbourhood of g under the open continuous orbit map is a compact
    neighbourhood of A(g, x) (the argument of
    affine_subspace_space_locally_compact). The local erratum has no entry
    for p. 121. *)
From mathcomp Require Import all_boot all_order boolp classical_sets functions topology.
From Federer Require Import HomeomorphismUP TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP
  HomogeneousSpaceLaws IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section SubgroupOrbits.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hT : is_topological_group mul inv e.
Hypothesis hAc : forall g h x, A (mul g h) x = A g (A h x).
Variable S : set G.
Hypothesis hSe : S e.
Variable AS : S -> X -> X.
Hypothesis hAS : forall s x, AS s x = A (set_val s) x.
Hypothesis hSo : forall x, is_open_map (orbit_map AS x).

(** Source for [subgroup_orbit_open]: "for each x in X the map A^x ...
    is open", Federer 2.7.1, p. 121, derived from the same property of
    a subgroup S of G acting by the restriction of A. Supporting lemma,
    used for the actions of 2.7.16, examples (4) and (5), p. 138: for g
    in an open set U the set U' = {s in S : s g in U} is open in S, and
    A^{A(g, x)}_S(U') is an open set containing A(g, x) and contained in
    A^x(U). *)
Lemma subgroup_orbit_open x : is_open_map (orbit_map A x).
Proof.
have hgl := topological_group_laws hT.
move=> U hU; rewrite openE=> y [g hg <-]; rewrite /interior.
pose F := fun s : S => mul (set_val s) g.
have hF : continuous F.
  move=> s; apply: (@continuous_comp S G G set_val (fun h => mul h g)).
    exact: set_type_val_continuous.
  exact: (right_translation_continuous hT g).
have hU' : open (F @^-1` U) by apply: open_comp hU=> s _; exact: hF.
have ho := hSo (A g x) hU'.
pose s0 : S := exist _ e (mem_set hSe).
have hs0 : (F @^-1` U) s0 by rewrite /F /= (group_mul1g hgl).
have hy : (orbit_map AS (A g x) @` (F @^-1` U)) (A g x).
  exists s0=> //; rewrite /orbit_map hAS /= -hAc (group_mul1g hgl).
  by [].
apply: (@filterS _ _ (nbhs_filter _) _ _ _ (open_nbhs_nbhs (conj ho hy))).
move=> z [s hs <-]; exists (F s)=> //.
by rewrite /orbit_map hAS hAc.
Qed.

End SubgroupOrbits.

Section HomogeneousLocallyCompact.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hX : hausdorff_space X.

(** Source for [homogeneous_space_locally_compact]: "X is a locally
    compact Hausdorff space", the standing hypothesis of Federer 2.7.1,
    p. 121, holds for every Hausdorff homogeneous space of a locally
    compact Hausdorff group. Supporting lemma: if K is a compact
    neighbourhood of g, then A^x(K) is compact, and it contains the open
    set A^x(int K), which contains A(g, x). *)
Lemma homogeneous_space_locally_compact : locally_compact [set: X].
Proof.
have hl := lch_group_locally_compact hG.
move=> y _.
have [g0 hg0] := homogeneous_transitive hA (y : X) y.
pose x := y.
have [K hK [hKc _]] := hl g0 I; rewrite withinET in hK.
have hpK : compact (orbit_map A x @` K).
  apply: continuous_compact=> //; apply: continuous_subspaceT; exact: orbit_map_continuous hA x.
exists (orbit_map A x @` K); last first.
  split=> //; exact: compact_closed hX hpK.
rewrite withinET nbhsE; exists (orbit_map A x @` K°).
  split; first exact: (homogeneous_orbit_open hA x (@open_interior _ K)).
  by exists g0; [exact: hK|exact: hg0].
by move=> _ [k hk <-]; exists k=> //; exact: interior_subset.
Qed.

End HomogeneousLocallyCompact.
