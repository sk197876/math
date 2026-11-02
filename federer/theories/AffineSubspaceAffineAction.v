(** Federer (1969), 2.7.16, example (5), printed p. 138: "For 0 < m < n,
    there exists no chi covariant integral with respect to the action of G
    on the space X of all m dimensional affine subspaces of R^n. In fact,
    choosing an m dimensional vectorsubspace W of R^n we now find that the
    isotropy group G^W equals M^{-1}(H x W), where H = GL(n, R) cap {h :
    h(W) = W}". Here G is the affine group of AffineGroupTopology.v, the
    pairs (g, z) of GL(V) x V standing for tau_z o g (so that M is the
    identity of this representation), and X is the space of m dimensional
    affine subspaces of AffineSubspaceSpace.v, with the initial topology of
    S |-> (dir S, nearest S). Federer presupposes that X is a homogeneous
    space of G in the sense of 2.7.1, p. 121. The action is A((g, z), S) =
    (tau_z o g)[S] (affine_subspace_image). It is continuous because dir
    (tau_z o g)[S] = g[dir S] depends continuously on (g, S)
    (LinearGrassmannAction.v) and nearest (tau_z o g)[S] = y - P(y) with y =
    z + g(nearest S) and P the projection onto g[dir S]. The orbit maps are
    open because those of the isometry group, a subgroup, are (example (7),
    affine_subspace_orbit_open), and the isometry group acts transitively.
    The isotropy group of the vector subspace W, the point tau_0 W of X,
    consists of the (g, z) with g[W] = W and z in W. The local erratum has
    no entry for this passage. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerMetric InnerNormedTopology
  LinearBasis Bilinear TensorUP Hom HomInner ModuleQuotient GrassmannSubspaces OrthogonalMaps
  IsotropyGroupTopology TopologicalProductMaps TopologicalGroupUP TopologicalGroupLaws
  HomogeneousSpaceUP HomogeneousSpaceLaws HomeomorphismUP HomSpaceTopology LinearGroupTopology LinearGroupSealed
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure GrassmannHomogeneousSpace AffineMaps
  AffineGroupTopology IsometryGroupStructure AffineSubspaceSpace SubspaceStabiliser SubgroupOrbitOpen
  LinearGrassmannAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AffineAction.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variables (m : nat) (c : 'I_m -> U) (n : nat) (b : 'I_n -> V).
Hypotheses (hc : is_basis c) (hb : is_basis b).
Local Notation HVV := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation VT := (inner_metric_space hB).
Local Notation GR := (grassmann_space hC hB hc hb).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation AG := (GL * VT)%type.
Local Notation X := (affine_subspace_space hC hB hc hb).
Local Notation P W := (grassmann_projection hC hB hc W).
Local Notation nearest := (affine_nearest hC hB hc).
Local Notation amap := (affine_group_map hB hb).
Local Notation lact := (linear_grassmann_action hC hB hc hb).

(** Source for [affine_subspace_affine_action]: "the action of G on the
    space X of all m dimensional affine subspaces of R^n", Federer
    2.7.16, p. 138, G the affine group: A((g, z), S) = (tau_z o g)[S].
    Definition. *)
Definition affine_subspace_affine_action (p : AG) (S : X) : X := affine_subspace_image hC hB hc hb p S.

(** Source for [affine_subspace_affine_direction]: dir (tau_z o g)[S] =
    g[dir S], Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma affine_subspace_affine_direction (p : AG) (S : X) :
  (affine_direction (affine_subspace_affine_action p S) : GR) = lact p.1 (affine_direction S : GR).
Proof.
rewrite /affine_subspace_affine_action affine_subspace_image_direction.
by apply: grassmann_ext=> y; split=> hy; exact: hy.
Qed.

(** Source for [affine_subspace_affine_nearest]: nearest (tau_z o g)[S]
    = y - P(y) with y = z + g(nearest S) and P the projection onto
    g[dir S], Federer 1.7.4, p. 30, and 2.7.16, p. 138. Supporting
    lemma. *)
Lemma affine_subspace_affine_nearest (p : AG) (S : X) :
  nearest (affine_subspace_affine_action p S) =
    amap p (nearest S) - P (affine_direction (affine_subspace_affine_action p S)) (amap p (nearest S)).
Proof.
by apply: affine_nearest_eq; apply: affine_subspace_image_mem; exact: affine_nearest_mem.
Qed.

(** Source for [affine_subspace_affine_action_continuous]: the action of
    the affine group on X is continuous, Federer 2.7.1, p. 121, for
    2.7.16, p. 138. Supporting lemma. *)
Lemma affine_subspace_affine_action_continuous :
  continuous (fun q : AG * X => affine_subspace_affine_action q.1 q.2).
Proof.
have hGa : continuous (fun r : GL * GR => lact r.1 r.2) by exact: linear_grassmann_action_continuous.
have hdir : continuous (fun q : AG * X => (affine_direction (affine_subspace_affine_action q.1 q.2) : GR)).
  have -> : (fun q : AG * X => (affine_direction (affine_subspace_affine_action q.1 q.2) : GR)) =
      (fun r : GL * GR => lact r.1 r.2) \o (fun q : AG * X => (q.1.1, (affine_direction q.2 : GR))).
    by apply: funext=> q; rewrite /= affine_subspace_affine_direction.
  move=> q; apply: (@continuous_comp (AG * X)%type (GL * GR)%type GR
    (fun q : AG * X => (q.1.1, (affine_direction q.2 : GR))) (fun r : GL * GR => lact r.1 r.2));
    last exact: hGa.
  apply: (@topological_pair_continuous (AG * X)%type GL GR).
    move=> r; apply: (@continuous_comp (AG * X)%type AG GL (@fst AG X) (@fst GL VT) r).
      exact: first_projection_continuous.
    exact: first_projection_continuous.
  move=> r; apply: (@continuous_comp (AG * X)%type X GR (@snd AG X) (fun S : X => (affine_direction S : GR)) r).
    exact: second_projection_continuous.
  exact: affine_direction_continuous.
have hAc := homogeneous_action_continuous (affine_group_homogeneous hB hb).
have hy : continuous (fun q : AG * X => (amap q.1 (nearest q.2) : VT)).
  move=> q; apply: (@continuous_comp (AG * X)%type (AG * VT)%type VT
    (fun q : AG * X => (q.1, (nearest q.2 : VT))) (fun r : AG * VT => affine_group_action hB hb r.1 r.2)).
    apply: (@topological_pair_continuous (AG * X)%type AG VT); first exact: first_projection_continuous.
    move=> r; apply: (@continuous_comp (AG * X)%type X VT (@snd AG X) (fun S : X => (nearest S : VT)) r).
      exact: second_projection_continuous.
    exact: affine_nearest_continuous.
  exact: hAc.
apply: affine_subspace_continuous_into=> //.
have hP : continuous (fun q : AG * X => (P (affine_direction (affine_subspace_affine_action q.1 q.2)) : HVV)).
  move=> q; apply: (continuous_comp (hdir q)); exact: grassmann_space_projection_continuous.
have hPy := hom_evaluation_continuous_comp hP hy.
have -> : (fun q : AG * X => (nearest (affine_subspace_affine_action q.1 q.2) : VT)) =
    (fun q : AG * X => (amap q.1 (nearest q.2) : VT)) -
      (fun q : AG * X => ((P (affine_direction (affine_subspace_affine_action q.1 q.2)) : Hom V V)
        (amap q.1 (nearest q.2)) : VT)).
  by apply: funext=> q; rewrite affine_subspace_affine_nearest.
by move=> q; apply: continuousB; [exact: hy|exact: hPy].
Qed.

(** Source for [affine_subspace_affine_action_compatible]: A(gh, S) =
    A(g, A(h, S)), Federer 2.7.1, p. 121, for the action of the affine
    group on X, 2.7.16, p. 138. Supporting lemma. *)
Lemma affine_subspace_affine_action_compatible (p q : AG) (S : X) :
  affine_subspace_affine_action (affine_group_mul hB hb p q) S =
    affine_subspace_affine_action p (affine_subspace_affine_action q S).
Proof. exact: affine_subspace_image_mul. Qed.

(** Source for [affine_subspace_affine_orbit_open]: the orbit maps of
    the action of the affine group on X are open, Federer 2.7.1,
    p. 121, for 2.7.16, p. 138. Supporting lemma: the orbit maps of the
    isometry group of example (7), a subgroup, are open
    (affine_subspace_orbit_open), and subgroup_orbit_open applies. *)
Lemma affine_subspace_affine_orbit_open (S : X) : is_open_map (orbit_map affine_subspace_affine_action S).
Proof.
have [mulS [invS [eS hS]]] := isometry_group_restriction_exists hB hb.
have [mulO [invO [eO hO]]] := orthogonal_group_restriction_exists hB hb.
have hI := affine_subspace_homogeneous hC hc hS hO.
apply: (@subgroup_orbit_open AG X (affine_group_mul hB hb) (affine_group_inv hB hb) (affine_group_unit hB hb)
  affine_subspace_affine_action (lch_group_topological (affine_group_lch hB hb))
  affine_subspace_affine_action_compatible (isometry_group hB hb)
  (subgroup_unit (isometry_group_subgroup hB hb)) (affine_subspace_action hC hB hc hb)).
  by [].
exact: (homogeneous_orbit_open hI).
Qed.

(** Source for [affine_subspace_affine_homogeneous]: the space X of all
    m dimensional affine subspaces of V is a homogeneous space of the
    affine group through A((g, z), S) = (tau_z o g)[S], Federer 2.7.1,
    p. 121, as presupposed in 2.7.16, example (5), p. 138. Direct
    formalisation; Federer gives no proof. *)
Theorem affine_subspace_affine_homogeneous :
  is_homogeneous_space (affine_group_mul hB hb) affine_subspace_affine_action.
Proof.
split.
- exact: affine_subspace_affine_action_continuous.
- exact: affine_subspace_affine_action_compatible.
- exact: affine_subspace_affine_orbit_open.
- move=> S; apply/seteqP; split=> // S' _.
  have [g hg] := affine_subspace_action_transitive S S'.
  by exists (set_val g).
Qed.

(** Source for [affine_subspace_affine_locally_compact]: X is a locally
    compact Hausdorff space, the standing hypothesis of Federer 2.7.1,
    p. 121, for 2.7.16, p. 138. Supporting lemma. *)
Lemma affine_subspace_affine_locally_compact : hausdorff_space X /\ locally_compact [set: X].
Proof.
have hH := @affine_subspace_space_hausdorff R U V C B hC hB m c n b hc hb.
split=> //.
exact: (homogeneous_space_locally_compact (affine_group_lch hB hb) affine_subspace_affine_homogeneous hH).
Qed.

(** Source for [affine_subspace_affine_isotropy]: "the isotropy group
    G^W equals M^{-1}(H x W), where H = GL(n, R) cap {h : h(W) = W}",
    Federer 2.7.16, p. 138: for the point tau_0 W of X, (g, z) fixes it
    exactly when g maps W onto W and z belongs to W. Direct
    formalisation, M being the identity of the representation of the
    affine group by pairs. *)
Theorem affine_subspace_affine_isotropy (W : G V m) :
  isotropy_subgroup affine_subspace_affine_action (affine_subspace_of 0 W : X) =
    [set p : AG | subspace_stabiliser hB hb (grassmann_val W) p.1 /\ grassmann_val W p.2].
Proof.
apply/seteqP; split=> p.
- rewrite /isotropy_subgroup /= => hp.
  have hd := affine_subspace_affine_direction p (affine_subspace_of 0 W : X).
  rewrite hp affine_subspace_of_direction in hd.
  split.
    have := @linear_grassmann_isotropy R U V C B hC hB m c n b hc hb W.
    move/seteqP=> [h1 _]; apply: h1.
    by rewrite /isotropy_subgroup /= -hd.
  have h0 : affine_points (affine_subspace_affine_action p (affine_subspace_of 0 W : X)) (amap p 0).
    apply: affine_subspace_image_mem; rewrite affine_subspace_of_points /affine_coset /= subr0.
    exact: subspace_zero.
  rewrite hp affine_subspace_of_points /affine_coset /= subr0 affine_group_map_zero in h0.
  exact: h0.
- move=> [hg hz]; rewrite /isotropy_subgroup /=.
  apply: (@affine_subspace_eq_point R V m _ _ p.2).
  + have hiso := @linear_grassmann_isotropy R U V C B hC hB m c n b hc hb W.
    move/seteqP: hiso=> [_ h2].
    have h3 := h2 p.1 hg; rewrite /isotropy_subgroup /= in h3.
    by rewrite affine_subspace_affine_direction affine_subspace_of_direction h3.
  + rewrite -(affine_group_map_zero p); apply: affine_subspace_image_mem.
    rewrite affine_subspace_of_points /affine_coset /= subr0; exact: subspace_zero.
  + by rewrite affine_subspace_of_points /affine_coset /= subr0.
Qed.

End AffineAction.

Arguments affine_subspace_affine_action {R U V C B} hC hB {m c n b} hc hb p S.
