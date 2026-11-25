(** Federer (1969), 2.7.12, printed p. 129: "For each closed subgroup S of
    G, Weil's condition implies that the homogeneous space G/S admits a
    nonzero invariant integral if and only if Delta_S = Delta_G | S. In
    particular, this equation holds whenever S is normal, because in this
    case every Haar integral of the group G/S is G invariant (alternately,
    because G acts uniformly on G/S). Considering the special case when S =
    ker Delta_G, one finds that ker Delta_G is unimodular." G is a locally
    compact Hausdorff topological group. The space G/S is any space of left
    cosets in the sense of CosetSpaceUP.v, with projection pi and the action
    A(g, hS) = g h S of 2.7.1, p. 122 (is_coset_action); by 2.7.1 it is a
    locally compact Hausdorff homogeneous space of G, and the isotropy group
    of the point S = pi(e) is S (closed_subgroup_coset_homogeneous). A
    closed subgroup S carries the restricted group structure of
    IsotropyGroupTopology.v, and Delta_S is a modular function for it. The
    first claim is 2.7.11(1) with chi = 1 and x = pi(e); since the isotropy
    subgroup of pi(e) equals S as a set, the subtype structure is
    transported along this equation. For a normal subgroup S the proof
    follows Federer's alternative "because G acts uniformly on G/S": the
    criterion of 2.7.3, p. 123 (acts_uniformly_iff), holds with W = pi(h M)
    for a neighbourhood M of e with M M^{-1} M contained in a given
    neighbourhood of e, and 2.7.4, p. 123, gives a nonzero monotone
    invariant integral on K(G/S). This avoids the construction of the
    quotient group G/S needed for Federer's first reason. ker Delta_G = {g:
    Delta_G(g) = 1} is a closed normal subgroup, because Delta_G is a
    continuous homomorphism (2.7.8 and 2.7.1, p. 122); hence Delta_S =
    Delta_G | S = 1 for S = ker Delta_G, and S is unimodular by
    UnimodularGroups.v. The local erratum has no entry for p. 129. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground TopologicalProductMaps HomeomorphismUP TopologicalGroupUP
  TopologicalGroupLaws HomogeneousSpaceUP HomogeneousSpaceLaws CompactSupportFunctionUP
  CovariantIntegralUP HaarIntegralUP HaarIntegralExistence ModularFunctionUP ModularFunction
  IsotropyGroupTopology CosetSpaceUP CosetSpaceLaws CosetSpace CosetSpaceHomogeneous
  UniformActionUP UniformActionLaws InvariantIntegralExistence WeilCondition UnimodularGroupUP
  UnimodularGroups NormalSubgroupUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ClosedSubgroupCosets.
Variable R : realType.
Variables G Q : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (S : set G) (pi : G -> Q).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hS : is_subgroup mul inv e S.
Hypothesis hSc : closed S.
Hypothesis hQ : is_left_coset_space mul inv S pi.
Variable A : G -> Q -> Q.
Hypothesis hAc : is_coset_action mul pi A.
Local Notation KQ := (@compactly_supported_continuous_functions R Q).

(** Source for [coset_space_invariant_integral_iff]: "For each closed
    subgroup S of G, Weil's condition implies that the homogeneous space
    G/S admits a nonzero invariant integral if and only if
    Delta_S = Delta_G | S", Federer 2.7.12, p. 129. Direct
    formalisation: 2.7.11(1) for chi = 1 and the point pi(e), whose
    isotropy subgroup is S (2.7.1, p. 122). *)
Theorem coset_space_invariant_integral_iff (mulS : S -> S -> S) (invS : S -> S) (eS : S)
    (DG : G -> R) (DS : S -> R) :
  is_subgroup_restriction mul inv e S mulS invS eS ->
  is_modular_function mul inv DG -> is_modular_function mulS invS DS ->
  (exists nu : (Q -> R) -> R, is_invariant_integral A nu /\ exists2 v, KQ v & nu v <> 0) <->
  forall t : S, DS t = DG (set_val t).
Proof.
move=> hR hDG hDS.
have hT := lch_group_topological hG.
have [hQH hQl hAh hiso] :=
  closed_subgroup_coset_homogeneous hT hS hQ hSc (lch_group_locally_compact hG) hAc.
move: mulS invS eS hR DS hDS; rewrite -hiso=> mulS invS eS hR DS hDS.
have h1M (g h : G) : (fun _ : G => 1 : R) (mul g h) = (fun _ : G => 1 : R) g * (fun _ : G => 1) h.
  by rewrite mulr1.
have h10 (g : G) : (fun _ : G => 1 : R) g != 0 by exact: oner_neq0.
have h1c : continuous ((fun _ : G => 1 : R) : G -> real_line_metric R) by apply: cst_continuous.
rewrite (covariant_integral_exists_iff_weil hG hAh hQH hQl hR hDG hDS h1M h10 h1c) /weil_condition.
by split=> h t; [rewrite -h mul1r|rewrite mul1r h].
Qed.

End ClosedSubgroupCosets.

Section NormalCosetUniform.
Variables G Q : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (S : set G) (pi : G -> Q).
Hypothesis hT : is_topological_group mul inv e.
Hypothesis hN : is_normal_subgroup mul inv e S.
Hypothesis hQ : is_left_coset_space mul inv S pi.
Variable A : G -> Q -> Q.
Hypothesis hAc : is_coset_action mul pi A.
(** Source for [hgl]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hgl := topological_group_laws hT.

(** Source for [triple_product_neighbourhood]: for each neighbourhood
    N of e there is an open neighbourhood M of e with
    M M^{-1} M subset N, supporting "G acts uniformly on G/S", Federer
    2.7.12, p. 129. Supporting lemma, by the continuity of
    (a,b) |-> a b and (a,b) |-> a b^{-1} at (e,e). *)
Lemma triple_product_neighbourhood (N : set G) : nbhs e N ->
  exists2 M : set G, open M /\ M e & forall a b c, M a -> M b -> M c -> N (mul (mul a (inv b)) c).
Proof.
move=> hNe.
have hmc : continuous (fun p : G * G => mul p.1 p.2) := topological_group_mul_continuous hT.
have hm := hmc (e, e).
rewrite /continuous_at /= (group_mul1g hgl) in hm.
have [[W1 W2] /= [hW1 hW2] hW12] := hm _ hNe.
have hic : continuous inv := topological_group_inv_continuous hT.
have hdr : continuous (fun p : G * G => mul p.1 (inv p.2)).
  have -> : (fun p : G * G => mul p.1 (inv p.2)) =
      (fun r : G * G => mul r.1 r.2) \o (fun p : G * G => (p.1, inv p.2)) by [].
  move=> p; apply: continuous_comp; last exact: (topological_group_mul_continuous hT).
  apply: topological_pair_continuous; first exact: first_projection_continuous.
  move=> q; apply: continuous_comp; first exact: second_projection_continuous.
  exact: hic.
have hd := hdr (e, e).
rewrite /continuous_at /= (group_inv1 hgl) (group_mul1g hgl) in hd.
have [[V1 V2] /= [hV1 hV2] hV12] := hd _ hW1.
have hM0 : nbhs e (V1 `&` V2 `&` W2) by apply: filterI=> //; exact: filterI.
exists (V1 `&` V2 `&` W2)°; first by split; [exact: open_interior|exact: nbhs_singleton (nbhs_interior hM0)].
move=> a b c ha hb hc.
have [[ha1 _] _] := interior_subset ha.
have [[_ hb2] _] := interior_subset hb.
have [_ hc2] := interior_subset hc.
have hab : W1 (mul a (inv b)) := hV12 (a, b) (conj ha1 hb2).
exact: (hW12 (mul a (inv b), c) (conj hab hc2)).
Qed.

(** Source for [normal_coset_action_uniform]: "G acts uniformly on
    G/S" when S is normal, Federer 2.7.12, p. 129, in the form of the
    criterion of 2.7.3, p. 123: for each neighbourhood V of hS there is
    a neighbourhood W of hS such that W cap A_g(W) <> empty implies
    A_g(W) subset V. Direct formalisation with W = pi(h M), where
    M M^{-1} M subset {m: pi(h m) in V}: if pi(h m1) = pi(g h m2), then
    (h m1 m2^{-1} m3)^{-1} g h m3 = k^{-1} s k with
    s = (h m1)^{-1} g h m2 in S and k = m2^{-1} m3, which lies in S by
    normality. *)
Theorem normal_coset_action_uniform : uniform_action_condition A.
Proof.
move=> q V hV.
have [h hq] := coset_projection_onto hQ q; rewrite -hq in hV *.
pose N := [set m | V (pi (mul h m))].
have hNe : nbhs e N.
  have hc : continuous (fun m => pi (mul h m)).
    move=> m; apply: continuous_comp; first exact: left_translation_continuous hT h m.
    exact: (coset_projection_continuous hQ).
  have := hc e; rewrite /continuous_at /= (group_mulg1 hgl)=> hce; exact: hce _ hV.
have [M [hMo hMe] hMN] := triple_product_neighbourhood hNe.
exists (pi @` (mul h @` M)).
  apply: open_nbhs_nbhs; split.
    apply: (coset_projection_open hT hQ); exact: left_translation_open_map hT h M hMo.
  by exists (mul h e); [exists e|rewrite (group_mulg1 hgl)].
move=> g [y [[a1 [m1 hm1 <-] hy1] [w0 [a2 [m2 hm2 <-] <-] hy2]]] z [w [a3 [m3 hm3 <-] <-] <-].
rewrite hAc in hy2 *.
have hs : S (mul (inv (mul h m1)) (mul g (mul h m2))).
  exact: (coset_projection_eq hQ _ _).1 (etrans hy1 (esym hy2)).
have hconj := normal_subgroup_conjugate hN (inv (mul (inv m2) m3)) hs.
have heq : pi (mul h (mul (mul m1 (inv m2)) m3)) = pi (mul g (mul h m3)).
  apply/(coset_projection_eq hQ).
  have -> : mul (inv (mul h (mul (mul m1 (inv m2)) m3))) (mul g (mul h m3)) =
      mul (mul (inv (mul (inv m2) m3)) (mul (inv (mul h m1)) (mul g (mul h m2))))
        (inv (inv (mul (inv m2) m3))).
    rewrite !(group_invM hgl) !(group_invK hgl) !(group_mulA hgl).
    by rewrite (group_mulgK hgl).
  exact: hconj.
rewrite hAc -heq; exact: (hMN m1 m2 m3 hm1 hm2 hm3).
Qed.

(** Source for [normal_coset_action_acts_uniformly]: "because G acts
    uniformly on G/S", Federer 2.7.12, p. 129, for a normal subgroup S.
    Direct formalisation, by the criterion of 2.7.3, p. 123. *)
Theorem normal_coset_action_acts_uniformly : acts_uniformly A.
Proof.
apply/(acts_uniformly_iff hgl (coset_action_homogeneous hT hQ hAc)).
exact: normal_coset_action_uniform.
Qed.

End NormalCosetUniform.

Section NormalSubgroupModular.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (S : set G).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hN : is_normal_subgroup mul inv e S.
Hypothesis hSc : closed S.
(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121,
    used in this section. *)
Let hT := lch_group_topological hG.
(** Source for [hgl]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hgl := topological_group_laws hT.

(** Source for [normal_subgroup_invariant_integral]: G/S admits a
    nonzero invariant integral when S is a closed normal subgroup,
    "because G acts uniformly on G/S", Federer 2.7.12, p. 129, by 2.7.4,
    p. 123. Supporting theorem, for every space of left cosets G/S with
    the action A(g, hS) = g h S. *)
Theorem normal_subgroup_invariant_integral (Q : topologicalType) (pi : G -> Q) (A : G -> Q -> Q) :
  is_left_coset_space mul inv S pi -> is_coset_action mul pi A ->
  exists nu : (Q -> R) -> R, is_nonzero_monotone_invariant_integral A nu.
Proof.
move=> hQ hAc.
have [hQH hQl hAh _] := closed_subgroup_coset_homogeneous hT (normal_subgroup_subgroup hN) hQ hSc
  (lch_group_locally_compact hG) hAc.
apply: (uniform_action_invariant_integral_exists R hgl hAh hQH hQl); first by exists (pi e).
exact: (normal_coset_action_acts_uniformly hT hN hQ hAc).
Qed.

(** Source for [normal_subgroup_modular_restriction]: "In particular,
    this equation [Delta_S = Delta_G | S] holds whenever S is normal",
    Federer 2.7.12, p. 129, for a closed normal subgroup S. Direct
    formalisation, by normal_subgroup_invariant_integral for the sealed
    coset space G/S (2.7.1, p. 122) and
    coset_space_invariant_integral_iff. *)
Theorem normal_subgroup_modular_restriction (mulS : S -> S -> S) (invS : S -> S) (eS : S)
    (DG : G -> R) (DS : S -> R) :
  is_subgroup_restriction mul inv e S mulS invS eS ->
  is_modular_function mul inv DG -> is_modular_function mulS invS DS ->
  forall t : S, DS t = DG (set_val t).
Proof.
move=> hR hDG hDS.
have hS := normal_subgroup_subgroup hN.
have hQ := coset_space_specification hgl hS.
have [A hAc] := coset_action_exists hgl hQ.
have [nu hnu] := normal_subgroup_invariant_integral hQ hAc.
apply/(coset_space_invariant_integral_iff hG hS hSc hQ hAc hR hDG hDS).
exists nu; split; first exact: (nonzero_invariant_integral_invariant hnu).
exact: (nonzero_invariant_integral_nonzero hnu).
Qed.

End NormalSubgroupModular.

Section ModularKernel.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Variable DG : G -> R.
Hypothesis hDG : is_modular_function mul inv DG.

(** Source for [modular_kernel_normal]: "the special case when
    S = ker Delta_G", Federer 2.7.12, p. 129: ker Delta_G is a normal
    subgroup, since Delta_G is a homomorphism of G into the
    multiplicative group of positive numbers (2.7.8, p. 126, and 2.7.1,
    p. 122). Supporting lemma. *)
Lemma modular_kernel_normal : is_normal_subgroup mul inv e [set g | DG g = 1].
Proof.
have [hM h1] := modular_function_homomorphism hG hDG.
have hgl := topological_group_laws (lch_group_topological hG).
have hD0 g : DG g != 0 := lt0r_neq0 (modular_function_positive hDG g).
have hinv g : DG (inv g) = (DG g)^-1.
  apply: (mulIf (hD0 g)); rewrite -hM (group_mulVg hgl) h1.
  by rewrite (mulVf (hD0 g)).
split; first split.
- exact: h1.
- by move=> g h hg hh; rewrite /= hM hg hh mulr1.
- by move=> g hg; rewrite /= hinv hg invr1.
- by move=> g s hs; rewrite /= !hM hs mulr1 hinv (mulfV (hD0 g)).
Qed.

(** Source for [modular_kernel_closed]: ker Delta_G is closed, since
    Delta_G is continuous (2.7.8, p. 126), as required by "For each
    closed subgroup S of G" in the special case S = ker Delta_G,
    Federer 2.7.12, p. 129. Supporting lemma. *)
Lemma modular_kernel_closed : closed [set g | DG g = 1].
Proof.
have h1 : closed ([set y | y = 1] : set (real_line_metric R)) := @closed_eq R 1.
by apply: (preimage_closed _ h1)=> g _; exact: (modular_function_continuous hDG).
Qed.

(** Source for [modular_kernel_unimodular]: "Considering the special
    case when S = ker Delta_G, one finds that ker Delta_G is
    unimodular", Federer 2.7.12, p. 129, for ker Delta_G with its
    restricted group structure. Direct formalisation: Delta_S =
    Delta_G | S = 1 by normal_subgroup_modular_restriction, and
    unimodular_iff_modular_unit applies. *)
Theorem modular_kernel_unimodular
    (mulS : [set g | DG g = 1] -> [set g | DG g = 1] -> [set g | DG g = 1])
    (invS : [set g | DG g = 1] -> [set g | DG g = 1]) (eS : [set g | DG g = 1]) :
  is_subgroup_restriction mul inv e [set g | DG g = 1] mulS invS eS -> is_unimodular R mulS invS.
Proof.
move=> hR.
have hSG := subgroup_restriction_locally_compact_hausdorff hR hG modular_kernel_closed.
have [DS hDS] := modular_function_exists R hSG.
have h := normal_subgroup_modular_restriction hG modular_kernel_normal modular_kernel_closed hR hDG hDS.
by apply/(unimodular_iff_modular_unit hSG hDS)=> t; rewrite h; exact: set_valP t.
Qed.

End ModularKernel.
