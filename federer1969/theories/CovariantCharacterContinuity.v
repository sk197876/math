(** Federer (1969), 2.7.1, printed p. 122: "A Daniell integral mu on K(X) is
    called a chi covariant integral if and only if chi: G -> R and mu(u o
    A_g) = chi(g) mu(u) whenever u in K(X), g in G. In case mu <> 0, it
    follows that chi is a continuous homomorphism of G into the
    multiplicative group R ~ {0}." The algebraic part is proved in
    CovariantIntegralLaws.v. For the continuity, choose u in K(X) with mu(u)
    <> 0, g_0 in G and a compact neighbourhood N of g_0. The supports of u o
    A_g, g in N, lie in the compact set C = {A(g^{-1}, y) : g in N, y in spt
    u}. The bound of 2.5.13 for Daniell integrals on functions vanishing
    outside C, together with the uniform continuity of (x,g) |-> u(A(g,x))
    on C near g_0, gives |chi(g) - chi(g_0)| |mu(u)| = |mu(u o A_g - u o
    A_{g_0})| small for g near g_0. Federer leaves this argument to the
    reader. The continuity of the inversion of G is used to see that C is
    compact. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground TopologicalProductMaps HomeomorphismUP
  TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP HomogeneousSpaceLaws FunctionLatticeUP
  DaniellIntegralUP DaniellIntegralAlgebra CompactSupportFunctionUP CompactSupportFunctionLattice
  VectorFunctionLattice CompactUniformNorm CompactSectionUniform CompactDaniellUniformBound
  DaniellSpaceCompactness CovariantIntegralUP CovariantIntegralLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CharacterContinuity.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hT : is_topological_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hlG : locally_compact [set: G].
Hypothesis hX : hausdorff_space X.
Hypothesis hlX : locally_compact [set: X].
Local Notation K := (@compactly_supported_continuous_functions R X).
(** Source for [hG]: the group laws of the topological group G,
    Federer 2.7.1, p. 121, used in this section. *)
Let hG := topological_group_laws hT.

(** Source for [translate_support_bound]: for g in N the function
    u o A_g vanishes outside {A(h^{-1}, y) : h in N, y in spt u},
    supporting the continuity of chi in Federer 2.7.1, p. 122. *)
Lemma translate_support_bound (u : X -> R) (N : set G) g x :
  N g -> ~ ((fun p : G * X => A (inv p.1) p.2) @` (N `*` real_function_support u)) x ->
  u (A g x) = 0.
Proof.
move=> hg hx; apply: real_function_zero_off_support=> hs; apply: hx.
exists (g, A g x)=> //=; exact: homogeneous_translation_inverse_left hG hA g x.
Qed.

(** Source for [covariant_character_continuous]: "In case mu <> 0, it
    follows that chi is a continuous homomorphism", Federer 2.7.1,
    p. 122: continuity of chi as a map of G into R. *)
Theorem covariant_character_continuous (chi : G -> R) (mu : (X -> R) -> R) :
  is_covariant_integral A chi mu -> (exists u, K u /\ mu u <> 0) ->
  continuous (chi : G -> real_line_metric R).
Proof.
move=> [hd hc] [u [hu hmu]] g0.
apply/cvg_ballP=> eps heps.
have [N hN [hNc _]] := @hlG g0 I; rewrite withinET in hN.
have hg0 : N g0 := nbhs_singleton hN.
pose C := (fun p : G * X => A (inv p.1) p.2) @` (N `*` real_function_support u).
have hAc : continuous (fun q : G * X => A q.1 q.2) := homogeneous_action_continuous hA.
have hinvc : continuous (fun p : G * X => A (inv p.1) p.2).
  have h1 := @first_factor_map_continuous G G X inv (topological_group_inv_continuous hT).
  by move=> p; have := continuous_comp (h1 p) (@hAc (inv p.1, p.2)); exact.
have hCc : compact C.
  apply: continuous_compact; first exact: continuous_subspaceT.
  exact: compact_setX hNc hu.2.
have [M [hM hbound]] := @compact_daniell_fixed_support_bound R X mu C hX hlX hCc hd.
have hmupos : 0 < `|mu u| by rewrite normr_gt0; apply/eqP.
have hM1 : 0 < M + 1 by rewrite ltr_wpDl.
pose d := eps * `|mu u| / (M + 1).
have hdpos : 0 < d by rewrite /d divr_gt0 // mulr_gt0.
pose h := fun p : X * G => u (A p.2 p.1).
have hh : continuous (h : X * G -> real_line_metric R).
  have hsw : continuous (fun p : X * G => (p.2, p.1)).
    by apply: topological_pair_continuous;
      [exact: second_projection_continuous|exact: first_projection_continuous].
  move=> p; have h1 := continuous_comp (hsw p) (@hAc (p.2, p.1)).
  by have := continuous_comp h1 (hu.1 (A p.2 p.1)); exact.
have [V [hVo [hVg0 hVu]]] := @compact_sections_locally_uniform R X G h C g0 d hh hCc hdpos.
have hVN : nbhs g0 (V `&` N) by apply: filterI=> //; exact: open_nbhs_nbhs.
apply: (filterS _ hVN)=> g [hgV hgN].
have hug := compactly_supported_translate hG hA g hu.
have hug0 := compactly_supported_translate hG hA g0 hu.
pose f := fun x => (u \o A g) x - (u \o A g0) x.
have hf : K f.
  exact: (vector_function_lattice_difference (@compact_support_vector_lattice R X) hug hug0).
have hfz : forall x, ~ C x -> f x = 0.
  by move=> x hx; rewrite /f /= (translate_support_bound hgN hx) (translate_support_bound hg0 hx) subrr.
have hfe : forall x, C x -> `|f x| <= d.
  by move=> x hx; apply: ltW; exact: hVu g x hgV hx.
have hb := hbound f hf hfz d hdpos hfe.
have hmuf : mu f = (chi g - chi g0) * mu u.
  rewrite /f (vector_lattice_additive_difference (@compact_support_vector_lattice R X) _ hug hug0).
    by rewrite (hc u g hu) (hc u g0 hu) mulrBl.
  by move=> f1 f2 h1 h2; have := daniell_integral_add hd h1 h2.
rewrite hmuf normrM in hb.
have hdM : d * M < eps * `|mu u|.
  have hlt : d * M < d * (M + 1) by rewrite ltr_pM2l // ltrDl ltr01.
  by rewrite /d divfK ?gt_eqF // in hlt.
have hlt : `|chi g - chi g0| * `|mu u| < eps * `|mu u| := le_lt_trans hb hdM.
rewrite ltr_pM2r // in hlt.
by rewrite /ball /= distrC.
Qed.

(** Source for [covariant_character_homomorphism]: "In case mu <> 0,
    it follows that chi is a continuous homomorphism of G into the
    multiplicative group R ~ {0}", Federer 2.7.1, p. 122. Direct
    formalisation. *)
Theorem covariant_character_homomorphism (chi : G -> R) (mu : (X -> R) -> R) :
  is_covariant_integral A chi mu -> (exists u, K u /\ mu u <> 0) ->
  [/\ forall g h, chi (mul g h) = chi g * chi h, chi e = 1, forall g, chi g != 0 &
    continuous (chi : G -> real_line_metric R)].
Proof.
move=> hmu hne; have [u [hu hu0]] := hne.
have hc := covariant_integral_law hmu.
split.
- exact (covariant_character_multiplicative hG hA hc hu hu0).
- exact (covariant_character_unit hG hA hc hu hu0).
- exact (covariant_character_nonzero hG hA hc hu hu0).
- exact (covariant_character_continuous hmu hne).
Qed.

End CharacterContinuity.
