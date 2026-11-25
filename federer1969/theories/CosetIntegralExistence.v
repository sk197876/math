(** Federer (1969), 2.7.10, printed pp. 127–128: "Lemma. To each x in X and
    each left Haar integral mu of the isotropy group G^x corresponds a
    linear epimorphism mu^x: K(G) -> K(X) with the following properties: (1)
    ... (6)". The proof begins: "For each u in K(G) the map w: G -> R, w(g)
    = mu_s[u(g s)] whenever g in G, is continuous, because u is uniformly
    continuous; moreover w(g t) = w(g) whenever t in G^x, because mu is left
    invariant; hence there exists a unique continuous map mu^x(u): X -> R
    with mu^x(u) o A^x = w." The uniform continuity is that of 2.7.5, p.
    125, for the uniformity of G with the basis {(y,z): y z^{-1} in V}, V a
    neighbourhood of e: if g g0^{-1} in V, then (gs)(g0 s)^{-1} = g g0^{-1}
    in V for every s in G^x, so that |u(gs) - u(g0 s)| <= delta. For g and
    g0 in a compact neighbourhood N of g0 the functions s |-> u(gs) and s
    |-> u(g0 s) vanish outside the compact set G^x cap {h^{-1} y: h in N, y
    in spt u}, and the bound of a Daniell integral on functions supported in
    a fixed compact set (2.5.13, 2.6.4) gives |w(g) - w(g0)| <= delta C. The
    factorisation through A^x uses that A^x is open and onto: mu^x(u)(y) =
    w(g) for any g with A(g,x) = y, and the inverse image of an open set
    under mu^x(u) is the image under A^x of its inverse image under w. The
    compactness of spt mu^x(u) follows from spt mu^x(u) subset A^x(spt u).
    The properties (2)–(6), the linearity and the surjectivity are those of
    CosetIntegralLaws.v. Standing hypotheses as in 2.7.1, p. 121: G is a
    locally compact Hausdorff topological group and X a homogeneous space of
    G; X is assumed Hausdorff, which makes G^x closed. The local compactness
    of X is not used. The local erratum has no entry for pp. 127–128. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground FunctionLatticeUP FunctionLatticeSeminormUP
  MonotoneDaniellIntegralUP DaniellIntegralUP DaniellIntegralNegation CompactSupportFunctionUP
  CompactSupportFunctionLattice VectorFunctionLattice CompactUniformNorm CompactDaniellUniformBound
  DaniellSpaceCompactness HomeomorphismUP TopologicalGroupUP TopologicalGroupLaws
  HomogeneousSpaceUP HomogeneousSpaceLaws CovariantIntegralUP HaarIntegralUP UniformActionUP
  GroupUniformity UniformityCompactSupport SubtypeCompactHausdorff IsotropyGroupTopology
  CosetIntegralUP CosetIntegralLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_map_factor_continuous]: "hence there exists a
    unique continuous map mu^x(u): X -> R with mu^x(u) o A^x = w",
    Federer 2.7.10, proof, p. 128, where A^x is open with im A^x = X
    (2.7.1, p. 121): a function f on Y is continuous when f o p is
    continuous for an open map p onto Y. Supporting lemma: the image
    under p of an open neighbourhood of t on which f o p lies in a
    neighbourhood of f(p(t)) is an open neighbourhood of p(t). *)
Lemma open_map_factor_continuous (T Y Z : topologicalType) (p : T -> Y) (f : Y -> Z) :
  is_open_map p -> (forall y, exists t, p t = y) -> continuous (f \o p) -> continuous f.
Proof.
move=> hp hs hc y; have [t <-] := hs y.
move=> N /(hc t) /=; rewrite nbhsE=> -[O [hO hOt] hON].
rewrite nbhsE; exists (p @` O); first by split; [exact: hp|exists t].
by move=> _ [s hs' <-]; exact: hON.
Qed.

Section CosetIntegralExistence.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (x : X).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hX : hausdorff_space X.
Local Notation S := (isotropy_subgroup A x).
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hR : is_subgroup_restriction mul inv e S mulS invS eS.
Variable mu : (S -> R) -> R.
Hypothesis hmu : is_left_haar_integral mulS mu.
Local Notation KG := (@compactly_supported_continuous_functions R G).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KS := (@compactly_supported_continuous_functions R S).

(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121,
    used in this section. *)
Let hT := lch_group_topological hG.
(** Source for [hgl]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hgl := topological_group_laws hT.
(** Source for [hSc]: "the isotropy subgroup G^x ... is closed in G",
    Federer 2.7.1, pp. 121–122, used in this section. *)
Let hSc : closed S := isotropy_subgroup_closed hA hX.
(** Source for [hSH]: G^x is Hausdorff, supporting "the isotropy group
    G^x", Federer 2.7.10, p. 127. *)
Let hSH : hausdorff_space S := @set_type_hausdorff G S (lch_group_hausdorff hG).
(** Source for [hSl]: G^x is locally compact, supporting "the isotropy
    group G^x", Federer 2.7.10, p. 127. *)
Let hSl : locally_compact [set: S] := set_type_locally_compact (lch_group_locally_compact hG) hSc.
(** Source for [hmuD]: mu is a monotone Daniell integral on K(G^x),
    part of "left Haar integral", Federer 2.7.2, p. 122. *)
Let hmuD := nonzero_invariant_integral_monotone hmu.
(** Source for [hmuL]: mu is linear on K(G^x), Federer 2.5.13, p. 106,
    applied to the Daniell integral mu. *)
Let hmuL := daniell_compact_support_linear (monotone_daniell_is_daniell hmuD).

(** Source for [coset_section_integral_continuous]: "For each u in
    K(G) the map w: G -> R, w(g) = mu_s[u(g s)] whenever g in G, is
    continuous, because u is uniformly continuous", Federer 2.7.10,
    proof, p. 128. The uniformity is that of 2.7.5, p. 125, with the
    basis {(y,z): y z^{-1} in V}. Direct formalisation. *)
Theorem coset_section_integral_continuous u : KG u ->
  continuous ((fun g => mu (fun s : S => u (mul g (set_val s)))) : G -> real_line_metric R).
Proof.
move=> hu g0; apply/cvg_ballP=> eps heps.
have hl := lch_group_locally_compact hG.
have [N hN [hNc _]] := @hl g0 I; rewrite withinET in hN.
have hg0 : N g0 := nbhs_singleton hN.
pose C := (fun p : G * G => mul (inv p.1) p.2) @` (N `*` real_function_support u).
have hCc : compact C.
  apply: continuous_compact; first by apply: continuous_subspaceT; exact: division_continuous hT.
  exact: compact_setX hNc hu.2.
pose KS0 : set S := set_val @^-1` (C `&` S).
have hKS : compact KS0 := set_type_compact_preimage (compact_closedI hCc hSc) (@subIsetr _ _ _).
have [Cb [hCb hbound]] := compact_daniell_fixed_support_bound hSH hSl hKS
  (monotone_daniell_is_daniell hmuD).
have hCb1 : 0 < Cb + 1 by rewrite ltr_wpDl.
pose d := eps / (Cb + 1).
have hd : 0 < d by rewrite divr_gt0.
have [hE hnb _ _] := right_division_entourage_basis hT.
have [D hD hDu] := compactly_supported_uniformly_continuous hE hnb hu hd.
have [V hV hVD] := hD.
have hW : nbhs g0 [set g | V (mul g (inv g0))].
  have hc := right_translation_continuous hT (inv g0) g0.
  by apply: hc; rewrite /= (group_mulgV hgl).
apply: (filterS _ (filterI hN hW))=> g [hgN hgV].
have hug := coset_section_compact x hG hA hX g hu.
have hug0 := coset_section_compact x hG hA hX g0 hu.
pose f := fun s : S => u (mul g (set_val s)) - u (mul g0 (set_val s)).
have hf : KS f := vector_function_lattice_difference (@compact_support_vector_lattice R S) hug hug0.
have hfz : forall s, ~ KS0 s -> f s = 0.
  move=> s hs; have hz h : N h -> u (mul h (set_val s)) = 0.
    move=> hh; apply: real_function_zero_off_support=> hsu; apply: hs; split; last exact: set_valP.
    by exists (h, mul h (set_val s))=> //=; rewrite (group_mulKg hgl).
  by rewrite /f (hz g hgN) (hz g0 hg0) subrr.
have hfe : forall s, KS0 s -> `|f s| <= d.
  move=> s _; apply: hDu; apply: hVD.
  by rewrite /division_entourage /= (group_invM hgl) (group_mulA hgl) (group_mulgK hgl).
have hb := hbound f hf hfz d hd hfe.
have hmuf : mu f = mu (fun s : S => u (mul g (set_val s))) - mu (fun s : S => u (mul g0 (set_val s))).
  exact: (vector_lattice_additive_difference (@compact_support_vector_lattice R S) hmuL.1 hug hug0).
have hdC : d * Cb < eps.
  have hlt : d * Cb < d * (Cb + 1) by rewrite ltr_pM2l // ltrDl ltr01.
  by rewrite /d divfK ?gt_eqF // in hlt.
rewrite /ball /= distrC -hmuf.
exact: le_lt_trans hb hdC.
Qed.

(** Source for [coset_integral_exists]: "hence there exists a unique
    continuous map mu^x(u): X -> R with mu^x(u) o A^x = w", Federer
    2.7.10, proof, p. 128, together with "mu^x: K(G) -> K(X)", p. 127.
    Existence proof for the specification is_coset_integral:
    mu^x(u)(y) = w(g) for a choice of g with A(g,x) = y; the choice does
    not matter, since w(g t) = w(g) for t in G^x
    (coset_section_orbit_eq). The support of mu^x(u) lies in the compact
    set A^x(spt u). *)
Theorem coset_integral_exists : exists M : (G -> R) -> X -> R, is_coset_integral mul A x mu M.
Proof.
have /choice [pick hpick] : forall y : X, exists g : G, A g x = y := homogeneous_transitive hA x.
pose M (u : G -> R) (y : X) := mu (fun s : S => u (mul (pick y) (set_val s))).
have hval u g : KG u -> M u (A g x) = mu (fun s : S => u (mul g (set_val s))).
  by move=> hu; apply: (coset_section_orbit_eq hG hA hX hR hmu hu); exact: hpick.
exists M; split=> [u hu|u g hu]; last exact: hval.
split.
- apply: (@open_map_factor_continuous G X (real_line_metric R) (orbit_map A x) (M u)).
  + exact: homogeneous_orbit_open hA x.
  + exact: homogeneous_transitive hA x.
  + have -> : M u \o orbit_map A x = (fun g => mu (fun s : S => u (mul g (set_val s)))).
      by apply: funext=> g; rewrite /= /orbit_map hval.
    exact: coset_section_integral_continuous.
- have hcl : compact (orbit_map A x @` real_function_support u).
    apply: continuous_compact; last exact: hu.2.
    by apply: continuous_subspaceT; exact: orbit_map_continuous hA x.
  apply: (real_function_compact_support_in_closed_set hcl (compact_closed hX hcl))=> y hy.
  rewrite -(hpick y) hval //; apply: contrapT=> hne.
  have [s hs] := coset_section_nonzero hG hA hX hmu hu hne.
  apply: hy; exists (mul (pick y) (set_val s)); first exact: subset_closure.
  by rewrite /orbit_map (isotropy_coset_orbit hA (pick y) s) hpick.
Qed.

(** Source for [isotropy_integral_epimorphism]: Federer 2.7.10,
    pp. 127–128: "To each x in X and each left Haar integral mu of the
    isotropy group G^x corresponds a linear epimorphism
    mu^x: K(G) -> K(X) with the following properties: (1) mu^x(u)(g x)
    = mu_s[u(g s)] whenever u in K(G), g in G. (2) spt mu^x(u) =
    A^x(spt u) whenever u in K(G)+. (3) mu^x[(v o A^x) . u] =
    v . mu^x(u) whenever u in K(G), v in K(X). (4) If u in K(G),
    h in G, u_h(y) = u(h y) for y in G, then mu^x(u_h) = mu^x(u) o A_h.
    (5) For each v in K(X) there exist functions f in K(G)+ with
    spt v subset A^x{g: f(g) > 0}, and this condition implies that
    mu^x[((v / mu^x(f)) o A^x) . f] = v. (6) If nu is a (monotone)
    Daniell integral on K(X), then nu o mu^x is a (monotone) Daniell
    integral on K(G). Moreover, nu is chi covariant if and only if
    nu o mu^x is left chi covariant." Direct formalisation; (1) and
    "mu^x: K(G) -> K(X)" form is_coset_integral, and the isotropy group
    G^x carries the restricted operations mulS, invS, eS. *)
Theorem isotropy_integral_epimorphism :
  exists M : (G -> R) -> X -> R,
  [/\ is_coset_integral mul A x mu M,
    (forall u v, KG u -> KG v -> M (fun g => u g + v g) = (fun y => M u y + M v y)) /\
      (forall c u, KG u -> M (fun g => c * u g) = (fun y => c * M u y)),
    (forall v, KX v -> exists2 u, KG u & M u = v),
    [/\ forall u, KG u -> function_nonnegative u ->
          real_function_support (M u) = orbit_map A x @` real_function_support u,
        forall u v, KG u -> KX v -> M (fun g => v (A g x) * u g) = (fun y => v y * M u y) &
        forall u h, KG u -> M (fun y => u (mul h y)) = M u \o A h] &
    [/\ forall v, KX v -> exists2 f, positive_function_lattice KG f &
          real_function_support v `<=` orbit_map A x @` [set g | 0 < f g],
        forall v f, KX v -> positive_function_lattice KG f ->
          real_function_support v `<=` orbit_map A x @` [set g | 0 < f g] ->
          M (fun g => v (A g x) / M f (A g x) * f g) = v &
        forall nu : (X -> R) -> R,
          [/\ is_daniell_integral KX nu -> is_daniell_integral KG (fun u => nu (M u)),
            is_monotone_daniell_integral KX nu ->
              is_monotone_daniell_integral KG (fun u => nu (M u)) &
            forall chi : G -> R, is_daniell_integral KX nu ->
              (is_covariant_integral A chi nu <->
                is_left_covariant_integral mul chi (fun u => nu (M u)))]]].
Proof.
have [M hM] := coset_integral_exists.
exists M; split=> //.
- split=> [u v hu hv|c u hu]; first exact: (coset_integral_add hG hA hX hmu hM hu hv).
  exact: (coset_integral_scale hG hA hX hmu hM c hu).
- by move=> v hv; exact: (coset_integral_onto hG hA hX hR hmu hM hv).
- split=> [u hu hu0|u v hu hv|u h hu].
  + exact: (coset_integral_support hG hA hX hR hmu hM hu hu0).
  + exact: (coset_integral_multiplier_compact hG hA hX hmu hM hu hv).
  + exact: (coset_integral_translate hG hA hM h hu).
- split=> [v hv|v f hv hf hsub|nu].
  + exact: (coset_integral_cover x hG hA hv).
  + exact: (coset_integral_quotient hG hA hX hR hmu hM hv hf hsub).
  + split=> [hnu|hnu|chi hnu].
    * exact: (coset_integral_daniell hG hA hX hmu hM hnu).
    * exact: (coset_integral_monotone_daniell hG hA hX hmu hM hnu).
    * exact: (coset_integral_covariant hG hA hX hR hmu hM chi hnu).
Qed.

End CosetIntegralExistence.
