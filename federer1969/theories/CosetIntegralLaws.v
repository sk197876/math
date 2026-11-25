(** Federer (1969), 2.7.10, printed pp. 127–128: the properties of the
    linear epimorphism mu^x: K(G) -> K(X) attached to x in X and to a left
    Haar integral mu of the isotropy group G^x. They are derived here from
    the specification is_coset_integral of CosetIntegralUP.v, which consists
    of "mu^x: K(G) -> K(X)" and of (1), "mu^x(u)(g x) = mu_s[u(g s)]
    whenever u in K(G), g in G". The proof of Federer reads "The assertions
    (1), (2), (3), (4) are now easily verified. Regarding (5), we infer the
    existence of suitable functions f from the fact that the sets A^x{g:
    u(g) > 0}, corresponding to u in K(G)+, form a base for the topology of
    X. Moreover, for any such f, we see that spt v subset {y: mu^x(f)(y) >
    0}, hence v = w . mu^x(f) with w in K(X), and (3) implies mu^x[(w o A^x)
    . f] = v. Finally (6) follows from (1), (4), (5)." Each point of X is
    A(g,x) for some g in G, so that identities between functions on X are
    verified at the points A(g,x). For s in G^x one has A(gs,x) = A(g,x),
    which gives (3); associativity gives (4). Two facts about mu are used:
    it is a monotone Daniell integral on K(G^x), hence linear and monotone,
    and it is positive on the nonzero members of K(G^x)+
    (InvariantIntegralPositivity.v, 2.7.6). The positivity gives mu^x(u)(g
    x) > 0 when u in K(G)+ and u(g) > 0, which yields the inclusion spt
    mu^x(u) supset A^x(spt u) in (2) and the inclusion spt v subset {y:
    mu^x(f)(y) > 0} in (5). The functions f of (5) are obtained from cutoff
    functions (2.5.13–2.5.14, pp. 106–108) equal to 1 on a compact set K
    subset G with A^x(K) supset spt v; K is a finite union of compact
    neighbourhoods, since A^x is open. The quotient v / mu^x(f) is the
    pointwise quotient of real numbers, with r/0 = 0; it vanishes off spt v.
    In (6), "nu o mu^x" is the functional u |-> nu(mu^x(u)), and the
    covariance on X refers to the action A, the left covariance on G to the
    action 2.7.2(1). The local erratum has no entry for pp. 127–128. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets functions
  reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground FunctionLatticeUP FunctionLatticeSeminormUP
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws DaniellIntegralUP DaniellIntegralNegation
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportProducts
  DaniellSpaceCompactness ProperMapUP DaniellSpacePushforward CompactFiniteCover CompactCutoffUP
  LocalizedCompactCutoffUP LocalizedCompactCutoff TopologicalGroupUP TopologicalGroupLaws
  HomogeneousSpaceUP HomogeneousSpaceLaws CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP
  GroupMultiplicationHomogeneous InvariantIntegralPositivity InvariantIntegralExistence
  IsotropyGroupTopology CosetIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CosetSections.
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
(** Source for [hTS]: G^x is a topological group, supporting "the
    isotropy group G^x", Federer 2.7.10, p. 127. *)
Let hTS := subgroup_restriction_topological hR hT.
(** Source for [hSc]: "the isotropy subgroup G^x ... is closed in G",
    Federer 2.7.1, pp. 121–122, used in this section. *)
Let hSc : closed S := isotropy_subgroup_closed hA hX.
(** Source for [hmuD]: mu is a monotone Daniell integral on K(G^x),
    part of "left Haar integral", Federer 2.7.2, p. 122. *)
Let hmuD := nonzero_invariant_integral_monotone hmu.
(** Source for [hmuL]: mu is linear on K(G^x), Federer 2.5.13, p. 106,
    applied to the Daniell integral mu. *)
Let hmuL := daniell_compact_support_linear (monotone_daniell_is_daniell hmuD).
(** Source for [hLS]: the lattice laws of K(G^x), Federer 2.5.13,
    p. 106, used in this section. *)
Let hLS : is_function_lattice KS := @compactly_supported_continuous_functions_lattice R S.

(** Source for [isotropy_coset_orbit]: A(gs,x) = A(g,x) whenever
    g in G and s in G^x, by "A(gh,x) = A[g,A(h,x)]" and
    G^x = G cap {g: A(g,x) = x}, Federer 2.7.1, p. 121. Supporting lemma
    for 2.7.10(2),(3), pp. 127–128. *)
Lemma isotropy_coset_orbit g (s : S) : A (mul g (set_val s)) x = A g x.
Proof. by rewrite (homogeneous_action_compatible hA) (set_valP s). Qed.

(** Source for [coset_section_compact]: the function s |-> u(gs) on G^x
    belongs to K(G^x) whenever u in K(G), g in G, as presupposed by
    "mu_s[u(g s)]", Federer 2.7.10, p. 127. It is u o (left
    multiplication by g) composed with the inclusion of the closed set
    G^x, which is a continuous proper map. Supporting lemma. *)
Lemma coset_section_compact u g : KG u -> KS (fun s : S => u (mul g (set_val s))).
Proof.
move=> hu; have hug : KG (u \o mul g).
  exact: (compactly_supported_translate hgl (left_multiplication_homogeneous hT) g hu).
exact: (compactly_supported_compose (@set_type_val_continuous G S) (set_type_val_proper hSc) hug).
Qed.

(** Source for [coset_section_translate]: "w(g t) = w(g) whenever
    t in G^x, because mu is left invariant", Federer 2.7.10, proof,
    p. 128, for w(g) = mu_s[u(g s)]. Supporting lemma. *)
Lemma coset_section_translate u g (t : S) : KG u ->
  mu (fun s : S => u (mul (mul g (set_val t)) (set_val s))) = mu (fun s : S => u (mul g (set_val s))).
Proof.
move=> hu.
have -> : (fun s : S => u (mul (mul g (set_val t)) (set_val s))) =
    (fun s : S => u (mul g (set_val s))) \o left_multiplication_action mulS t.
  by apply: funext=> s; rewrite /= /left_multiplication_action (subgroup_restriction_mul hR)
    (group_mulA hgl).
rewrite (covariant_integral_law (nonzero_invariant_integral_invariant hmu) t
  (coset_section_compact g hu)).
exact: mul1r.
Qed.

(** Source for [coset_section_orbit_eq]: w(g) = w(h) whenever
    A(g,x) = A(h,x), where w(g) = mu_s[u(g s)], from "w(g t) = w(g)
    whenever t in G^x", Federer 2.7.10, proof, p. 128, since then
    h = g t with t = g^{-1} h in G^x. Supporting lemma for "there
    exists a unique continuous map mu^x(u)". *)
Lemma coset_section_orbit_eq u g h : KG u -> A g x = A h x ->
  mu (fun s : S => u (mul g (set_val s))) = mu (fun s : S => u (mul h (set_val s))).
Proof.
move=> hu /(orbit_map_eq hgl hA) hgh.
pose t : S := exist _ (mul (inv g) h) (mem_set hgh).
have -> : h = mul g (set_val t) by rewrite /= (group_mulKVg hgl).
by rewrite coset_section_translate.
Qed.

(** Source for [coset_section_nonnegative]: mu_s[u(g s)] >= 0 for
    u in K(G)+, since mu is monotone, Federer 2.7.10, p. 127, with
    2.5.2, p. 92. Supporting lemma. *)
Lemma coset_section_nonnegative u g : KG u -> function_nonnegative u ->
  0 <= mu (fun s : S => u (mul g (set_val s))).
Proof.
move=> hu hu0; apply: (monotone_daniell_integral_nonnegative hLS hmuD (coset_section_compact g hu)).
by move=> s; exact: hu0.
Qed.

(** Source for [coset_section_positive]: mu_s[u(g s)] > 0 whenever
    u in K(G)+ and u(g) <> 0, supporting (2) and "spt v subset
    {y: mu^x(f)(y) > 0}", Federer 2.7.10, pp. 127–128. The function
    s |-> u(gs) is a member of K(G^x)+ with value u(g) at e, and a left
    Haar integral is positive on the nonzero members of K(G^x)+
    (left_haar_integral_positive). *)
Lemma coset_section_positive u g : KG u -> function_nonnegative u -> u g <> 0 ->
  0 < mu (fun s : S => u (mul g (set_val s))).
Proof.
move=> hu hu0 hug.
apply: (left_haar_integral_positive hTS hmu (coset_section_compact g hu)).
  by move=> s; exact: hu0.
by exists eS; rewrite (subgroup_restriction_unit hR) (group_mulg1 hgl).
Qed.

(** Source for [coset_section_nonzero]: if mu_s[u(g s)] <> 0, then
    u(gs) <> 0 for some s in G^x, since mu vanishes on the zero
    function. Supporting lemma for (2), Federer 2.7.10, p. 127. *)
Lemma coset_section_nonzero u g : KG u -> mu (fun s : S => u (mul g (set_val s))) <> 0 ->
  exists s : S, u (mul g (set_val s)) <> 0.
Proof.
move=> hu hne; apply: contrapT=> hn; apply: hne.
have -> : (fun s : S => u (mul g (set_val s))) = (fun _ => 0).
  by apply: funext=> s; apply: contrapT=> hs; apply: hn; exists s.
exact: (monotone_daniell_integral_zero hmuD (coset_section_compact g hu)).
Qed.

End CosetSections.

Section CosetIntegralLaws.
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
Variable M : (G -> R) -> X -> R.
Hypothesis hM : is_coset_integral mul A x mu M.
Local Notation KG := (@compactly_supported_continuous_functions R G).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KS := (@compactly_supported_continuous_functions R S).

(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121,
    used in this section. *)
Let hT := lch_group_topological hG.
(** Source for [hgl]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hgl := topological_group_laws hT.
(** Source for [hmuD]: mu is a monotone Daniell integral on K(G^x),
    part of "left Haar integral", Federer 2.7.2, p. 122. *)
Let hmuD := nonzero_invariant_integral_monotone hmu.
(** Source for [hmuL]: mu is linear on K(G^x), Federer 2.5.13, p. 106,
    applied to the Daniell integral mu. *)
Let hmuL := daniell_compact_support_linear (monotone_daniell_is_daniell hmuD).
(** Source for [hLG]: the lattice laws of K(G), Federer 2.5.13, p. 106,
    used in this section. *)
Let hLG : is_function_lattice KG := @compactly_supported_continuous_functions_lattice R G.

(** Source for [orbit_function_eq]: two functions on X agree when they
    agree at the points g x = A(g,x), g in G, since "im A^x = X",
    Federer 2.7.1, p. 121. Supporting lemma for 2.7.10, pp. 127–128. *)
Lemma orbit_function_eq (T : Type) (f1 f2 : X -> T) : (forall g, f1 (A g x) = f2 (A g x)) -> f1 = f2.
Proof. by move=> h; apply: funext=> y; have [g <-] := homogeneous_transitive hA x y; exact: h. Qed.

(** Source for [coset_integral_unique]: mu^x is determined on K(G) by
    (1), Federer 2.7.10, p. 127, "corresponds a linear epimorphism
    mu^x", since im A^x = X. Supporting theorem. *)
Theorem coset_integral_unique (M' : (G -> R) -> X -> R) :
  is_coset_integral mul A x mu M' -> forall u, KG u -> M' u = M u.
Proof.
move=> hM' u hu; apply: orbit_function_eq=> g.
by rewrite (coset_integral_value hM' g hu) (coset_integral_value hM g hu).
Qed.

(** Source for [coset_integral_add]: mu^x is additive on K(G), part of
    "linear epimorphism", Federer 2.7.10, p. 127; by (1) and the
    additivity of mu. *)
Theorem coset_integral_add u v : KG u -> KG v -> M (fun g => u g + v g) = (fun y => M u y + M v y).
Proof.
move=> hu hv; apply: orbit_function_eq=> g.
rewrite (coset_integral_value hM g (function_lattice_add hLG hu hv)).
rewrite (coset_integral_value hM g hu) (coset_integral_value hM g hv).
exact: (monotone_daniell_integral_add hmuD (coset_section_compact x hG hA hX g hu)
  (coset_section_compact x hG hA hX g hv)).
Qed.

(** Source for [coset_integral_scale]: mu^x(c u) = c mu^x(u) for every
    real c, part of "linear epimorphism", Federer 2.7.10, p. 127; by
    (1) and the linearity of mu on K(G^x). *)
Theorem coset_integral_scale c u : KG u -> M (fun g => c * u g) = (fun y => c * M u y).
Proof.
move=> hu; apply: orbit_function_eq=> g.
rewrite (coset_integral_value hM g (compactly_supported_scale c hu)) (coset_integral_value hM g hu).
exact: hmuL.2 c _ (coset_section_compact x hG hA hX g hu).
Qed.

(** Source for [coset_integral_le]: mu^x is monotone on K(G),
    supporting "(monotone) Daniell integral" in 2.7.10(6), Federer
    p. 128; by (1) and the monotonicity of mu. *)
Lemma coset_integral_le u v : KG u -> KG v -> function_le u v -> function_le (M u) (M v).
Proof.
move=> hu hv huv y; have [g <-] := homogeneous_transitive hA x y.
rewrite (coset_integral_value hM g hu) (coset_integral_value hM g hv).
apply: (monotone_daniell_integral_monotone hmuD (coset_section_compact x hG hA hX g hu)
  (coset_section_compact x hG hA hX g hv)).
by move=> s; exact: huv.
Qed.

(** Source for [coset_integral_nonnegative]: mu^x maps K(G)+ into
    K(X)+, supporting 2.7.10(2),(5),(6), Federer pp. 127–128. *)
Lemma coset_integral_nonnegative u : KG u -> function_nonnegative u -> function_nonnegative (M u).
Proof.
move=> hu hu0 y; have [g <-] := homogeneous_transitive hA x y.
by rewrite (coset_integral_value hM g hu); exact: (coset_section_nonnegative hG hA hX hmu g hu hu0).
Qed.

(** Source for [coset_integral_increases]: if u_n in K(G) increase
    pointwise to u in K(G), then mu^x(u_n) increase pointwise to
    mu^x(u), by (1) and the fourth condition of 2.5.2, p. 92, for mu;
    supporting "(monotone) Daniell integral" in 2.7.10(6), Federer
    p. 128. *)
Lemma coset_integral_increases (f : nat -> G -> R) u : (forall n, KG (f n)) -> KG u ->
  real_functions_increase_to f u -> real_functions_increase_to (fun n => M (f n)) (M u).
Proof.
move=> hf hu hinc y; have [g <-] := homogeneous_transitive hA x y.
rewrite (coset_integral_value hM g hu).
have -> : (fun n => (M (f n) (A g x))%:E) = (fun n => (mu (fun s : S => f n (mul g (set_val s))))%:E).
  by apply: funext=> n; rewrite (coset_integral_value hM g (hf n)).
apply: (monotone_daniell_integral_increases hmuD (f := fun n (s : S) => f n (mul g (set_val s)))).
- by move=> n; exact: (coset_section_compact x hG hA hX g (hf n)).
- exact: (coset_section_compact x hG hA hX g hu).
- by move=> s; exact: hinc.
Qed.

(** Source for [orbit_support_closed]: A^x(spt u) is compact, hence
    closed in the Hausdorff space X, for u in K(G); supporting
    2.7.10(2), Federer p. 127. *)
Lemma orbit_support_closed u : KG u -> closed (orbit_map A x @` real_function_support u).
Proof.
move=> [_ hK]; apply: (compact_closed hX); apply: continuous_compact=> //.
by apply: continuous_subspaceT; exact: orbit_map_continuous hA x.
Qed.

(** Source for [coset_integral_support_sub]: spt mu^x(u) subset
    A^x(spt u) whenever u in K(G), one inclusion of 2.7.10(2), Federer
    p. 127, which is printed for u in K(G)+. If mu^x(u)(g x) <> 0, then
    u(gs) <> 0 for some s in G^x, and g x = (gs) x. *)
Theorem coset_integral_support_sub u : KG u ->
  real_function_support (M u) `<=` orbit_map A x @` real_function_support u.
Proof.
move=> hu; apply: (real_function_support_in_closed_set (orbit_support_closed hu))=> y hy.
have [g hg] := homogeneous_transitive hA x y; rewrite -hg in hy *.
rewrite (coset_integral_value hM g hu); apply: contrapT=> hne.
have [s hs] := coset_section_nonzero hG hA hX hmu hu hne.
apply: hy; exists (mul g (set_val s)); first exact: subset_closure.
exact: (isotropy_coset_orbit hA g s).
Qed.

(** Source for [coset_integral_support]: "(2) spt mu^x(u) = A^x(spt u)
    whenever u in K(G)+", Federer 2.7.10, p. 127. The inclusion supset
    holds because the closed set (A^x)^{-1}(spt mu^x(u)) contains each g
    with u(g) > 0, by coset_section_positive. Direct formalisation. *)
Theorem coset_integral_support u : KG u -> function_nonnegative u ->
  real_function_support (M u) = orbit_map A x @` real_function_support u.
Proof.
move=> hu hu0; apply/seteqP; split; first exact: coset_integral_support_sub.
have hcl : closed (orbit_map A x @^-1` real_function_support (M u)).
  apply: preimage_closed (@real_function_support_closed R X (M u))=> g _.
  exact: orbit_map_continuous hA x g.
have hsub : real_function_support u `<=` orbit_map A x @^-1` real_function_support (M u).
  rewrite ((closure_id _).1 hcl); apply: (@closureS _ [set g | u g <> 0])=> g hg.
  apply: subset_closure; rewrite /= /orbit_map (coset_integral_value hM g hu).
  by apply/eqP; rewrite gt_eqF // (coset_section_positive hG hA hX hR hmu hu hu0 hg).
by move=> _ [g hg <-]; exact: hsub hg.
Qed.

(** Source for [coset_integral_multiplier]: "(3) mu^x[(v o A^x) . u]
    = v . mu^x(u) whenever u in K(G), v in K(X)", Federer 2.7.10,
    p. 127, for every continuous real function v on X. Generalisation:
    the compactness of spt v is not used. *)
Theorem coset_integral_multiplier u (v : X -> R) : KG u -> continuous (v : X -> real_line_metric R) ->
  M (fun g => v (A g x) * u g) = (fun y => v y * M u y).
Proof.
move=> hu hv.
have hvA : continuous ((fun g => v (A g x)) : G -> real_line_metric R).
  move=> g; apply: (@continuous_comp G X (real_line_metric R) (orbit_map A x) v g).
    exact: orbit_map_continuous hA x g.
  exact: hv.
have hvu : KG (fun g => v (A g x) * u g) := compact_support_continuous_multiplier hvA hu.
apply: orbit_function_eq=> g.
rewrite (coset_integral_value hM g hvu) (coset_integral_value hM g hu).
have -> : (fun s : S => v (A (mul g (set_val s)) x) * u (mul g (set_val s))) =
    (fun s : S => v (A g x) * u (mul g (set_val s))).
  by apply: funext=> s; rewrite (isotropy_coset_orbit hA g s).
exact: hmuL.2 _ _ (coset_section_compact x hG hA hX g hu).
Qed.

(** Source for [coset_integral_multiplier_compact]: "(3)
    mu^x[(v o A^x) . u] = v . mu^x(u) whenever u in K(G), v in K(X)",
    Federer 2.7.10, p. 127. Direct formalisation. *)
Corollary coset_integral_multiplier_compact u v : KG u -> KX v ->
  M (fun g => v (A g x) * u g) = (fun y => v y * M u y).
Proof. by move=> hu hv; exact: coset_integral_multiplier hu hv.1. Qed.

(** Source for [coset_integral_translate]: "(4) If u in K(G), h in G,
    u_h(y) = u(h y) for y in G, then mu^x(u_h) = mu^x(u) o A_h",
    Federer 2.7.10, p. 127. By (1) and associativity. Direct
    formalisation. *)
Theorem coset_integral_translate u h : KG u -> M (fun y => u (mul h y)) = M u \o A h.
Proof.
move=> hu.
have huh : KG (fun y => u (mul h y)).
  exact: (compactly_supported_translate hgl (left_multiplication_homogeneous hT) h hu).
apply: orbit_function_eq=> g; rewrite /= (coset_integral_value hM g huh).
rewrite -(homogeneous_action_compatible hA) (coset_integral_value hM (mul h g) hu).
by congr mu; apply: funext=> s; rewrite (group_mulA hgl).
Qed.

(** Source for [coset_integral_cover]: "(5) For each v in K(X) there
    exist functions f in K(G)+ with spt v subset A^x{g: f(g) > 0}",
    Federer 2.7.10, p. 127. Federer infers this from the fact that the
    sets A^x{g: u(g) > 0}, u in K(G)+, form a base of X. Here the open
    sets A^x(Int N_g), for compact neighbourhoods N_g of the points g of
    G, cover the compact set spt v; finitely many of them suffice, and
    f is a cutoff function equal to 1 on the union K of the
    corresponding N_g (2.5.13–2.5.14, pp. 106–108). *)
Theorem coset_integral_cover v : KX v ->
  exists2 f, positive_function_lattice KG f & real_function_support v `<=` orbit_map A x @` [set g | 0 < f g].
Proof.
move=> [_ hvK].
have hl := lch_group_locally_compact hG; have hH := lch_group_hausdorff hG.
have /choice [N hN] : forall g : G, exists N : set G, nbhs g N /\ compact N.
  by move=> g; have [N hN [hNc _]] := hl g I; rewrite withinET in hN; exists N.
pose O g := orbit_map A x @` (N g)°.
have hO g : open (O g) := homogeneous_orbit_open hA x (@open_interior _ (N g)).
have hcov : real_function_support v `<=` \bigcup_(g in [set: G]) O g.
  move=> y _; have [g hg] := homogeneous_transitive hA x y.
  by exists g=> //; exists g=> //; exact: nbhs_singleton (nbhs_interior (hN g).1).
have [D _ hD] := compact_open_finite_cover hvK (fun g _ => hO g) hcov.
pose K := \bigcup_(g in [set g | g \in D]) N g.
have hK : compact K by rewrite /K bigcup_fset; apply: bigsetU_compact=> g _; exact: (hN g).2.
have hKV : K `<=` [set: G] by [].
pose f := localized_compact_cutoff R hH hl hK openT hKV.
have [[hfK hf01 hf1] _] := localized_compact_cutoff_specification R hH hl hK openT hKV.
exists f; first by split=> // g; have /andP [] := hf01 g.
move=> y hy; have [g hgD [k hk <-]] := hD y hy.
have hKk : K k by exists g=> //; exact: interior_subset hk.
by exists k=> //=; rewrite /f (hf1 k hKk); exact: ltr01.
Qed.

(** Source for [coset_integral_quotient_compact]: "spt v subset
    {y: mu^x(f)(y) > 0}, hence v = w . mu^x(f) with w in K(X)", Federer
    2.7.10, proof, p. 128: the quotient w = v / mu^x(f) belongs to
    K(X). Supporting lemma. *)
Lemma coset_integral_quotient_compact v f : KX v -> positive_function_lattice KG f ->
  real_function_support v `<=` orbit_map A x @` [set g | 0 < f g] ->
  real_function_support v `<=` [set y | 0 < M f y] /\ KX (fun y => v y / M f y).
Proof.
move=> hv [hf hf0] hsub.
have hMf := coset_integral_compact hM hf.
have hpos : real_function_support v `<=` [set y | 0 < M f y].
  move=> y hy; have [g hg <-] := hsub y hy; rewrite /= /orbit_map (coset_integral_value hM g hf).
  by apply: (coset_section_positive hG hA hX hR hmu hf hf0); apply/eqP; rewrite gt_eqF.
have hU : open [set y | 0 < M f y] := (continuousP _).1 hMf.1 _ (@open_gt R 0).
split=> //; apply: (compactly_supported_quotient hv hMf.1 hU hpos)=> y hy.
by rewrite gt_eqF.
Qed.

(** Source for [coset_integral_quotient]: "(5) ... and this condition
    implies that mu^x[((v / mu^x(f)) o A^x) . f] = v", Federer 2.7.10,
    p. 127, with the proof "(3) implies mu^x[(w o A^x) . f] = v",
    p. 128. The quotient is pointwise, with r/0 = 0. Direct
    formalisation. *)
Theorem coset_integral_quotient v f : KX v -> positive_function_lattice KG f ->
  real_function_support v `<=` orbit_map A x @` [set g | 0 < f g] ->
  M (fun g => v (A g x) / M f (A g x) * f g) = v.
Proof.
move=> hv hf hsub; have [hpos [hqc _]] := coset_integral_quotient_compact hv hf hsub.
have [hfK _] := hf.
have -> := coset_integral_multiplier (v := fun y => v y / M f y) hfK hqc.
apply: funext=> y; case: (pselect (real_function_support v y))=> hy.
- by rewrite divfK // gt_eqF //; exact: hpos.
- by rewrite (real_function_zero_off_support hy) !mul0r.
Qed.

(** Source for [coset_integral_onto]: "im mu^x = K(X)", the
    surjectivity in "linear epimorphism", Federer 2.7.10, p. 127, used
    in 2.7.11, p. 128; it follows from (5). Direct formalisation. *)
Theorem coset_integral_onto v : KX v -> exists2 u, KG u & M u = v.
Proof.
move=> hv; have [f hf hsub] := coset_integral_cover hv.
have [_ [hqc _]] := coset_integral_quotient_compact hv hf hsub.
have [hfK _] := hf.
exists (fun g => v (A g x) / M f (A g x) * f g); last exact: coset_integral_quotient.
apply: compact_support_continuous_multiplier hfK=> g.
apply: (@continuous_comp G X (real_line_metric R) (orbit_map A x) (fun y => v y / M f y) g).
  exact: orbit_map_continuous hA x g.
exact: hqc.
Qed.

(** Source for [coset_integral_monotone_daniell]: "(6) If nu is a
    monotone Daniell integral on K(X), then nu o mu^x is a monotone
    Daniell integral on K(G)", Federer 2.7.10, p. 128. By the linearity,
    the monotonicity and coset_integral_increases. Direct
    formalisation. *)
Theorem coset_integral_monotone_daniell (nu : (X -> R) -> R) :
  is_monotone_daniell_integral KX nu -> is_monotone_daniell_integral KG (fun u => nu (M u)).
Proof.
move=> hnu; constructor.
- move=> u v hu hv; rewrite /= (coset_integral_add hu hv).
  exact: (monotone_daniell_integral_add hnu (coset_integral_compact hM hu) (coset_integral_compact hM hv)).
- move=> c u hc hu; rewrite /= (coset_integral_scale c hu).
  exact: (monotone_daniell_integral_scale hnu hc (coset_integral_compact hM hu)).
- move=> u v hu hv huv.
  exact: (monotone_daniell_integral_monotone hnu (coset_integral_compact hM hu)
    (coset_integral_compact hM hv) (coset_integral_le hu hv huv)).
- move=> f u hf hu hinc.
  apply: (monotone_daniell_integral_increases hnu (f := fun n => M (f n))).
  + by move=> n; exact: (coset_integral_compact hM (hf n)).
  + exact: (coset_integral_compact hM hu).
  + exact: coset_integral_increases.
Qed.

(** Source for [coset_integral_daniell]: "(6) If nu is a ... Daniell
    integral on K(X), then nu o mu^x is a ... Daniell integral on
    K(G)", Federer 2.7.10, p. 128, for the Daniell integrals of 2.5.5,
    p. 96. The bound of nu on {k: 0 <= k <= mu^x(f)} bounds nu o mu^x on
    {k: 0 <= k <= f}. Direct formalisation. *)
Theorem coset_integral_daniell (nu : (X -> R) -> R) :
  is_daniell_integral KX nu -> is_daniell_integral KG (fun u => nu (M u)).
Proof.
move=> hnu; constructor.
- move=> u v hu hv; rewrite /= (coset_integral_add hu hv).
  exact: (daniell_integral_add hnu (coset_integral_compact hM hu) (coset_integral_compact hM hv)).
- move=> c u hc hu; rewrite /= (coset_integral_scale c hu).
  exact: (daniell_integral_scale hnu hc (coset_integral_compact hM hu)).
- move=> f hf; have [b hb] := daniell_integral_order_bounded hnu (coset_integral_compact hM hf).
  exists b=> k [hk [hk0 hkf]]; apply: hb; split; first exact: (coset_integral_compact hM hk).
  by split; [exact: coset_integral_nonnegative|exact: coset_integral_le].
- move=> f u hf hu hinc.
  apply: (daniell_integral_increasing_continuity hnu (f := fun n => M (f n))).
  + by move=> n; exact: (coset_integral_compact hM (hf n)).
  + exact: (coset_integral_compact hM hu).
  + exact: coset_integral_increases.
Qed.

(** Source for [coset_integral_covariant]: "(6) ... Moreover, nu is
    chi covariant if and only if nu o mu^x is left chi covariant",
    Federer 2.7.10, p. 128, for a Daniell integral nu on K(X). The
    direct implication uses (4); the converse uses (4) and the
    surjectivity of mu^x, which follows from (5). Direct formalisation. *)
Theorem coset_integral_covariant (nu : (X -> R) -> R) (chi : G -> R) :
  is_daniell_integral KX nu ->
  (is_covariant_integral A chi nu <-> is_left_covariant_integral mul chi (fun u => nu (M u))).
Proof.
move=> hnu; split.
- move=> hc; split; first exact: coset_integral_daniell.
  move=> u g hu; rewrite /= /left_multiplication_action.
  have -> : M (u \o mul g) = M u \o A g := coset_integral_translate g hu.
  exact: (covariant_integral_law hc g (coset_integral_compact hM hu)).
- move=> [_ hc]; split=> // v g hv.
  have [u hu <-] := coset_integral_onto hv.
  rewrite -(coset_integral_translate g hu); exact: hc u g hu.
Qed.

End CosetIntegralLaws.
