(** Federer (1969), 2.7.12, printed p. 129: "Weil's condition holds whenever
    chi is positive and the isotropy group G^x is compact, because every
    continuous homomorphism of a compact group into the multiplicative group
    of positive numbers is constant with value 1. In this case the map A^x
    is proper. If lambda is a left chi covariant integral of G, then
    A^x_#(lambda) is a chi covariant integral on K(X), which equals the
    function nu constructed in 2.7.11 provided mu is chosen so that mu(1) =
    1, because [A^x_#(lambda) o mu^x] u = lambda[mu^x(u) o A^x] =
    lambda_g[mu_s u(g s)] = mu_s[lambda_g u(g s)] = mu_s[lambda(u)] =
    lambda(u) whenever u in K(G)." Standing hypotheses of 2.7.1, p. 121: G
    is a locally compact Hausdorff topological group and X a locally compact
    Hausdorff homogeneous space of G; the isotropy group G^x is compact as a
    subset of G. Weil's condition is that of WeilCondition.v; it is obtained
    by applying compact_group_positive_character_unit
    (CompactGroupCharacters.v) to t |-> chi(t) Delta_{G^x}(t)
    Delta_G(t)^{-1} on the compact group G^x. Federer gives no argument for
    the properness of A^x: a compact set C of X lies in A^x(K) for a compact
    K of G, because A^x is open and onto and G is locally compact, so that
    (A^x)^{-1}(C) is a closed subset of the compact set K G^x. A^x_#(lambda)
    is the Daniell pushforward of 2.5.19, p. 113 (daniell_pushforward), v
    |-> lambda(v o A^x). In the displayed computation, the third equation is
    Fubini's theorem for Daniell integrals on K(G x G^x) (2.6.4, 2.6.6, pp.
    119–120), and the fourth uses that lambda is right Delta_G chi^{-1}
    covariant (2.7.9(3)) and that Delta_G(t) chi(t)^{-1} = Delta_{G^x}(t) =
    1 for t in G^x, by Weil's condition and the unimodularity of the compact
    group G^x; the last equation is mu_s[lambda(u)] = mu(1) lambda(u). The
    computation is proved for every left Haar integral mu of G^x, with the
    factor mu(1) in place of the normalisation mu(1) = 1. "Equals the
    function nu constructed in 2.7.11" is formalised as A^x_#(lambda) = nu
    on K(X) for every nu with nu o mu^x = lambda on K(G), since nu is
    determined by this condition and im mu^x = K(X). The local erratum has
    no entry for p. 129. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets functions
  reals constructive_ereal topology normedtype.
From mathcomp Require Import ring.
From Federer Require Import RealMetricBackground TopologicalProductMaps ProperMapUP
  FunctionLatticeUP DaniellIntegralUP MonotoneDaniellIntegralUP DaniellIntegralNegation
  CompactSupportFunctionUP DaniellSpaceCompactness DaniellSpacePushforward CompactFiniteCover
  TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP HomogeneousSpaceLaws
  CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP GroupMultiplicationHomogeneous
  ModularFunctionUP ModularFunction CovariantHaarCharacterisation SubtypeCompactHausdorff
  IsotropyGroupTopology CosetIntegralUP CosetIntegralLaws CompactDaniellIterationCommutation
  CovariantIntegralFactorisation WeilCondition CompactGroupCharacters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactIsotropy.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (x : X).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hX : hausdorff_space X.
Local Notation S := (isotropy_subgroup A x).
Hypothesis hSc : compact S.
Local Notation KG := (@compactly_supported_continuous_functions R G).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KS := (@compactly_supported_continuous_functions R S).

(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121,
    used in this section. *)
Let hT := lch_group_topological hG.
(** Source for [hgl]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hgl := topological_group_laws hT.
(** Source for [hH]: G is Hausdorff, Federer 2.7.1, p. 121. *)
Let hH := lch_group_hausdorff hG.
(** Source for [hlG]: G is locally compact, Federer 2.7.1, p. 121. *)
Let hlG := lch_group_locally_compact hG.
(** Source for [hScl]: G^x is closed in G, Federer 2.7.1, pp. 121–122,
    since X is Hausdorff. *)
Let hScl : closed S := isotropy_subgroup_closed hA hX.
(** Source for [hSall]: the compact isotropy group G^x of Federer
    2.7.12, p. 129, is a compact space in its relative topology. *)
Let hSall : compact [set: S] := set_type_compact_whole hSc.

(** Source for [compact_isotropy_weil_condition]: "Weil's condition
    holds whenever chi is positive and the isotropy group G^x is
    compact, because every continuous homomorphism of a compact group
    into the multiplicative group of positive numbers is constant with
    value 1", Federer 2.7.12, p. 129. Direct formalisation, applied to
    t |-> chi(t) Delta_{G^x}(t) / Delta_G(t) on G^x. *)
Theorem compact_isotropy_weil_condition (mulS : S -> S -> S) (invS : S -> S) (eS : S)
    (DG : G -> R) (DS : S -> R) (chi : G -> R) :
  is_subgroup_restriction mul inv e S mulS invS eS ->
  is_modular_function mul inv DG -> is_modular_function mulS invS DS ->
  (forall g h, chi (mul g h) = chi g * chi h) -> continuous (chi : G -> real_line_metric R) ->
  (forall g, 0 < chi g) -> weil_condition chi DG DS.
Proof.
move=> hR hDG hDS hchiM hchic hchip.
have hSG := subgroup_restriction_locally_compact_hausdorff hR hG hScl.
have hSgl := topological_group_laws (lch_group_topological hSG).
have [hDSM _] := modular_function_homomorphism hSG hDS.
have [hDGM _] := modular_function_homomorphism hG hDG.
have hv := @set_type_val_continuous G S.
have hDGp := modular_function_positive hDG.
pose phi (t : S) := chi (set_val t) * DS t / DG (set_val t).
have hphic : continuous (phi : S -> real_line_metric R).
  move=> t; apply: (@continuousM R S).
    apply: (@continuousM R S); first exact: continuous_comp (hv t) (hchic _).
    exact: (modular_function_continuous hDS).
  apply: (@continuousV R S (fun s => DG (set_val s)) t); first by rewrite gt_eqF.
  by apply: continuous_comp; [exact: hv|exact: (modular_function_continuous hDG)].
have hphiM a b : phi (mulS a b) = phi a * phi b.
  rewrite /phi (subgroup_restriction_mul hR) hchiM hDSM hDGM invfM; ring.
have hphip t : 0 < phi t.
  by rewrite /phi divr_gt0 // mulr_gt0 //; exact: (modular_function_positive hDS).
have h1 := compact_group_positive_character_unit hSgl hphic hphiM hphip hSall.
move=> t; have := h1 t; rewrite /phi=> h.
have hD0 : DG (set_val t) != 0 := lt0r_neq0 (hDGp _).
by apply: (mulIf (invr_neq0 hD0)); rewrite h (mulfV hD0).
Qed.

(** Source for [compact_isotropy_orbit_proper]: "In this case the map
    A^x is proper", Federer 2.7.12, p. 129, when G^x is compact. Direct
    formalisation; Federer gives no proof. A compact set C of X is
    covered by finitely many of the open sets A^x(Int N_g), N_g a
    compact neighbourhood of g in G, so that C subset A^x(K) for a
    compact K, and (A^x)^{-1}(C) is a closed subset of the compact set
    K G^x. *)
Theorem compact_isotropy_orbit_proper : is_proper_map (orbit_map A x).
Proof.
move=> C hC; have hl : locally_compact [set: G] := hlG.
have /choice [N hN] : forall g : G, exists N : set G, nbhs g N /\ compact N.
  by move=> g; have [N hN [hNc _]] := hl g I; rewrite withinET in hN; exists N.
pose O g := orbit_map A x @` (N g)°.
have hO g : open (O g) := homogeneous_orbit_open hA x (@open_interior _ (N g)).
have hcov : C `<=` \bigcup_(g in [set: G]) O g.
  move=> y _; have [g hg] := homogeneous_transitive hA x y.
  by exists g=> //; exists g=> //; exact: nbhs_singleton (nbhs_interior (hN g).1).
have [Fs _ hFs] := compact_open_finite_cover hC (fun g _ => hO g) hcov.
pose K := \bigcup_(g in [set g | g \in Fs]) N g.
have hK : compact K by rewrite /K bigcup_fset; apply: bigsetU_compact=> g _; exact: (hN g).2.
have hKS : compact [set mul p.1 p.2 | p in K `*` S].
  apply: continuous_compact; last exact: compact_setX hK hSc.
  by apply: continuous_subspaceT; exact: (topological_group_mul_continuous hT).
apply: (subclosed_compact _ hKS).
  apply: preimage_closed (compact_closed hX hC)=> g _.
  exact: orbit_map_continuous hA x g.
move=> g hg; have [j hj [k hk hkg]] := hFs _ hg.
exists (k, mul (inv k) g); last by rewrite /= (group_mulKVg hgl).
split; first by exists j=> //; exact: interior_subset hk.
exact: (orbit_map_eq hgl hA x k g).1 hkg.
Qed.

(** Source for [orbit_pushforward_covariant_integral]: "If lambda is
    a left chi covariant integral of G, then A^x_#(lambda) is a chi
    covariant integral on K(X)", Federer 2.7.12, p. 129, for a proper
    map A^x. Supporting theorem: A^x_#(lambda) is a Daniell integral by
    2.5.19, p. 113, and (v o A_g) o A^x = (v o A^x) o (left
    multiplication by g) by A(g h, x) = A[g, A(h, x)]. *)
Theorem orbit_pushforward_covariant_integral (chi : G -> R) (lambda : (G -> R) -> R) :
  is_proper_map (orbit_map A x) -> is_left_covariant_integral mul chi lambda ->
  is_covariant_integral A chi (daniell_pushforward (orbit_map A x) lambda).
Proof.
move=> hp [hlD hlc]; split.
  exact: (daniell_pushforward_daniell (orbit_map_continuous hA x) hp hlD).
move=> v g hv; rewrite /daniell_pushforward.
have hvo := compactly_supported_compose (orbit_map_continuous hA x) hp hv.
have -> : (v \o A g) \o orbit_map A x = (v \o orbit_map A x) \o left_multiplication_action mul g.
  apply: funext=> h.
  by rewrite /= /orbit_map /left_multiplication_action (homogeneous_action_compatible hA).
exact: hlc _ g hvo.
Qed.

(** Source for [compact_isotropy_pushforward_covariant]: "In this case
    the map A^x is proper. If lambda is a left chi covariant integral
    of G, then A^x_#(lambda) is a chi covariant integral on K(X)",
    Federer 2.7.12, p. 129. Direct formalisation. *)
Theorem compact_isotropy_pushforward_covariant (chi : G -> R) (lambda : (G -> R) -> R) :
  is_left_covariant_integral mul chi lambda ->
  is_covariant_integral A chi (daniell_pushforward (orbit_map A x) lambda).
Proof. exact: orbit_pushforward_covariant_integral compact_isotropy_orbit_proper. Qed.

Section CosetIdentity.
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hR : is_subgroup_restriction mul inv e S mulS invS eS.
Variable mu : (S -> R) -> R.
Hypothesis hmu : is_left_haar_integral mulS mu.
Variable M : (G -> R) -> X -> R.
Hypothesis hM : is_coset_integral mul A x mu M.
Variable chi : G -> R.
Hypothesis hchiM : forall g h, chi (mul g h) = chi g * chi h.
Hypothesis hchic : continuous (chi : G -> real_line_metric R).
Hypothesis hchip : forall g, 0 < chi g.
Variable lambda : (G -> R) -> R.
Hypothesis hlc : is_left_covariant_integral mul chi lambda.

(** Source for [hSG]: the compact isotropy group G^x is a locally
    compact Hausdorff topological group, Federer 2.7.10, p. 127. *)
Let hSG := subgroup_restriction_locally_compact_hausdorff hR hG hScl.
(** Source for [hmuD]: mu is a Daniell integral on K(G^x), part of
    "left Haar integral", Federer 2.7.2, p. 122. *)
Let hmuD := monotone_daniell_is_daniell (nonzero_invariant_integral_monotone hmu).
(** Source for [hmuL]: mu is linear on K(G^x), Federer 2.5.13,
    p. 106. *)
Let hmuL := daniell_compact_support_linear hmuD.
(** Source for [hlD]: lambda is a Daniell integral on K(G), part of
    "left chi covariant integral", Federer 2.7.1–2.7.2, p. 122. *)
Let hlD := covariant_integral_daniell hlc.
(** Source for [hchi0]: chi does not vanish, since it is positive,
    Federer 2.7.12, p. 129. *)
Let hchi0 g : chi g != 0 := lt0r_neq0 (hchip g).

(** Source for [isotropy_unit_function_compact]: the function 1 on
    the compact group G^x belongs to K(G^x), as presupposed by
    "mu(1) = 1", Federer 2.7.12, p. 129. Supporting lemma. *)
Lemma isotropy_unit_function_compact : KS (fun _ => 1).
Proof.
split; first exact: cst_continuous.
exact: subclosed_compact (@real_function_support_closed R S _) hSall (@subsetT _ _).
Qed.

(** Source for [compact_isotropy_section_invariant]: "mu_s[lambda_g
    u(g s)] = mu_s[lambda(u)]", Federer 2.7.12, p. 129:
    lambda_g u(g s) = lambda(u) whenever u in K(G), s in G^x. Supporting
    lemma; lambda is right Delta_G chi^{-1} covariant by 2.7.9(3), and
    Delta_G(t) chi(t)^{-1} = 1 for t in G^x by Weil's condition and the
    unimodularity of the compact group G^x. *)
Lemma compact_isotropy_section_invariant u (s : S) : KG u ->
  lambda (fun g => u (mul g (set_val s))) = lambda u.
Proof.
move=> hu.
have [DG hDG] := modular_function_exists R hG.
have [DS hDS] := modular_function_exists R hSG.
have hW := compact_isotropy_weil_condition hR hDG hDS hchiM hchic hchip.
have [hDSM _] := modular_function_homomorphism hSG hDS.
have hDS1 := compact_group_positive_character_unit (topological_group_laws (lch_group_topological hSG))
  (modular_function_continuous hDS) hDSM (modular_function_positive hDS) hSall.
have hlr := left_covariant_right_modular hG hlD hchiM hchi0 hchic hDG hlc.
have e1 : (fun g => u (mul g (set_val s))) = u \o right_multiplication_action mul inv (inv (set_val s)).
  by apply: funext=> g; rewrite /= /right_multiplication_action (group_invK hgl).
rewrite e1 (covariant_integral_law hlr _ hu) /= -(subgroup_restriction_inv hR).
by rewrite -(hW (invS s)) hDS1 mulr1 (mulfV (hchi0 _)) mul1r.
Qed.

(** Source for [compact_isotropy_coset_product_compact]: the function
    (g,s) |-> u(g s) belongs to K(G x G^x) for u in K(G), as presupposed
    by "lambda_g[mu_s u(g s)] = mu_s[lambda_g u(g s)]", Federer 2.7.12,
    p. 129. Supporting lemma: the function vanishes unless g lies in
    the compact set spt(u) G^x and s in G^x. *)
Lemma compact_isotropy_coset_product_compact u : KG u ->
  @compactly_supported_continuous_functions R (G * S)%type
    (fun p : G * S => u (mul p.1 (set_val p.2))).
Proof.
move=> hu.
have hic : continuous inv := topological_group_inv_continuous hT.
have hdr : continuous (fun p : G * G => mul p.1 (inv p.2)).
  have -> : (fun p : G * G => mul p.1 (inv p.2)) =
      (fun r : G * G => mul r.1 r.2) \o (fun p : G * G => (p.1, inv p.2)) by [].
  move=> p; apply: continuous_comp; last exact: (topological_group_mul_continuous hT).
  apply: topological_pair_continuous; first exact: first_projection_continuous.
  move=> q; apply: continuous_comp; first exact: second_projection_continuous.
  exact: hic.
pose C := [set mul p.1 (inv p.2) | p in real_function_support u `*` S] `|` S.
have hC : compact C.
  apply: compactU hSc; apply: continuous_compact; last exact: compact_setX hu.2 hSc.
  by apply: continuous_subspaceT.
apply: (subgroup_product_compactly_supported hH hScl _ hC).
  have hq : continuous (fun q : G * S => mul q.1 (set_val q.2)).
    have -> : (fun q : G * S => mul q.1 (set_val q.2)) =
        (fun r : G * G => mul r.1 r.2) \o (fun q : G * S => (q.1, set_val q.2)) by [].
    move=> q; apply: continuous_comp; last exact: (topological_group_mul_continuous hT).
    apply: topological_pair_continuous; first exact: first_projection_continuous.
    move=> r; apply: continuous_comp; first exact: second_projection_continuous.
    exact: set_type_val_continuous.
  by move=> p; apply: continuous_comp; [exact: hq|exact: hu.1].
move=> g s hn; split; last by right; exact: set_valP s.
left; exists (mul g (set_val s), set_val s); last by rewrite /= (group_mulgK hgl).
by split; [exact: subset_closure hn|exact: set_valP s].
Qed.

(** Source for [compact_isotropy_pushforward_coset_scaled]: the
    computation "[A^x_#(lambda) o mu^x] u = lambda[mu^x(u) o A^x]
    = lambda_g[mu_s u(g s)] = mu_s[lambda_g u(g s)] = mu_s[lambda(u)]",
    Federer 2.7.12, p. 129, for every left Haar integral mu of the
    compact group G^x: [A^x_#(lambda) o mu^x] u = mu(1) lambda(u)
    whenever u in K(G). Generalisation of the printed identity, which
    is the case mu(1) = 1. *)
Theorem compact_isotropy_pushforward_coset_scaled u : KG u ->
  daniell_pushforward (orbit_map A x) lambda (M u) = mu (fun _ => 1) * lambda u.
Proof.
move=> hu; rewrite /daniell_pushforward.
have hfun : M u \o orbit_map A x =
    (fun g => mu (fun s : S => (fun p : G * S => u (mul p.1 (set_val p.2))) (g, s))).
  by apply: funext=> g; rewrite /= /orbit_map (coset_integral_value hM g hu).
rewrite hfun -(compact_daniell_iterations_commute hH hlG (lch_group_hausdorff hSG)
  (lch_group_locally_compact hSG) hlD hmuD (compact_isotropy_coset_product_compact hu)).
have -> : (fun s : S => lambda (fun g => (fun p : G * S => u (mul p.1 (set_val p.2))) (g, s))) =
    (fun s : S => lambda u * 1).
  by apply: funext=> s; rewrite /= compact_isotropy_section_invariant // mulr1.
by rewrite (hmuL.2 (lambda u) _ isotropy_unit_function_compact) mulrC.
Qed.

(** Source for [compact_isotropy_pushforward_coset]: "provided mu is
    chosen so that mu(1) = 1, because [A^x_#(lambda) o mu^x] u = ...
    = lambda(u) whenever u in K(G)", Federer 2.7.12, p. 129. Direct
    formalisation. *)
Theorem compact_isotropy_pushforward_coset u : mu (fun _ => 1) = 1 -> KG u ->
  daniell_pushforward (orbit_map A x) lambda (M u) = lambda u.
Proof. by move=> h1 hu; rewrite compact_isotropy_pushforward_coset_scaled // h1 mul1r. Qed.

(** Source for [compact_isotropy_pushforward_factor]: "A^x_#(lambda)
    ... equals the function nu constructed in 2.7.11 provided mu is
    chosen so that mu(1) = 1", Federer 2.7.12, p. 129: if
    nu o mu^x = lambda on K(G), then A^x_#(lambda) = nu on K(X). Direct
    formalisation, by im mu^x = K(X). *)
Theorem compact_isotropy_pushforward_factor (nu : (X -> R) -> R) :
  mu (fun _ => 1) = 1 -> (forall u, KG u -> nu (M u) = lambda u) ->
  forall v, KX v -> daniell_pushforward (orbit_map A x) lambda v = nu v.
Proof.
move=> h1 hfac v hv; have [u hu <-] := coset_integral_onto hG hA hX hR hmu hM hv.
by rewrite hfac // compact_isotropy_pushforward_coset.
Qed.

End CosetIdentity.

End CompactIsotropy.
