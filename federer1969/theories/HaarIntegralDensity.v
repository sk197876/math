(** Federer (1969), 2.7.6, printed p. 125: "Lemma. If lambda is a left Haar
    integral and mu is a right Haar integral, then there exists a continuous
    positive real valued function k on G such that (1) k(y) mu(v) = lambda_x
    v(y x^{-1}) whenever y in G, v in K(G), (2) mu(k u) = lambda(u) whenever
    u in K(G)." Here G is a locally compact Hausdorff topological group
    (is_locally_compact_hausdorff_group), K(G) is
    compactly_supported_continuous_functions, lambda_x v(y x^{-1}) is lambda
    applied to x |-> v(y x^{-1}), and k u is the pointwise product. The
    existence of Haar integrals (2.7.5) is not used: lambda and mu are
    hypotheses. Federer's computation lambda(u) mu(v) = mu_y lambda_x[u(x)
    v(y)] = mu_y lambda_x[u(y x) v(y)] = lambda_x mu_y[u(y x) v(y)] =
    lambda_x mu_y[u(y) v(y x^{-1})] = mu_y[u(y) lambda_x v(y x^{-1})] is
    haar_fubini_identity. The two applications of "Fubini's theorem" are
    compact_daniell_iterations_commute (2.6.4, p. 119, and 2.6.6, p. 120)
    for the functions (x,y) |-> u(y x) v(y) and (x,y) |-> u(y) v(y x^{-1}),
    which belong to K(G x G) because they are compositions of (z,y) |-> u(z)
    v(y) and (z,y) |-> v(z) u(y) with the homeomorphisms (x,y) |-> (y x, y)
    and (x,y) |-> (y x^{-1}, y) of G x G. The second and fourth equations
    use the invariance of lambda and mu. The function y |-> lambda_x v(y
    x^{-1}) is continuous: near a point b it equals y |-> lambda_x[w(y) v(y
    x^{-1})], where w in K(G) is a cutoff function equal to 1 on a compact
    neighbourhood of b (2.5.13, p. 106), and the continuity of the latter
    follows from the 2.6.4 argument (compact_section_functional_continuous).
    Federer's claims "k is uniquely characterized by (2), hence does not
    really depend on the choice of v. It follows that (1) holds for all v in
    K(G)" use the positivity of Haar integrals of
    InvariantIntegralPositivity.v. The particular nonzero v in K(G)+ chosen
    to define k is a cutoff function v_0 with v_0(e) = 1; then mu(v_0) > 0
    and lambda_x v_0(y x^{-1}) > 0, whence k > 0. The local erratum has no
    entry for p. 125. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground TopologicalProductMaps HomeomorphismUP
  TopologicalGroupUP TopologicalGroupLaws FunctionLatticeUP CompactSupportFunctionUP
  CompactSupportProducts CompactSeparatedProduct DaniellSpaceCompactness DaniellSpacePushforward
  CompactSectionFunctional CompactDaniellIterationCommutation CompactCutoff CovariantIntegralUP
  CovariantIntegralLaws HaarIntegralUP GroupMultiplicationHomogeneous EquivariantPushforward
  InvariantIntegralPositivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section HaarShear.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hT : is_topological_group mul inv e.
Local Notation K := (@compactly_supported_continuous_functions R G).
Local Notation K2 := (@compactly_supported_continuous_functions R (G * G)%type).
(** Source for [hG]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hG := topological_group_laws hT.

(** Source for [left_shear_homeomorphism]: the map
    (x,y) |-> (y x, y) of G x G is a homeomorphism with inverse
    (z,y) |-> (y^{-1} z, y). Supporting lemma for the substitution
    u(x) v(y) -> u(y x) v(y) under Fubini's theorem in Federer 2.7.6,
    p. 125. *)
Lemma left_shear_homeomorphism :
  is_homeomorphism_with_inverse (fun p : G * G => (mul p.2 p.1, p.2))
    (fun p : G * G => (mul (inv p.2) p.1, p.2)).
Proof.
have hm : continuous (fun p : G * G => mul p.1 p.2) := topological_group_mul_continuous hT.
have hd : continuous (fun p : G * G => mul (inv p.1) p.2) := division_continuous hT.
have hs := @topological_swap_continuous G G.
constructor.
- apply: topological_pair_continuous; last exact: second_projection_continuous.
  by move=> p; have := continuous_comp (hs p) (@hm (p.2, p.1)); exact.
- apply: topological_pair_continuous; last exact: second_projection_continuous.
  by move=> p; have := continuous_comp (hs p) (@hd (p.2, p.1)); exact.
- by case=> x y /=; rewrite (group_mulKg hG).
- by case=> z y /=; rewrite (group_mulKVg hG).
Qed.

(** Source for [right_shear_homeomorphism]: the map
    (x,y) |-> (y x^{-1}, y) of G x G is a homeomorphism with inverse
    (z,y) |-> (z^{-1} y, y). Supporting lemma for the function
    u(y) v(y x^{-1}) under Fubini's theorem in Federer 2.7.6, p. 125. *)
Lemma right_shear_homeomorphism :
  is_homeomorphism_with_inverse (fun p : G * G => (mul p.2 (inv p.1), p.2))
    (fun p : G * G => (mul (inv p.1) p.2, p.2)).
Proof.
constructor.
- apply: topological_pair_continuous; last exact: second_projection_continuous.
  exact: (right_multiplication_action_continuous hT).
- apply: topological_pair_continuous; last exact: second_projection_continuous.
  exact: (division_continuous hT).
- by case=> x y /=; rewrite (group_invM hG) (group_invK hG) (group_mulgKV hG).
- by case=> z y /=; rewrite (group_invM hG) (group_invK hG) (group_mulKVg hG).
Qed.

(** Source for [left_shear_compact]: (x,y) |-> u(y x) v(y) belongs to
    K(G x G) whenever u, v in K(G), as required for "Fubini's theorem"
    in Federer 2.7.6, p. 125. Supporting lemma. *)
Lemma left_shear_compact u v : K u -> K v -> K2 (fun p : G * G => u (mul p.2 p.1) * v p.2).
Proof.
move=> hu hv; have hh := left_shear_homeomorphism.
exact (@compactly_supported_compose R (G * G)%type (G * G)%type _ (homeomorphism_continuous hh)
  (homeomorphism_with_inverse_proper hh) _ (compactly_supported_separated_product hu hv)).
Qed.

(** Source for [right_shear_compact]: (x,y) |-> u(y) v(y x^{-1})
    belongs to K(G x G) whenever u, v in K(G), as required for
    "Fubini's theorem" in Federer 2.7.6, p. 125. Supporting lemma. *)
Lemma right_shear_compact u v : K u -> K v -> K2 (fun p : G * G => u p.2 * v (mul p.2 (inv p.1))).
Proof.
move=> hu hv; have hh := right_shear_homeomorphism.
have -> : (fun p : G * G => u p.2 * v (mul p.2 (inv p.1))) =
    (fun p : G * G => v p.1 * u p.2) \o (fun p : G * G => (mul p.2 (inv p.1), p.2)).
  by apply: funext=> p; rewrite /= mulrC.
exact (@compactly_supported_compose R (G * G)%type (G * G)%type _ (homeomorphism_continuous hh)
  (homeomorphism_with_inverse_proper hh) _ (compactly_supported_separated_product hv hu)).
Qed.

(** Source for [division_translate_compact]: x |-> v(y x^{-1})
    belongs to K(G) whenever v in K(G) and y in G, so that
    lambda_x v(y x^{-1}) in Federer 2.7.6(1), p. 125, is defined. It is
    v o (left multiplication by y) o (inversion). Supporting lemma. *)
Lemma division_translate_compact v y : K v -> K (fun x => v (mul y (inv x))).
Proof.
move=> hv.
have h1 : K (v \o left_multiplication_action mul y) :=
  compactly_supported_translate hG (left_multiplication_homogeneous hT) y hv.
exact (@compactly_supported_compose R G G inv (topological_group_inv_continuous hT)
  (homeomorphism_with_inverse_proper (inversion_homeomorphism hT)) _ h1).
Qed.

(** Source for [right_translate_compact]: y |-> v(y x^{-1}) belongs to
    K(G) whenever v in K(G) and x in G; it is v o A_x for the action
    2.7.2(2), p. 122. Supporting lemma for Federer 2.7.6, p. 125. *)
Lemma right_translate_compact v x : K v -> K (fun y => v (mul y (inv x))).
Proof.
move=> hv; exact (compactly_supported_translate hG (right_multiplication_homogeneous hT) x hv).
Qed.

End HaarShear.

Section HaarDensity.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.
Variables (lambda mu : (G -> R) -> R).
Hypothesis hl : is_left_haar_integral mul lambda.
Hypothesis hr : is_right_haar_integral mul inv mu.
Local Notation K := (@compactly_supported_continuous_functions R G).
(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121. *)
Let hT := lch_group_topological hGc.
(** Source for [hG]: the group laws of G, Federer 2.7.1, p. 121. *)
Let hG := topological_group_laws hT.
(** Source for [hH]: G is Hausdorff, Federer 2.7.1, p. 121. *)
Let hH := lch_group_hausdorff hGc.
(** Source for [hlc]: G is locally compact, Federer 2.7.1, p. 121. *)
Let hlc := lch_group_locally_compact hGc.
(** Source for [hld]: lambda is a Daniell integral on K(G), part of
    "left Haar integral", Federer 2.7.1-2.7.2, p. 122. *)
Let hld := covariant_integral_daniell (nonzero_invariant_integral_invariant hl).
(** Source for [hrd]: mu is a Daniell integral on K(G), part of
    "right Haar integral", Federer 2.7.1-2.7.2, p. 122. *)
Let hrd := covariant_integral_daniell (nonzero_invariant_integral_invariant hr).
(** Source for [hlin]: lambda is linear on K(G), Federer 2.5.13,
    p. 106, used in the computation of 2.7.6, p. 125. *)
Let hlin := daniell_compact_support_linear hld.
(** Source for [hrin]: mu is linear on K(G), Federer 2.5.13, p. 106,
    used in the computation of 2.7.6, p. 125. *)
Let hrin := daniell_compact_support_linear hrd.

(** Source for [haar_fubini_identity]: the computation in the proof of
    Federer 2.7.6, p. 125, "Using Fubini's theorem we compute
    lambda(u) mu(v) = ... = mu_y[u(y) . lambda_x v(y x^{-1})]",
    whenever u, v in K(G). Direct formalisation; Fubini's theorem is
    compact_daniell_iterations_commute. *)
Theorem haar_fubini_identity u v : K u -> K v ->
  lambda u * mu v = mu (fun y => u y * lambda (fun x => v (mul y (inv x)))).
Proof.
move=> hu hv.
have hli y : lambda (fun x => u (mul y x) * v y) = lambda u * v y.
  have hy : K (u \o left_multiplication_action mul y) :=
    compactly_supported_translate hG (left_multiplication_homogeneous hT) y hu.
  have -> : (fun x => u (mul y x) * v y) =
      (fun x => v y * (u \o left_multiplication_action mul y) x).
    by apply: funext=> x; rewrite mulrC.
  by rewrite (hlin.2 (v y) _ hy) (invariant_integral_translate hl y hu) mulrC.
have h1 : lambda u * mu v = mu (fun y => lambda (fun x => u (mul y x) * v y)).
  by rewrite (funext hli) (hrin.2 (lambda u) _ hv).
have hF1 : mu (fun y => lambda (fun x => u (mul y x) * v y)) =
    lambda (fun x => mu (fun y => u (mul y x) * v y)) :=
  compact_daniell_iterations_commute hH hlc hH hlc hld hrd (left_shear_compact hT hu hv).
have hri x : mu (fun y => u (mul y x) * v y) = mu (fun y => u y * v (mul y (inv x))).
  have hw : K (fun y => u y * v (mul y (inv x))) :=
    compact_support_continuous_multiplier hu.1 (right_translate_compact hT x hv).
  rewrite -(invariant_integral_translate hr (inv x) hw); congr mu; apply: funext=> y.
  by rewrite /= /right_multiplication_action (group_invK hG) (group_mulgK hG).
have hF2 : lambda (fun x => mu (fun y => u y * v (mul y (inv x)))) =
    mu (fun y => lambda (fun x => u y * v (mul y (inv x)))) :=
  esym (compact_daniell_iterations_commute hH hlc hH hlc hld hrd (right_shear_compact hT hu hv)).
have hsc y : lambda (fun x => u y * v (mul y (inv x))) = u y * lambda (fun x => v (mul y (inv x))).
  exact: (hlin.2 (u y) _ (division_translate_compact hT y hv)).
by rewrite h1 hF1 (funext hri) hF2 (funext hsc).
Qed.

(** Source for [haar_section_integral_continuous]: continuity of
    y |-> lambda_x v(y x^{-1}) for v in K(G), presupposed by "we can
    use the equation in (1) to define a positive continuous function k
    on G", Federer 2.7.6, p. 125. Near b the function equals
    y |-> lambda_x[w(y) v(y x^{-1})] for a cutoff function w in K(G)
    equal to 1 on a compact neighbourhood of b. *)
Lemma haar_section_integral_continuous v : K v ->
  continuous ((fun y => lambda (fun x => v (mul y (inv x)))) : G -> real_line_metric R).
Proof.
move=> hv b.
have [N hN [hNc _]] := @hlc b I; rewrite withinET in hN.
have [hw hw01 hw1] := compact_cutoff_specification R hH hlc hNc.
set w := compact_cutoff R hH hlc hNc in hw hw01 hw1.
have hc := compact_section_functional_continuous hH hlc hld (right_shear_compact hT hw hv) (x:=b).
have hwy y : N y -> lambda (fun x => w y * v (mul y (inv x))) = lambda (fun x => v (mul y (inv x))).
  move=> hy; rewrite (hlin.2 (w y) _ (division_translate_compact hT y hv)) (hw1 y hy).
  exact: mul1r.
have hnear : \forall y \near b,
    lambda (fun x => w y * v (mul y (inv x))) = lambda (fun x => v (mul y (inv x))).
  by apply: filterS hN=> y; exact: hwy.
apply: cvg_trans (near_eq_cvg hnear) _.
rewrite -(hwy b (nbhs_singleton hN)).
exact: hc.
Qed.

(** Source for [haar_section_quotient_density]: "If we choose any
    particular nonzero v in K(G)+, we can use the equation in (1) to
    define a ... continuous function k on G, and our computation
    implies (2) for all u in K(G)", Federer 2.7.6, p. 125: for v in K(G)
    with mu(v) <> 0 the function k(y) = lambda_x v(y x^{-1}) / mu(v) is
    continuous and satisfies (2). The proof uses only mu(v) <> 0. *)
Lemma haar_section_quotient_density v : K v -> mu v != 0 ->
  continuous ((fun y => lambda (fun x => v (mul y (inv x))) / mu v) : G -> real_line_metric R) /\
  forall u, K u -> mu (fun y => lambda (fun x => v (mul y (inv x))) / mu v * u y) = lambda u.
Proof.
move=> hv hmv.
have hFc := haar_section_integral_continuous hv.
split.
  move=> y; apply: (@continuousM R G _ (fun _ => (mu v)^-1) y (hFc y)).
  exact: cvg_cst.
move=> u hu.
have hFu := compact_support_continuous_multiplier hFc hu.
have -> : (fun y => lambda (fun x => v (mul y (inv x))) / mu v * u y) =
    (fun y => (mu v)^-1 * (u y * lambda (fun x => v (mul y (inv x))))).
  by apply: funext=> y; rewrite mulrAC mulrC [u y * _]mulrC.
have hFu' : K (fun y => u y * lambda (fun x => v (mul y (inv x)))).
  have -> : (fun y => u y * lambda (fun x => v (mul y (inv x)))) =
      (fun y => lambda (fun x => v (mul y (inv x))) * u y).
    by apply: funext=> y; exact: mulrC.
  exact: hFu.
rewrite (hrin.2 _ _ hFu') -(haar_fubini_identity hu hv).
by rewrite mulrCA mulVf // mulr1.
Qed.

(** Source for [haar_integral_density_unique]: "However k is uniquely
    characterized by (2)", Federer 2.7.6, p. 125: two continuous
    functions k_1, k_2 on G with mu(k_1 u) = lambda(u) = mu(k_2 u)
    whenever u in K(G) are equal. Direct formalisation; continuity is
    the class in which k is characterised, since mu is defined on K(G)
    only. *)
Theorem haar_integral_density_unique (k1 k2 : G -> R) :
  continuous (k1 : G -> real_line_metric R) -> continuous (k2 : G -> real_line_metric R) ->
  (forall u, K u -> mu (fun y => k1 y * u y) = lambda u) ->
  (forall u, K u -> mu (fun y => k2 y * u y) = lambda u) -> k1 = k2.
Proof.
move=> h1 h2 hk1 hk2; apply: (right_haar_multiplier_unique hT hH hlc hr h1 h2)=> u hu.
by rewrite hk1 // hk2.
Qed.

(** Source for [haar_integral_density_choice_independent]: "hence
    [k] does not really depend on the choice of v", Federer 2.7.6,
    p. 125: the quotients lambda_x v(y x^{-1}) / mu(v) agree for all
    v_1, v_2 in K(G) with mu(v_1) <> 0 <> mu(v_2); this includes all
    nonzero v in K(G)+ by right_haar_integral_positive. *)
Corollary haar_integral_density_choice_independent v1 v2 :
  K v1 -> K v2 -> mu v1 != 0 -> mu v2 != 0 ->
  (fun y => lambda (fun x => v1 (mul y (inv x))) / mu v1) =
  (fun y => lambda (fun x => v2 (mul y (inv x))) / mu v2).
Proof.
move=> hv1 hv2 hm1 hm2.
have [hc1 hk1] := haar_section_quotient_density hv1 hm1.
have [hc2 hk2] := haar_section_quotient_density hv2 hm2.
exact: haar_integral_density_unique hc1 hc2 hk1 hk2.
Qed.

(** Source for [haar_density_section_identity]: "It follows that (1)
    holds for all v in K(G)", Federer 2.7.6, p. 125: every continuous
    k satisfying (2) satisfies k(y) mu(v) = lambda_x v(y x^{-1})
    whenever y in G, v in K(G). The continuous functions
    y |-> lambda_x v(y x^{-1}) and y |-> mu(v) k(y) have the same
    integrals against every u in K(G), by haar_fubini_identity and (2). *)
Theorem haar_density_section_identity (k : G -> R) :
  continuous (k : G -> real_line_metric R) ->
  (forall u, K u -> mu (fun y => k y * u y) = lambda u) ->
  forall y v, K v -> k y * mu v = lambda (fun x => v (mul y (inv x))).
Proof.
move=> hkc hk y v hv.
have hFc := haar_section_integral_continuous hv.
have hkm : continuous ((fun z => mu v * k z) : G -> real_line_metric R).
  move=> z; apply: (@continuousM R G (fun _ => mu v) k z); [exact: cvg_cst|exact: hkc].
have heq : (fun z => lambda (fun x => v (mul z (inv x)))) = (fun z => mu v * k z).
  apply: (right_haar_multiplier_unique hT hH hlc hr hFc hkm)=> u hu.
  have hku : K (fun z => k z * u z) := compact_support_continuous_multiplier hkc hu.
  have -> : (fun z => mu v * k z * u z) = (fun z => mu v * (k z * u z)).
    by apply: funext=> z; rewrite mulrA.
  rewrite (hrin.2 _ _ hku) hk // mulrC (haar_fubini_identity hu hv); congr mu.
  by apply: funext=> z; rewrite mulrC.
by have := congr1 (fun f => f y) heq; rewrite /= mulrC=> ->.
Qed.

(** Source for [haar_integral_density]: Federer 2.7.6, p. 125,
    "If lambda is a left Haar integral and mu is a right Haar
    integral, then there exists a continuous positive real valued
    function k on G such that (1) k(y) mu(v) = lambda_x v(y x^{-1})
    whenever y in G, v in K(G), (2) mu(k u) = lambda(u) whenever
    u in K(G)." Direct formalisation; k is defined from a cutoff
    function v_0 in K(G)+ with v_0(e) = 1. *)
Theorem haar_integral_density :
  exists k : G -> R,
    [/\ continuous (k : G -> real_line_metric R), forall y, 0 < k y,
      forall y v, K v -> k y * mu v = lambda (fun x => v (mul y (inv x))) &
      forall u, K u -> mu (fun y => k y * u y) = lambda u].
Proof.
have [hv0 hv001 hv01] := compact_cutoff_specification R hH hlc (@compact_set1 G e).
set v0 := compact_cutoff R hH hlc (@compact_set1 G e) in hv0 hv001 hv01.
have hv0e : v0 e = 1 := hv01 e erefl.
have hv0n : function_nonnegative v0 by move=> x; exact: (andP (hv001 x)).1.
have hmv0 : 0 < mu v0.
  apply: (right_haar_integral_positive hT hr hv0 hv0n).
  by exists e; rewrite hv0e; apply/eqP; exact: oner_neq0.
have [hkc hk2] := haar_section_quotient_density hv0 (lt0r_neq0 hmv0).
exists (fun y => lambda (fun x => v0 (mul y (inv x))) / mu v0); split=> //.
- move=> y; apply: divr_gt0 hmv0.
  apply: (left_haar_integral_positive hT hl (division_translate_compact hT y hv0)).
    by move=> x; exact: hv0n.
  by exists y; rewrite (group_mulgV hG) hv0e; apply/eqP; exact: oner_neq0.
- exact: haar_density_section_identity hkc hk2.
Qed.

End HaarDensity.
