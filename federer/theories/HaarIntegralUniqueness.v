(** Federer (1969), 2.7.7, printed pp. 125-126: "Theorem. Any two left
    (right) Haar integrals of G are constant positive multiples of each
    other. Proof. Suppose lambda_1, lambda_2 are left Haar integrals and mu
    is a right Haar integral. According to 2.7.6 there exist positive
    continuous functions k_1, k_2 on G such that mu(k_1 u) = lambda_1(u),
    mu(k_2 u) = lambda_2(u) whenever u in K(G). Then f = k_1/k_2 is a
    positive continuous function such that lambda_1(u) = mu(k_2 f u) =
    lambda_2(f u) whenever u in K(G). If g in G, then lambda_2(f u) =
    lambda_1(u) = lambda_1(u o A_g) = lambda_2[f . (u o A_g)] = lambda_2[(f
    o A_g^{-1}) . u] whenever u in K(G), hence f = f o A_g^{-1}. Thus f is
    constant on G." Here G is a locally compact Hausdorff topological group
    and A_g is left multiplication by g. The right Haar integral mu is
    p#(lambda_1), p the inversion of G, which is a right Haar integral by
    2.7.2, p. 123 (left_haar_inversion); thus the existence theorem 2.7.5 is
    not used. The step "hence f = f o A_g^{-1}" is
    left_haar_multiplier_unique of InvariantIntegralPositivity.v, and f is
    constant because f(x) = f(x^{-1} x) = f(e). The right version is deduced
    from the left version applied to p#(mu_1) and p#(mu_2), which are left
    Haar integrals by 2.7.2 (right_haar_inversion), since p#(p#(mu)) = mu.
    The local erratum has no entry for pp. 125-126. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground HomeomorphismUP TopologicalGroupUP
  TopologicalGroupLaws CompactSupportFunctionUP CompactSupportProducts DaniellSpaceCompactness
  DaniellSpacePushforward CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP
  GroupMultiplicationHomogeneous EquivariantPushforward HaarInversion
  InvariantIntegralPositivity HaarIntegralDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section HaarUniqueness.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.
Local Notation K := (@compactly_supported_continuous_functions R G).
(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121. *)
Let hT := lch_group_topological hGc.
(** Source for [hG]: the group laws of G, Federer 2.7.1, p. 121. *)
Let hG := topological_group_laws hT.
(** Source for [hH]: G is Hausdorff, Federer 2.7.1, p. 121. *)
Let hH := lch_group_hausdorff hGc.
(** Source for [hlc]: G is locally compact, Federer 2.7.1, p. 121. *)
Let hlc := lch_group_locally_compact hGc.

(** Source for [left_haar_integral_unique]: "Any two left ... Haar
    integrals of G are constant positive multiples of each other",
    Federer 2.7.7, p. 125. Direct formalisation, following the printed
    proof with mu = p#(lambda_1). *)
Theorem left_haar_integral_unique (lambda1 lambda2 : (G -> R) -> R) :
  is_left_haar_integral mul lambda1 -> is_left_haar_integral mul lambda2 ->
  exists2 c : R, 0 < c & forall u, K u -> lambda1 u = c * lambda2 u.
Proof.
move=> hl1 hl2.
have hr := (left_haar_inversion hT lambda1).1 hl1.
set mu := daniell_pushforward inv lambda1 in hr.
have [k1 [hk1c hk1p _ hk1]] := haar_integral_density hGc hl1 hr.
have [k2 [hk2c hk2p _ hk2]] := haar_integral_density hGc hl2 hr.
pose f y := k1 y / k2 y.
have hfc : continuous (f : G -> real_line_metric R).
  move=> y; apply: (@continuousM R G k1 (fun z => (k2 z)^-1) y (hk1c y)).
  exact: (continuousV (lt0r_neq0 (hk2p y)) (hk2c y)).
have hld2 := covariant_integral_daniell (nonzero_invariant_integral_invariant hl2).
have hf u : K u -> lambda1 u = lambda2 (fun y => f y * u y).
  move=> hu; have hfu : K (fun y => f y * u y) := compact_support_continuous_multiplier hfc hu.
  rewrite -(hk1 u hu) -(hk2 _ hfu); congr mu; apply: funext=> y.
  rewrite /f mulrA [k2 y * _]mulrC divfK //; exact: lt0r_neq0 (hk2p y).
have hinv g : f = f \o left_multiplication_action mul (inv g).
  have hfgc : continuous ((f \o left_multiplication_action mul (inv g)) : G -> real_line_metric R).
    move=> y; exact: continuous_comp (left_translation_continuous hT (inv g) y) (hfc _).
  apply: (left_haar_multiplier_unique hT hH hlc hl2 hfc hfgc)=> u hu.
  have hug : K (u \o left_multiplication_action mul g) :=
    compactly_supported_translate hG (left_multiplication_homogeneous hT) g hu.
  have hw : K (fun x => (f \o left_multiplication_action mul (inv g)) x * u x) :=
    compact_support_continuous_multiplier hfgc hu.
  rewrite -(hf u hu) -(invariant_integral_translate hl1 g hu) (hf _ hug).
  rewrite -(invariant_integral_translate hl2 g hw); congr lambda2; apply: funext=> x.
  by rewrite /= /left_multiplication_action (group_mulKg hG).
have hconst x : f x = f e.
  have := congr1 (fun h => h x) (hinv x).
  by rewrite /= /left_multiplication_action (group_mulVg hG).
exists (f e); first exact: divr_gt0 (hk1p e) (hk2p e).
move=> u hu; rewrite (hf u hu).
have -> : (fun y => f y * u y) = (fun y => f e * u y) by apply: funext=> y; rewrite hconst.
exact: (daniell_compact_support_linear hld2).2 (f e) u hu.
Qed.

(** Source for [right_haar_integral_unique]: "Any two ... (right) Haar
    integrals of G are constant positive multiples of each other",
    Federer 2.7.7, p. 125. Direct formalisation; the proof reduces to
    left_haar_integral_unique through the inversion p of 2.7.2,
    p. 123. *)
Theorem right_haar_integral_unique (mu1 mu2 : (G -> R) -> R) :
  is_right_haar_integral mul inv mu1 -> is_right_haar_integral mul inv mu2 ->
  exists2 c : R, 0 < c & forall u, K u -> mu1 u = c * mu2 u.
Proof.
move=> hr1 hr2.
have hl1 := (right_haar_inversion hT mu1).1 hr1.
have hl2 := (right_haar_inversion hT mu2).1 hr2.
have [c hc hcu] := left_haar_integral_unique hl1 hl2.
exists c=> // u hu.
have hp := inversion_homeomorphism hT.
have hui : K (u \o inv) := @compactly_supported_compose R G G inv (homeomorphism_continuous hp)
  (homeomorphism_with_inverse_proper hp) _ hu.
have := hcu _ hui; rewrite /daniell_pushforward.
have -> : (u \o inv) \o inv = u by apply: funext=> x; rewrite /= (group_invK hG).
by [].
Qed.

End HaarUniqueness.
