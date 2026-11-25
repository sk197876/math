(** Federer (1969), 2.7.8, printed p. 126: "Theorem. There exists a
    continuous positive real valued function Delta_G with the following
    properties: (1) ... (4) ... Moreover Delta_G is uniquely characterized
    by each of these properties; it is called the modular function of G.
    Proof. In view of 2.7.7 we need only consider one particular left Haar
    integral lambda, and the corresponding (see 2.7.2) right Haar integral
    mu = p#(lambda). As Delta_G we may take the function k of 2.7.6, because
    k(y) mu(v) = mu_x v(y x) whenever y in G, v in K(G), hence mu is left k
    covariant, lambda = p#(mu) is right k covariant by 2.7.2, while
    lambda[(k o p) . (u o p)] = mu(k u) = lambda(u), mu[k . (u o p)] =
    lambda(u o p) = mu(u) whenever u in K(G)." The properties (1)-(4) and
    the predicate is_modular_function are those of ModularFunctionUP.v; G is
    a locally compact Hausdorff topological group and p is its inversion.
    The proof follows Federer: for a left Haar integral lambda and the k of
    2.7.6 (haar_integral_density) for lambda and mu = p#(lambda),
    haar_density_modular_function shows that k is a modular function; "in
    view of 2.7.7" is the passage from lambda and mu to arbitrary left and
    right Haar integrals by left_haar_integral_unique and
    right_haar_integral_unique. A left Haar integral exists by 2.7.5
    (left_haar_integral_exists of HaarIntegralExistence.v); it is used for
    the existence statement modular_function_exists and for the four
    uniqueness statements. In the uniqueness statements for (3) and (4) the
    competing function is assumed continuous: lambda and mu are given on
    K(G) only, and continuity guarantees that the integrands in (3) and (4)
    belong to K(G) for every u in K(G). In the uniqueness statements for (1)
    and (2) no condition is imposed on the competing function. The
    uniqueness for (3) and (4) uses the determination of a continuous
    function by its products with K(G) under a Haar integral
    (left_haar_multiplier_unique, right_haar_multiplier_unique of
    InvariantIntegralPositivity.v); the uniqueness for (1) and (2) uses a u
    in K(G) with lambda(u) <> 0. The local erratum has no entry for p. 126. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground HomeomorphismUP TopologicalGroupUP
  TopologicalGroupLaws CompactSupportFunctionUP CompactSupportProducts DaniellSpacePushforward
  CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP GroupMultiplicationHomogeneous
  EquivariantPushforward HaarInversion HaarIntegralExistence InvariantIntegralPositivity
  HaarIntegralDensity HaarIntegralUniqueness ModularFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ModularFunction.
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
(** Source for [hp]: "p(x) = x^{-1} for x in G", Federer 2.7.2,
    p. 123, is a homeomorphism with inverse p. *)
Let hp : is_homeomorphism_with_inverse inv inv := inversion_homeomorphism hT.

(** Source for [inversion_compactly_supported]: u o p belongs to K(G)
    whenever u in K(G), as presupposed by "lambda(u o p)" in the proof
    of Federer 2.7.8, p. 126. Supporting lemma. *)
Lemma inversion_compactly_supported u : K u -> K (u \o inv).
Proof.
exact: (@compactly_supported_compose R G G inv (homeomorphism_continuous hp)
  (homeomorphism_with_inverse_proper hp) u).
Qed.

(** Source for [inversion_pushforward_involutive]: p#(p#(lambda)) =
    lambda, used in "lambda = p#(mu)" of the proof of Federer 2.7.8,
    p. 126, since p o p is the identity. Supporting lemma. *)
Lemma inversion_pushforward_involutive (lambda : (G -> R) -> R) :
  daniell_pushforward inv (daniell_pushforward inv lambda) = lambda.
Proof.
apply: funext=> u; rewrite /daniell_pushforward; congr lambda.
by apply: funext=> x; rewrite /= (group_invK hG).
Qed.

(** Source for [weighted_inversion_compactly_supported]: the function
    x |-> u(x^{-1}) D(x^{-1}) belongs to K(G) whenever u in K(G) and D
    is continuous, so that the left side of Federer 2.7.8(3), p. 126,
    is defined. Supporting lemma. *)
Lemma weighted_inversion_compactly_supported (D : G -> R) u :
  continuous (D : G -> real_line_metric R) -> K u -> K (fun x => u (inv x) * D (inv x)).
Proof.
move=> hD hu.
have h := inversion_compactly_supported (compact_support_continuous_multiplier hD hu).
have -> : (fun x => u (inv x) * D (inv x)) = (fun x => D x * u x) \o inv.
  by apply: funext=> x; rewrite /= mulrC.
exact: h.
Qed.

(** Source for [inversion_weighted_compactly_supported]: the function
    x |-> u(x^{-1}) D(x) belongs to K(G) whenever u in K(G) and D is
    continuous, so that the left side of Federer 2.7.8(4), p. 126, is
    defined. Supporting lemma. *)
Lemma inversion_weighted_compactly_supported (D : G -> R) u :
  continuous (D : G -> real_line_metric R) -> K u -> K (fun x => u (inv x) * D x).
Proof.
move=> hD hu.
have h := compact_support_continuous_multiplier hD (inversion_compactly_supported hu).
have -> : (fun x => u (inv x) * D x) = (fun x => D x * (u \o inv) x).
  by apply: funext=> x; rewrite /= mulrC.
exact: h.
Qed.

Section FixedLeftHaar.
Variable lambda : (G -> R) -> R.
Hypothesis hl : is_left_haar_integral mul lambda.
(** Source for [mu]: "the corresponding (see 2.7.2) right Haar
    integral mu = p#(lambda)", Federer 2.7.8, p. 126. *)
Let mu := daniell_pushforward inv lambda.
(** Source for [hr]: mu = p#(lambda) is a right Haar integral, Federer
    2.7.2, p. 123, as cited in 2.7.8, p. 126. *)
Let hr : is_right_haar_integral mul inv mu := (left_haar_inversion hT lambda).1 hl.
Variable k : G -> R.
Hypothesis hkc : continuous (k : G -> real_line_metric R).
Hypothesis hkp : forall y, 0 < k y.
Hypothesis hk1 : forall y v, K v -> k y * mu v = lambda (fun x => v (mul y (inv x))).
Hypothesis hk2 : forall u, K u -> mu (fun y => k y * u y) = lambda u.

(** Source for [haar_density_left_translation]: the display
    "k(y) mu(v) = mu_x v(y x) whenever y in G, v in K(G)" in the proof
    of Federer 2.7.8, p. 126, for the function k of 2.7.6(1). Direct
    formalisation: mu_x v(y x) = lambda_x v(y x^{-1}). *)
Lemma haar_density_left_translation y v : K v -> k y * mu v = mu (fun x => v (mul y x)).
Proof. by move=> hv; rewrite hk1. Qed.

(** Source for [haar_density_right_haar_left_covariant]: "hence mu is
    left k covariant", Federer 2.7.8, p. 126. Direct formalisation. *)
Lemma haar_density_right_haar_left_covariant : is_left_covariant_integral mul k mu.
Proof.
constructor; first exact: covariant_integral_daniell (nonzero_invariant_integral_invariant hr).
by move=> v y hv; rewrite (haar_density_left_translation y hv).
Qed.

(** Source for [haar_density_left_haar_right_covariant]: "lambda =
    p#(mu) is right k covariant by 2.7.2", Federer 2.7.8, p. 126.
    Direct formalisation through left_covariant_inversion. *)
Lemma haar_density_left_haar_right_covariant : is_right_covariant_integral mul inv k lambda.
Proof.
have h := (left_covariant_inversion hT k mu).1 haar_density_right_haar_left_covariant.
by rewrite /mu inversion_pushforward_involutive in h.
Qed.

(** Source for [haar_density_left_inversion]: "lambda[(k o p) .
    (u o p)] = mu(k u) = lambda(u) ... whenever u in K(G)", Federer
    2.7.8, p. 126, for the function k of 2.7.6(2). Direct
    formalisation. *)
Lemma haar_density_left_inversion u : K u -> lambda (fun x => u (inv x) * k (inv x)) = lambda u.
Proof.
move=> hu; rewrite -(hk2 hu) /mu /daniell_pushforward; congr lambda.
by apply: funext=> x; rewrite /= mulrC.
Qed.

(** Source for [haar_density_right_inversion]: "mu[k . (u o p)] =
    lambda(u o p) = mu(u) whenever u in K(G)", Federer 2.7.8, p. 126,
    for the function k of 2.7.6(2). Direct formalisation. *)
Lemma haar_density_right_inversion u : K u -> mu (fun x => u (inv x) * k x) = mu u.
Proof.
move=> hu; have h := hk2 (inversion_compactly_supported hu).
have -> : (fun x => u (inv x) * k x) = (fun y => k y * (u \o inv) y).
  by apply: funext=> x; rewrite /= mulrC.
by rewrite h.
Qed.

(** Source for [haar_density_modular_function]: "As Delta_G we may
    take the function k of 2.7.6", Federer 2.7.8, p. 126: k has the
    properties (1)-(4) for all left and right Haar integrals. Direct
    formalisation; "In view of 2.7.7 we need only consider one
    particular left Haar integral" is the use of
    left_haar_integral_unique and right_haar_integral_unique. *)
Theorem haar_density_modular_function : is_modular_function mul inv k.
Proof.
have hlr := haar_density_left_haar_right_covariant.
have hrl := haar_density_right_haar_left_covariant.
constructor=> //.
- move=> lambda' hl'; have [c _ hcu] := left_haar_integral_unique hGc hl' hl.
  constructor; first exact: covariant_integral_daniell (nonzero_invariant_integral_invariant hl').
  move=> u g hu.
  have hug := compactly_supported_translate hG (right_multiplication_homogeneous hT) g hu.
  by rewrite (hcu _ hug) (hcu _ hu) (covariant_integral_law hlr g hu) mulrCA.
- move=> mu' hr'; have [c _ hcu] := right_haar_integral_unique hGc hr' hr.
  constructor; first exact: covariant_integral_daniell (nonzero_invariant_integral_invariant hr').
  move=> u g hu.
  have hug := compactly_supported_translate hG (left_multiplication_homogeneous hT) g hu.
  by rewrite (hcu _ hug) (hcu _ hu) (covariant_integral_law hrl g hu) mulrCA.
- move=> lambda' hl' u hu; have [c _ hcu] := left_haar_integral_unique hGc hl' hl.
  rewrite (hcu _ (weighted_inversion_compactly_supported hkc hu)) (hcu _ hu).
  by rewrite haar_density_left_inversion.
- move=> mu' hr' u hu; have [c _ hcu] := right_haar_integral_unique hGc hr' hr.
  rewrite (hcu _ (inversion_weighted_compactly_supported hkc hu)) (hcu _ hu).
  by rewrite haar_density_right_inversion.
Qed.

End FixedLeftHaar.

(** Source for [modular_function_of_left_haar]: the proof of Federer
    2.7.8, p. 126, for a given left Haar integral lambda: the function
    k of 2.7.6 for lambda and mu = p#(lambda) is a modular function.
    Direct formalisation for the given lambda. *)
Theorem modular_function_of_left_haar (lambda : (G -> R) -> R) :
  is_left_haar_integral mul lambda ->
  exists k : G -> R,
    [/\ is_modular_function mul inv k,
      forall y v, K v ->
        k y * daniell_pushforward inv lambda v = lambda (fun x => v (mul y (inv x))) &
      forall u, K u -> daniell_pushforward inv lambda (fun y => k y * u y) = lambda u].
Proof.
move=> hl; have hr := (left_haar_inversion hT lambda).1 hl.
have [k [hkc hkp hk1 hk2]] := haar_integral_density hGc hl hr.
by exists k; split=> //; exact: (haar_density_modular_function hl hkc hkp hk1 hk2).
Qed.

(** Source for [modular_function_exists]: "There exists a continuous
    positive real valued function Delta_G with the following
    properties: (1) ... (4)", Federer 2.7.8, p. 126. Direct
    formalisation, following Federer's proof
    (modular_function_of_left_haar) for a left Haar integral given by
    2.7.5, p. 125 (left_haar_integral_exists). *)
Theorem modular_function_exists : exists D : G -> R, is_modular_function mul inv D.
Proof.
have [lambda hl] := left_haar_integral_exists R hGc.
by have [k [hk _ _]] := modular_function_of_left_haar hl; exists k.
Qed.

(** Source for [modular_function_unique_left_haar]: "Delta_G is
    uniquely characterized by each of these properties", Federer 2.7.8,
    p. 126, for property (1): every function D: G -> R such that every
    left Haar integral is right D covariant equals Delta_G. Direct
    formalisation; for a left Haar integral lambda (2.7.5) and
    lambda(u) <> 0 both D(g) and Delta_G(g) equal
    lambda(u o A_g)/lambda(u). *)
Theorem modular_function_unique_left_haar (Delta D : G -> R) :
  is_modular_function mul inv Delta -> left_haar_right_covariant mul inv D -> D = Delta.
Proof.
move=> hD hd; have [lambda hl] := left_haar_integral_exists R hGc.
have [u hu hu0] := nonzero_invariant_integral_nonzero hl.
apply: funext=> g.
have h1 := covariant_integral_law (hd lambda hl) g hu.
have h2 := covariant_integral_law (modular_function_left_haar hD hl) g hu.
rewrite h1 in h2; exact: (mulIf (introN eqP hu0) h2).
Qed.

(** Source for [modular_function_unique_right_haar]: "Delta_G is
    uniquely characterized by each of these properties", Federer 2.7.8,
    p. 126, for property (2): every function D: G -> R such that every
    right Haar integral is left D covariant equals Delta_G. Direct
    formalisation; for a left Haar integral lambda (2.7.5), p#(lambda)
    is a right Haar integral (2.7.2, p. 123). *)
Theorem modular_function_unique_right_haar (Delta D : G -> R) :
  is_modular_function mul inv Delta -> right_haar_left_covariant mul inv D -> D = Delta.
Proof.
move=> hD hd; have [lambda hl] := left_haar_integral_exists R hGc.
have hr := (left_haar_inversion hT lambda).1 hl.
have [u hu hu0] := nonzero_invariant_integral_nonzero hr.
apply: funext=> g.
have h1 := covariant_integral_law (hd _ hr) g hu.
have h2 := covariant_integral_law (modular_function_right_haar hD hr) g hu.
rewrite h1 in h2; exact: (mulIf (introN eqP hu0) h2).
Qed.

(** Source for [modular_function_unique_left_inversion]: "Delta_G is
    uniquely characterized by each of these properties", Federer 2.7.8,
    p. 126, for property (3): every continuous function D: G -> R with
    lambda_x[u(x^{-1}) D(x^{-1})] = lambda(u) for all left Haar
    integrals lambda and u in K(G) equals Delta_G. Direct formalisation;
    a left Haar integral exists by 2.7.5. Continuity of D makes the
    integrands members of K(G). With u = w o p one obtains
    lambda((D o p) w) = lambda((Delta_G o p) w) for w in K(G), hence
    D o p = Delta_G o p by left_haar_multiplier_unique. *)
Theorem modular_function_unique_left_inversion (Delta D : G -> R) :
  is_modular_function mul inv Delta -> continuous (D : G -> real_line_metric R) ->
  left_haar_inversion_identity mul inv D -> D = Delta.
Proof.
move=> hD hDc hd; have [lambda hl] := left_haar_integral_exists R hGc.
have hic : continuous inv := topological_group_inv_continuous hT.
have hc1 : continuous ((D \o inv) : G -> real_line_metric R).
  by move=> x; exact: continuous_comp (hic x) (hDc _).
have hDec : continuous (Delta : G -> real_line_metric R) := modular_function_continuous hD.
have hc2 : continuous ((Delta \o inv) : G -> real_line_metric R).
  by move=> x; exact: continuous_comp (hic x) (hDec _).
have heq : D \o inv = Delta \o inv.
  apply: (left_haar_multiplier_unique hT hH hlc hl hc1 hc2)=> w hw.
  have hwi := inversion_compactly_supported hw.
  have h1 := hd lambda hl _ hwi.
  have h2 := modular_function_left_inversion hD hl hwi.
  have e1 F : (fun x => (w \o inv) (inv x) * F (inv x)) = (fun x => (F \o inv) x * w x).
    by apply: funext=> x; rewrite /= (group_invK hG) mulrC.
  by rewrite -e1 -e1 h1 h2.
apply: funext=> g; have := congr1 (fun f => f (inv g)) heq.
by rewrite /= (group_invK hG).
Qed.

(** Source for [modular_function_unique_right_inversion]: "Delta_G is
    uniquely characterized by each of these properties", Federer 2.7.8,
    p. 126, for property (4): every continuous function D: G -> R with
    mu_x[u(x^{-1}) D(x)] = mu(u) for all right Haar integrals mu and
    u in K(G) equals Delta_G. Direct formalisation; for a left Haar
    integral lambda (2.7.5), mu = p#(lambda) is a right Haar integral,
    and u = w o p gives mu(D w) = mu(Delta_G w) for w in K(G), hence
    D = Delta_G by right_haar_multiplier_unique. *)
Theorem modular_function_unique_right_inversion (Delta D : G -> R) :
  is_modular_function mul inv Delta -> continuous (D : G -> real_line_metric R) ->
  right_haar_inversion_identity mul inv D -> D = Delta.
Proof.
move=> hD hDc hd; have [lambda hl] := left_haar_integral_exists R hGc.
have hr := (left_haar_inversion hT lambda).1 hl.
apply: (right_haar_multiplier_unique hT hH hlc hr hDc (modular_function_continuous hD))=> w hw.
have hwi := inversion_compactly_supported hw.
have h1 := hd _ hr _ hwi.
have h2 := modular_function_right_inversion hD hr hwi.
have e1 F : (fun x => (w \o inv) (inv x) * F x) = (fun x => F x * w x).
  by apply: funext=> x; rewrite /= (group_invK hG) mulrC.
by rewrite -e1 -e1 h1 h2.
Qed.

(** Source for [modular_function_unique]: "Delta_G is uniquely
    characterized", Federer 2.7.8, p. 126: two modular functions of G
    coincide. Corollary of modular_function_unique_left_haar. *)
Corollary modular_function_unique (D1 D2 : G -> R) :
  is_modular_function mul inv D1 -> is_modular_function mul inv D2 -> D1 = D2.
Proof.
move=> h1 h2; exact: modular_function_unique_left_haar h2 (modular_function_left_haar h1).
Qed.

(** Source for [modular_function_homomorphism]: the modular function
    is a homomorphism of G into the multiplicative group R ~ {0}, by
    2.7.8(1) and "In case mu <> 0, it follows that chi is a continuous
    homomorphism of G into the multiplicative group R ~ {0}", Federer
    2.7.1, p. 122, applied to a left Haar integral (2.7.5). Supporting
    corollary, not stated in 2.7.8. *)
Corollary modular_function_homomorphism (Delta : G -> R) :
  is_modular_function mul inv Delta ->
  (forall g h, Delta (mul g h) = Delta g * Delta h) /\ Delta e = 1.
Proof.
move=> hD; have [lambda hl] := left_haar_integral_exists R hGc.
have [u hu hu0] := nonzero_invariant_integral_nonzero hl.
have hc := covariant_integral_law (modular_function_left_haar hD hl).
have hA := right_multiplication_homogeneous hT.
split.
- exact: (covariant_character_multiplicative hG hA hc hu hu0).
- exact: (covariant_character_unit hG hA hc hu hu0).
Qed.

End ModularFunction.
