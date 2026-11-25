(** Federer (1969), 2.7.9, printed pp. 126-127: "Theorem. Suppose nu is a
    Daniell integral on K(G) and chi is a continuous homomorphism of G into
    the multiplicative group R ~ {0}. (1) nu is left chi covariant if and
    only if there exists a left Haar integral lambda and a real number r
    such that nu(u) = r lambda(u chi^{-1}) whenever u in K(G). (2) nu is
    right chi covariant if and only if there exists a right Haar integral mu
    and a real number r such that nu(u) = r mu(u chi) whenever u in K(G).
    (3) nu is left chi covariant if and only if nu is right Delta_G chi^{-1}
    covariant. Proof. To verify (1) we define sigma(u) = nu(u chi) whenever
    u in K(G), compute sigma(u o A_g) = nu_x[u(g x) chi(x)] = chi(g)^{-1}
    nu[(u chi) o A_g] for g in G, and infer that nu is left chi covariant if
    and only if sigma is left invariant. If sigma is left invariant, so are
    sigma+ and sigma-, hence sigma+ and sigma- are nonnegative multiples of
    a left Haar integral. We obtain (2) from (1) by means of p# (see 2.7.2).
    Regarding (3) we observe that if nu is left chi covariant, then sigma is
    right Delta_G covariant by 2.7.8(1), hence nu_x[u(x g^{-1})] =
    sigma_x[u(x g^{-1}) chi^{-1}(x)] = chi^{-1}(g) sigma_x[u(x g^{-1})
    chi^{-1}(x g^{-1})] = chi^{-1}(g) Delta_G(g) sigma(u chi^{-1}) =
    (chi^{-1} Delta_G)(g) nu(u) whenever u in K(G) and g in G, so that nu is
    right chi^{-1} Delta_G covariant. The converse follows by use of p#."
    Here G is a locally compact Hausdorff topological group, chi is given by
    the hypotheses chi(g h) = chi(g) chi(h), chi(g) <> 0 and continuity, u
    chi^{-1} is x |-> u(x) chi(x)^{-1}, and Delta_G is any function with
    is_modular_function (ModularFunctionUP.v). The proof follows Federer.
    That sigma is a Daniell integral on K(G) is
    continuous_multiplier_daniell. "sigma+ and sigma- are nonnegative
    multiples of a left Haar integral" combines
    invariant_integral_variation_extensions (InvariantDaniellVariation.v)
    with 2.7.7 (left_haar_integral_unique): the extension of sigma+ to K(G)
    is a monotone left invariant Daniell integral, hence either zero or a
    left Haar integral. In (3), "sigma is right Delta_G covariant by
    2.7.8(1)" is applied to sigma = sigma+ - sigma- in the same way, each
    part being zero or a left Haar integral; this needs no existence of Haar
    integrals. The converse of (3) applies the direct implication to p#(nu)
    and the character Delta_G chi^{-1}; that this function is multiplicative
    follows from 2.7.1, p. 122, when nu does not vanish on K(G), and the
    case nu = 0 on K(G) is trivial. The implications from left to right in
    (1) and (2) use a left Haar integral, which exists by 2.7.5
    (left_haar_integral_exists of HaarIntegralExistence.v). The local
    erratum has no entry for pp. 126-127. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground HomeomorphismUP TopologicalGroupUP
  TopologicalGroupLaws FunctionLatticeUP DaniellIntegralUP MonotoneDaniellIntegralUP
  DaniellIntegralNegation DaniellVariationUP CompactSupportFunctionUP DaniellSpaceCompactness
  DaniellSpacePushforward CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP
  GroupMultiplicationHomogeneous EquivariantPushforward HaarInversion HaarIntegralExistence
  InvariantIntegralPositivity HaarIntegralUniqueness ModularFunctionUP DaniellContinuousMultiplier
  InvariantDaniellVariation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LeftInvariantIntegrals.
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
(** Source for [hAl]: the action 2.7.2(1), p. 122, makes G a
    homogeneous space of G. *)
Let hAl := left_multiplication_homogeneous hT.
(** Source for [hAr]: the action 2.7.2(2), p. 122, makes G a
    homogeneous space of G. *)
Let hAr := right_multiplication_homogeneous hT.

(** Source for [monotone_left_invariant_zero_or_haar]: a monotone
    Daniell integral on K(G) satisfying the left invariance identity
    vanishes on K(G) or is a left Haar integral, by the definition
    "a nonzero monotone left invariant integral ... is called a left
    Haar integral", Federer 2.7.2, p. 122. Supporting lemma for 2.7.9,
    p. 127. *)
Lemma monotone_left_invariant_zero_or_haar (B : (G -> R) -> R) :
  is_monotone_daniell_integral K B ->
  is_covariant_on K (left_multiplication_action mul) (fun _ => 1) B ->
  (forall u, K u -> B u = 0) \/ is_left_haar_integral mul B.
Proof.
move=> hm hi.
case: (pselect (exists2 u, K u & B u <> 0))=> [hn|hz]; last first.
  by left=> u hu; apply: contrapT=> h; apply: hz; exists u.
right; split=> //; split=> //; exact: monotone_daniell_is_daniell.
Qed.

(** Source for [monotone_left_invariant_multiple]: the clause "hence
    sigma+ and sigma- are nonnegative multiples of a left Haar
    integral", Federer 2.7.9, p. 127, for a monotone left invariant
    Daniell integral B on K(G): B = c lambda on K(G) with c >= 0, for a
    given left Haar integral lambda. Supporting lemma, by 2.7.7
    (left_haar_integral_unique) when B does not vanish on K(G). *)
Lemma monotone_left_invariant_multiple (B lambda : (G -> R) -> R) :
  is_left_haar_integral mul lambda -> is_monotone_daniell_integral K B ->
  is_covariant_on K (left_multiplication_action mul) (fun _ => 1) B ->
  exists2 c : R, 0 <= c & forall u, K u -> B u = c * lambda u.
Proof.
move=> hl hm hi; case: (monotone_left_invariant_zero_or_haar hm hi)=> [hz|hB].
  by exists 0=> // u hu; rewrite mul0r; exact: hz.
have [c hc hcu] := left_haar_integral_unique hGc hB hl.
by exists c=> //; exact: ltW.
Qed.

(** Source for [left_invariant_variations_haar_multiples]: "If sigma
    is left invariant, so are sigma+ and sigma-, hence sigma+ and
    sigma- are nonnegative multiples of a left Haar integral", Federer
    2.7.9, p. 127, for a left invariant integral sigma on K(G), its
    variations sigma+, sigma- on K(G)+ (2.5.5, p. 96) and a given left
    Haar integral lambda. Direct formalisation. *)
Theorem left_invariant_variations_haar_multiples (sigma lambda P0 Q0 : (G -> R) -> R) :
  is_left_invariant_integral mul sigma -> is_left_haar_integral mul lambda ->
  is_daniell_positive_variation K sigma P0 -> is_daniell_negative_variation K sigma Q0 ->
  exists a b : R, [/\ 0 <= a, 0 <= b,
    forall f, positive_function_lattice K f -> P0 f = a * lambda f &
    forall f, positive_function_lattice K f -> Q0 f = b * lambda f].
Proof.
move=> hs hl hP0 hQ0.
have [P [Q [[hPm hPi] [hQm hQi] hPQ _]]] :=
  invariant_integral_variation_extensions hG hAl hs hH hlc hP0 hQ0.
have [a ha hPa] := monotone_left_invariant_multiple hl hPm hPi.
have [b hb hQb] := monotone_left_invariant_multiple hl hQm hQi.
exists a, b; split=> // f hf.
- by rewrite -(hPQ f hf).1 hPa //; exact: hf.1.
- by rewrite -(hPQ f hf).2 hQb //; exact: hf.1.
Qed.

(** Source for [left_invariant_integral_multiple]: the conclusion
    drawn from "sigma+ and sigma- are nonnegative multiples of a left
    Haar integral" in the proof of Federer 2.7.9(1), p. 127: a left
    invariant integral sigma on K(G) is r lambda on K(G) for a real r
    and a given left Haar integral lambda. Supporting theorem;
    sigma = sigma+ - sigma- on K(G) after the extension of the
    variations. *)
Theorem left_invariant_integral_multiple (sigma lambda : (G -> R) -> R) :
  is_left_invariant_integral mul sigma -> is_left_haar_integral mul lambda ->
  exists r : R, forall u, K u -> sigma u = r * lambda u.
Proof.
move=> hs hl.
have [P [Q [hPm hPi hQm hQi hd]]] := invariant_integral_variation_decomposition hG hAl hs hH hlc.
have [a _ hPa] := monotone_left_invariant_multiple hl hPm hPi.
have [b _ hQb] := monotone_left_invariant_multiple hl hQm hQi.
by exists (a - b)=> u hu; rewrite hd // hPa // hQb // mulrBl.
Qed.

(** Source for [left_invariant_integral_right_covariant]: "then sigma
    is right Delta_G covariant by 2.7.8(1)", Federer 2.7.9, p. 127: if
    every left Haar integral is right D covariant, then so is every
    left invariant integral sigma on K(G). Supporting theorem; sigma is
    the difference of two monotone left invariant Daniell integrals,
    each zero on K(G) or a left Haar integral. The existence of Haar
    integrals is not used. *)
Theorem left_invariant_integral_right_covariant (D : G -> R) (sigma : (G -> R) -> R) :
  left_haar_right_covariant mul inv D -> is_left_invariant_integral mul sigma ->
  is_right_covariant_integral mul inv D sigma.
Proof.
move=> hD hs.
have [P [Q [hPm hPi hQm hQi hd]]] := invariant_integral_variation_decomposition hG hAl hs hH hlc.
have hcov (B : (G -> R) -> R) : is_monotone_daniell_integral K B ->
    is_covariant_on K (left_multiplication_action mul) (fun _ => 1) B ->
    is_covariant_on K (right_multiplication_action mul inv) D B.
  move=> hm hi u g hu; case: (monotone_left_invariant_zero_or_haar hm hi)=> [hz|hB].
    by rewrite !hz ?mulr0 //; exact: (compactly_supported_translate hG hAr g hu).
  exact: (covariant_integral_law (hD B hB) g hu).
constructor; first exact: covariant_integral_daniell hs.
move=> u g hu; have hug := compactly_supported_translate hG hAr g hu.
by rewrite (hd _ hug) (hd _ hu) (hcov P hPm hPi u g hu) (hcov Q hQm hQi u g hu) mulrBr.
Qed.

End LeftInvariantIntegrals.

Section CovariantWeight.
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
(** Source for [hAl]: the action 2.7.2(1), p. 122, makes G a
    homogeneous space of G. *)
Let hAl := left_multiplication_homogeneous hT.
(** Source for [hAr]: the action 2.7.2(2), p. 122, makes G a
    homogeneous space of G. *)
Let hAr := right_multiplication_homogeneous hT.
Variable nu : (G -> R) -> R.
Hypothesis hnu : is_daniell_integral K nu.
Variable chi : G -> R.
Hypothesis hchiM : forall g h, chi (mul g h) = chi g * chi h.
Hypothesis hchi0 : forall g, chi g != 0.
Hypothesis hchic : continuous (chi : G -> real_line_metric R).
(** Source for [hlin]: nu is linear on K(G), Federer 2.5.13, p. 106. *)
Let hlin := daniell_compact_support_linear hnu.

(** Source for [character_unit]: chi(e) = 1 for a homomorphism chi of
    G into the multiplicative group R ~ {0}, as in the hypothesis of
    Federer 2.7.9, p. 126. Supporting lemma. *)
Lemma character_unit : chi e = 1.
Proof.
have h := hchiM e e; rewrite (group_mul1g hG) -{1}[chi e]mulr1 in h.
exact: esym (mulfI (hchi0 e) h).
Qed.

(** Source for [character_inverse]: chi(g^{-1}) = chi(g)^{-1},
    supporting the use of p# in Federer 2.7.9, p. 127. *)
Lemma character_inverse g : chi (inv g) = (chi g)^-1.
Proof.
apply: (mulfI (hchi0 g)).
by rewrite -hchiM (group_mulgV hG) character_unit (mulfV (hchi0 g)).
Qed.

(** Source for [character_inverse_continuous]: chi^{-1} is
    continuous, as presupposed by "lambda(u chi^{-1})", Federer 2.7.9,
    p. 126. Supporting lemma. *)
Lemma character_inverse_continuous :
  continuous ((fun x => (chi x)^-1) : G -> real_line_metric R).
Proof. by move=> x; apply: (continuousV (hchi0 x)); exact: hchic. Qed.

(** Source for [covariant_weight]: "sigma(u) = nu(u chi) whenever
    u in K(G)", Federer 2.7.9, p. 127. Direct definition. *)
Definition covariant_weight : (G -> R) -> R := fun u => nu (fun x => u x * chi x).

(** Source for [covariant_weight_daniell]: sigma is a Daniell
    integral on K(G), presupposed by "sigma+ and sigma-" in Federer
    2.7.9, p. 127. Supporting lemma. *)
Lemma covariant_weight_daniell : is_daniell_integral K covariant_weight.
Proof. exact: (continuous_multiplier_daniell hH hlc hnu hchic). Qed.

(** Source for [covariant_weight_inverse]: nu(w) = sigma(w chi^{-1})
    whenever w is a function on G, the relation between nu and sigma
    used in Federer 2.7.9, p. 127. Supporting lemma. *)
Lemma covariant_weight_inverse w : nu w = covariant_weight (fun x => w x * (chi x)^-1).
Proof.
rewrite /covariant_weight; congr nu; apply: funext=> x.
by rewrite (divfK (hchi0 x)).
Qed.

(** Source for [left_covariant_weight_invariant]: "compute
    sigma(u o A_g) = nu_x[u(g x) chi(x)] = chi(g)^{-1} nu[(u chi) o A_g]
    for g in G, and infer that nu is left chi covariant if and only if
    sigma is left invariant", Federer 2.7.9, p. 127. Direct
    formalisation. *)
Theorem left_covariant_weight_invariant :
  is_left_covariant_integral mul chi nu <-> is_left_invariant_integral mul covariant_weight.
Proof.
have hdw := daniell_compact_support_linear covariant_weight_daniell.
split.
- case=> _ hc; split; first exact: covariant_weight_daniell.
  move=> u g hu; rewrite mul1r /covariant_weight.
  have huc := continuous_multiplier_member hchic hu.
  have hucg := compactly_supported_translate hG hAl g huc.
  have -> : (fun x => (u \o left_multiplication_action mul g) x * chi x) =
      (fun x => (chi g)^-1 * (((fun y => u y * chi y) \o left_multiplication_action mul g) x)).
    by apply: funext=> x; rewrite /= /left_multiplication_action hchiM mulrCA (mulKf (hchi0 g)).
  by rewrite (hlin.2 _ _ hucg) (hc _ g huc) (mulKf (hchi0 g)).
- case=> _ hs; split=> // w g hw.
  have hwc := continuous_multiplier_member character_inverse_continuous hw.
  have hwcg := compactly_supported_translate hG hAl g hwc.
  rewrite (covariant_weight_inverse (w \o _)) (covariant_weight_inverse w).
  have -> : (fun x => (w \o left_multiplication_action mul g) x * (chi x)^-1) =
      (fun x => chi g * (((fun y => w y * (chi y)^-1) \o left_multiplication_action mul g) x)).
    apply: funext=> x; rewrite /= /left_multiplication_action hchiM invfM.
    by rewrite mulrCA (mulVKf (hchi0 g)).
  by rewrite (hdw.2 _ _ hwcg) (hs _ g hwc) mul1r.
Qed.

(** Source for [left_covariant_haar_multiple]: the implication from
    left to right in Federer 2.7.9(1), p. 126, for a given left Haar
    integral lambda: if nu is left chi covariant, then
    nu(u) = r lambda(u chi^{-1}) whenever u in K(G), for some real r.
    Supporting theorem; sigma is left invariant, hence a multiple of
    lambda. *)
Theorem left_covariant_haar_multiple (lambda : (G -> R) -> R) :
  is_left_haar_integral mul lambda -> is_left_covariant_integral mul chi nu ->
  exists r : R, forall u, K u -> nu u = r * lambda (fun x => u x * (chi x)^-1).
Proof.
move=> hl hc.
have hs := left_covariant_weight_invariant.1 hc.
have [r hr] := left_invariant_integral_multiple hGc hs hl.
exists r=> u hu; rewrite covariant_weight_inverse hr //.
exact: (continuous_multiplier_member character_inverse_continuous hu).
Qed.

(** Source for [haar_multiple_left_covariant]: the implication from
    right to left in Federer 2.7.9(1), p. 126: if lambda is a left Haar
    integral, r is real and nu(u) = r lambda(u chi^{-1}) whenever
    u in K(G), then nu is left chi covariant. Supporting theorem;
    sigma = r lambda on K(G) is left invariant. *)
Theorem haar_multiple_left_covariant (lambda : (G -> R) -> R) (r : R) :
  is_left_haar_integral mul lambda ->
  (forall u, K u -> nu u = r * lambda (fun x => u x * (chi x)^-1)) ->
  is_left_covariant_integral mul chi nu.
Proof.
move=> hl hr; apply/left_covariant_weight_invariant.
have hsr w : K w -> covariant_weight w = r * lambda w.
  move=> hw; rewrite /covariant_weight hr; last exact: (continuous_multiplier_member hchic hw).
  congr (r * lambda _); apply: funext=> x; exact: (mulfK (hchi0 x)).
split; first exact: covariant_weight_daniell.
move=> w g hw; have hwg := compactly_supported_translate hG hAl g hw.
by rewrite (hsr _ hwg) (hsr _ hw) (invariant_integral_translate hl g hw) mul1r.
Qed.

(** Source for [left_covariant_haar_characterisation]: Federer
    2.7.9(1), p. 126, "nu is left chi covariant if and only if there
    exists a left Haar integral lambda and a real number r such that
    nu(u) = r lambda(u chi^{-1}) whenever u in K(G)". Direct
    formalisation; a left Haar integral exists by 2.7.5, p. 125
    (left_haar_integral_exists). *)
Theorem left_covariant_haar_characterisation :
  is_left_covariant_integral mul chi nu <->
  exists (lambda : (G -> R) -> R) (r : R), is_left_haar_integral mul lambda /\
    forall u, K u -> nu u = r * lambda (fun x => u x * (chi x)^-1).
Proof.
have [lambda hl] := left_haar_integral_exists R hGc; split.
  by move=> hc; have [r hr] := left_covariant_haar_multiple hl hc; exists lambda, r.
by case=> lambda' [r [hl' hr]]; exact: haar_multiple_left_covariant hl' hr.
Qed.

(** Source for [left_covariant_right_modular]: the implication from
    left to right in Federer 2.7.9(3), p. 127: "if nu is left chi
    covariant, then sigma is right Delta_G covariant by 2.7.8(1), hence
    nu_x[u(x g^{-1})] = ... = (chi^{-1} Delta_G)(g) nu(u) whenever
    u in K(G) and g in G, so that nu is right chi^{-1} Delta_G
    covariant". Direct formalisation for any modular function Delta;
    only 2.7.8(1) is used. *)
Theorem left_covariant_right_modular (Delta : G -> R) :
  is_modular_function mul inv Delta -> is_left_covariant_integral mul chi nu ->
  is_right_covariant_integral mul inv (fun g => Delta g * (chi g)^-1) nu.
Proof.
move=> hD hc.
have hs := left_covariant_weight_invariant.1 hc.
have [_ hsr] := left_invariant_integral_right_covariant hGc (modular_function_left_haar hD) hs.
have hdw := daniell_compact_support_linear covariant_weight_daniell.
split=> // u g hu.
have huc := continuous_multiplier_member character_inverse_continuous hu.
have hucg := compactly_supported_translate hG hAr g huc.
rewrite (covariant_weight_inverse (u \o _)) (covariant_weight_inverse u).
have -> : (fun x => (u \o right_multiplication_action mul inv g) x * (chi x)^-1) =
    (fun x => (chi g)^-1 *
      (((fun y => u y * (chi y)^-1) \o right_multiplication_action mul inv g) x)).
  apply: funext=> x.
  have hx : chi x = chi (mul x (inv g)) * chi g by rewrite -hchiM (group_mulgKV hG).
  by rewrite /= /right_multiplication_action hx invfM mulrA mulrC.
by rewrite (hdw.2 _ _ hucg) (hsr _ g huc) mulrA [(chi g)^-1 * _]mulrC.
Qed.

End CovariantWeight.

Section CovariantCharacterisation.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.
Local Notation K := (@compactly_supported_continuous_functions R G).
(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121. *)
Let hT := lch_group_topological hGc.
(** Source for [hG]: the group laws of G, Federer 2.7.1, p. 121. *)
Let hG := topological_group_laws hT.
(** Source for [hp]: "p(x) = x^{-1} for x in G", Federer 2.7.2,
    p. 123, is a homeomorphism with inverse p. *)
Let hp : is_homeomorphism_with_inverse inv inv := inversion_homeomorphism hT.
Variable nu : (G -> R) -> R.
Hypothesis hnu : is_daniell_integral K nu.
Variable chi : G -> R.
Hypothesis hchiM : forall g h, chi (mul g h) = chi g * chi h.
Hypothesis hchi0 : forall g, chi g != 0.
Hypothesis hchic : continuous (chi : G -> real_line_metric R).

(** Source for [inversion_pushforward_daniell]: p#(nu) is a Daniell
    integral on K(G), Federer 2.5.19, p. 113, as used in "by means of
    p# (see 2.7.2)", 2.7.9, p. 127. Supporting lemma. *)
Lemma inversion_pushforward_daniell : is_daniell_integral K (daniell_pushforward inv nu).
Proof.
exact: (@daniell_pushforward_daniell R G G inv (homeomorphism_continuous hp)
  (homeomorphism_with_inverse_proper hp) nu hnu).
Qed.

(** Source for [inversion_compact]: u o p belongs to K(G) whenever
    u in K(G), supporting the use of p# in Federer 2.7.9, p. 127. *)
Lemma inversion_compact u : K u -> K (u \o inv).
Proof.
exact: (@compactly_supported_compose R G G inv (homeomorphism_continuous hp)
  (homeomorphism_with_inverse_proper hp) u).
Qed.

(** Source for [right_covariant_haar_characterisation]: Federer
    2.7.9(2), p. 127, "nu is right chi covariant if and only if there
    exists a right Haar integral mu and a real number r such that
    nu(u) = r mu(u chi) whenever u in K(G)". Direct formalisation; "We
    obtain (2) from (1) by means of p#": nu is right chi covariant if and only
    if p#(nu) is left chi covariant, and mu = p#(lambda). *)
Theorem right_covariant_haar_characterisation :
  is_right_covariant_integral mul inv chi nu <->
  exists (mu : (G -> R) -> R) (r : R), is_right_haar_integral mul inv mu /\
    forall u, K u -> nu u = r * mu (fun x => u x * chi x).
Proof.
have h1 := left_covariant_haar_characterisation hGc inversion_pushforward_daniell hchiM hchi0 hchic.
have hci := character_inverse hGc hchiM hchi0.
have hinvK u : (u \o inv) \o inv = u by apply: funext=> x; rewrite /= (group_invK hG).
rewrite (right_covariant_inversion hT chi nu) h1; split.
- case=> lambda [r [hl hr]]; exists (daniell_pushforward inv lambda), r; split.
    exact: (left_haar_inversion hT lambda).1 hl.
  move=> u hu; have := hr _ (inversion_compact hu).
  rewrite /daniell_pushforward hinvK=> ->; congr (r * lambda _); apply: funext=> x.
  by rewrite /= hci.
- case=> mu [r [hr hmu]]; exists (daniell_pushforward inv mu), r; split.
    exact: (right_haar_inversion hT mu).1 hr.
  move=> w hw; rewrite /daniell_pushforward (hmu _ (inversion_compact hw)).
  congr (r * mu _); apply: funext=> x.
  by rewrite /= hci invrK.
Qed.

(** Source for [left_covariant_modular_characterisation]: Federer
    2.7.9(3), p. 127, "nu is left chi covariant if and only if nu is
    right Delta_G chi^{-1} covariant", for any modular function Delta
    of G. Direct formalisation; "The converse follows by use of p#":
    p#(nu) is left Delta chi^{-1} covariant, and the direct implication
    for the character Delta chi^{-1} shows that p#(nu) is right
    Delta (Delta chi^{-1})^{-1} = chi covariant. The character
    Delta chi^{-1} is multiplicative by 2.7.1, p. 122, unless nu
    vanishes on K(G), in which case nu is trivially left chi
    covariant. *)
Theorem left_covariant_modular_characterisation (Delta : G -> R) :
  is_modular_function mul inv Delta ->
  is_left_covariant_integral mul chi nu <->
  is_right_covariant_integral mul inv (fun g => Delta g * (chi g)^-1) nu.
Proof.
move=> hD; split; first exact: (left_covariant_right_modular hGc hnu hchiM hchi0 hchic hD).
move=> h.
case: (pselect (exists2 u, K u & nu u <> 0))=> [[u hu hu0]|hz]; last first.
  have hz0 v : K v -> nu v = 0 by move=> hv; apply: contrapT=> h0; apply: hz; exists v.
  split=> // v g hv; rewrite !hz0 ?mulr0 //.
  exact: (compactly_supported_translate hG (left_multiplication_homogeneous hT) g hv).
pose psi g := Delta g * (chi g)^-1.
have hpsiM : forall g h, psi (mul g h) = psi g * psi h.
  exact: (covariant_character_multiplicative hG (right_multiplication_homogeneous hT)
    (covariant_integral_law h) hu hu0).
have hpsi0 g : psi g != 0.
  by rewrite mulf_neq0 ?invr_eq0 ?hchi0 // gt_eqF // (modular_function_positive hD).
have hpsic : continuous (psi : G -> real_line_metric R).
  move=> x; apply: (@continuousM R G Delta (fun y => (chi y)^-1) x).
    exact: (modular_function_continuous hD).
  exact: (character_inverse_continuous hchi0 hchic).
have hl' := (right_covariant_inversion hT psi nu).1 h.
have hr' := left_covariant_right_modular hGc inversion_pushforward_daniell hpsiM hpsi0 hpsic hD hl'.
have hpe : (fun g => Delta g * (psi g)^-1) = chi.
  apply: funext=> g; have hD0 : Delta g != 0 by rewrite gt_eqF // (modular_function_positive hD).
  by rewrite /psi invfM invrK (mulVKf hD0).
rewrite hpe in hr'.
exact: (left_covariant_inversion hT chi nu).2 hr'.
Qed.

End CovariantCharacterisation.
