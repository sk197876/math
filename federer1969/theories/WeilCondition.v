(** Federer (1969), 2.7.11, printed pp. 128–129: "Theorem. Suppose chi is a
    continuous homomorphism of G into the multiplicative group R ~ {0}, and
    x in X. (1) Nonzero chi covariant integrals on K(X) exist if and only if
    chi satisfies Weil's condition: chi(t) Delta_{G^x}(t) = Delta_G(t)
    whenever t in G^x. (2) Any two nonzero chi covariant integrals are
    constant real multiples of each other. Proof. We observe that (2)
    follows from 2.7.10(6), 2.7.9(1) and the fact that im mu^x = K(X). To
    prove (1) we first suppose nu is a nonzero chi covariant integral on
    K(X), infer from 2.7.10(6) that lambda = nu o mu^x is a nonzero left chi
    covariant integral on K(G), from 2.7.9(3) that lambda is right Delta_G
    chi^{-1} covariant, and choose u in K(G) so that lambda(u) <> 0. Given t
    in G^x, we define w(y) = u(y t^{-1}) for y in G, and compute mu^x(w)(g
    x) = mu_s[u(g s t^{-1})] = Delta_{G^x}(t) mu^x(u)(g x) for g in G, hence
    mu^x(w) = Delta_{G^x}(t) mu^x(u) and Delta_{G^x}(t) lambda(u) =
    lambda(w) = Delta_G(t) chi(t)^{-1} lambda(u). Next, to prove the other
    half of (1), we assume Weil's condition and use 2.7.9 to choose a left
    chi covariant and right Delta_G chi^{-1} covariant integral lambda on
    K(G). ... Therefore ker mu^x subset ker lambda, there exists a linear
    function nu: K(X) -> R with nu o mu^x = lambda, and we see from
    2.7.10(5), (6) that nu is a chi covariant integral." The standing
    hypotheses of 2.7.1, p. 121, are explicit: G is a locally compact
    Hausdorff topological group, X a locally compact Hausdorff homogeneous
    space of G. The homomorphism chi is given by chi(g h) = chi(g) chi(h),
    chi(g) <> 0 and continuity. The isotropy group G^x is the subtype of
    isotropy_subgroup A x with the restricted operations of
    IsotropyGroupTopology.v; Delta_G and Delta_{G^x} are functions
    satisfying is_modular_function (2.7.8, p. 126) for G and for G^x. A
    nonzero integral on K(X) is one which does not vanish on K(X). The left
    Haar integral mu of G^x and the epimorphism mu^x of 2.7.10 used in the
    proof exist by 2.7.5 and 2.7.10; they do not occur in the statements. In
    the sufficiency, the integral lambda of 2.7.9 is lambda(u) = lambda_0(u
    chi^{-1}) for a left Haar integral lambda_0 of G, which is left chi
    covariant by 2.7.9(1) and right Delta_G chi^{-1} covariant by 2.7.9(3);
    the rest of the argument is coset_integral_factorisation
    (CovariantIntegralFactorisation.v). In (2), "constant real multiples" is
    formalised as nu_2 = c nu_1 on K(X) for some real c <> 0. The local
    erratum has no entry for pp. 128–129. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground FunctionLatticeUP DaniellIntegralUP
  MonotoneDaniellIntegralUP DaniellIntegralNegation CompactSupportFunctionUP
  DaniellSpaceCompactness TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP
  HomogeneousSpaceLaws CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP
  GroupMultiplicationHomogeneous HaarIntegralExistence ModularFunctionUP
  DaniellContinuousMultiplier CovariantHaarCharacterisation IsotropyGroupTopology CosetIntegralUP
  CosetIntegralLaws CosetIntegralExistence CovariantIntegralFactorisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weil_condition]: "chi satisfies Weil's condition:
    chi(t) Delta_{G^x}(t) = Delta_G(t) whenever t in G^x", Federer
    2.7.11(1), p. 128, for a subset S of G (the isotropy group G^x),
    functions chi and Delta_G on G and a function Delta_S on S.
    Direct definition. *)
Definition weil_condition (R : realType) (G : Type) (S : set G) (chi DG : G -> R) (DS : S -> R) :
    Prop :=
  forall t : S, chi (set_val t) * DS t = DG (set_val t).

Section WeilCondition.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (x : X).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hX : hausdorff_space X.
Hypothesis hXl : locally_compact [set: X].
Local Notation S := (isotropy_subgroup A x).
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hR : is_subgroup_restriction mul inv e S mulS invS eS.
Variable DG : G -> R.
Hypothesis hDG : is_modular_function mul inv DG.
Variable DS : S -> R.
Hypothesis hDS : is_modular_function mulS invS DS.
Variable chi : G -> R.
Hypothesis hchiM : forall g h, chi (mul g h) = chi g * chi h.
Hypothesis hchi0 : forall g, chi g != 0.
Hypothesis hchic : continuous (chi : G -> real_line_metric R).
Local Notation KG := (@compactly_supported_continuous_functions R G).
Local Notation KX := (@compactly_supported_continuous_functions R X).

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

(** Source for [weil_condition_ratio]: Weil's condition
    chi(t) Delta_{G^x}(t) = Delta_G(t), Federer 2.7.11(1), p. 128, is
    equivalent to Delta_G(t) chi(t)^{-1} = Delta_{G^x}(t) for t in G^x,
    the form in which it enters the proof, p. 129. Supporting lemma. *)
Lemma weil_condition_ratio :
  weil_condition chi DG DS <-> forall t : S, DG (set_val t) / chi (set_val t) = DS t.
Proof.
split=> h t; first by rewrite -(h t) [chi _ * _]mulrC (mulfK (hchi0 _)).
by rewrite -(h t) mulrC (divfK (hchi0 _)).
Qed.

(** Source for [weil_condition_factorisation]: Federer 2.7.11, proof
    of the second half of (1), p. 129, for a given left Haar integral
    mu of G^x and the corresponding mu^x of 2.7.10: if chi satisfies
    Weil's condition and lambda is a left chi covariant integral on
    K(G), then lambda is right Delta_G chi^{-1} covariant by 2.7.9(3),
    and there is a chi covariant integral nu on K(X) with
    nu o mu^x = lambda on K(G). Direct formalisation through
    coset_integral_factorisation with psi = Delta_G chi^{-1}. *)
Theorem weil_condition_factorisation (mu : (S -> R) -> R) (M : (G -> R) -> X -> R)
    (lambda : (G -> R) -> R) :
  is_left_haar_integral mulS mu -> is_coset_integral mul A x mu M ->
  weil_condition chi DG DS -> is_left_covariant_integral mul chi lambda ->
  exists nu : (X -> R) -> R,
    is_covariant_integral A chi nu /\ forall u, KG u -> nu (M u) = lambda u.
Proof.
move=> hmu hM hW hlc.
have hlD := covariant_integral_daniell hlc.
have hlr := left_covariant_right_modular hG hlD hchiM hchi0 hchic hDG hlc.
have hpsic : continuous ((fun g => DG g / chi g) : G -> real_line_metric R).
  move=> g; apply: (@continuousM R G DG (fun y => (chi y)^-1) g).
    exact: (modular_function_continuous hDG).
  exact: (character_inverse_continuous hchi0 hchic).
exact: (coset_integral_factorisation hG hA hX hR hmu hM hDS hlD hpsic
  (weil_condition_ratio.1 hW) (covariant_integral_law hlr) hXl (covariant_integral_law hlc)).
Qed.

(** Source for [weil_condition_necessary]: the first half of Federer
    2.7.11(1), p. 128: if nu is a nonzero chi covariant integral on
    K(X), then chi satisfies Weil's condition. Direct formalisation
    of the proof on pp. 128–129, with mu^x(w) = Delta_{G^x}(t) mu^x(u)
    from the right Delta_{G^x} covariance of mu (2.7.8(1)). *)
Theorem weil_condition_necessary (nu : (X -> R) -> R) :
  is_covariant_integral A chi nu -> (exists2 v, KX v & nu v <> 0) -> weil_condition chi DG DS.
Proof.
move=> hnu [v0 hv0 hnv0].
have [mu hmu] := isotropy_left_haar_integral_exists hG hA hX R hR.
have [M hM] := coset_integral_exists hG hA hX hR hmu.
have hnuD := covariant_integral_daniell hnu.
have hnuL := daniell_compact_support_linear hnuD.
pose lambda := fun u => nu (M u).
have hlD : is_daniell_integral KG lambda := coset_integral_daniell hG hA hX hmu hM hnuD.
have hlc : is_left_covariant_integral mul chi lambda.
  exact: (coset_integral_covariant hG hA hX hR hmu hM chi hnuD).1 hnu.
have hlr := left_covariant_right_modular hG hlD hchiM hchi0 hchic hDG hlc.
have [u0 hu0 hMu0] := coset_integral_onto hG hA hX hR hmu hM hv0.
have hl0 : lambda u0 != 0 by rewrite /lambda hMu0; exact/eqP.
apply/weil_condition_ratio=> t.
pose w := u0 \o right_multiplication_action mul inv (set_val t).
have hw : KG w := compactly_supported_translate hgl (right_multiplication_homogeneous hT) _ hu0.
have hMw : M w = (fun y => DS t * M u0 y).
  apply: (orbit_function_eq (x := x) hA)=> g.
  rewrite (coset_integral_value hM g hw) (coset_integral_value hM g hu0).
  have hf := coset_section_compact x hG hA hX g hu0.
  rewrite -(covariant_integral_law (modular_function_left_haar hDS hmu) t hf).
  congr mu; apply: funext=> s.
  rewrite /w /= /right_multiplication_action (subgroup_restriction_mul hR).
  by rewrite (subgroup_restriction_inv hR) (group_mulA hgl).
have h1 : lambda w = DS t * lambda u0.
  by rewrite /lambda hMw (hnuL.2 _ _ (coset_integral_compact hM hu0)).
have h2 : lambda w = DG (set_val t) / chi (set_val t) * lambda u0.
  exact: (covariant_integral_law hlr (set_val t) hu0).
rewrite h2 in h1; exact: (mulIf hl0 h1).
Qed.

(** Source for [weil_condition_sufficient]: the second half of Federer
    2.7.11(1), p. 129: if chi satisfies Weil's condition, then there
    exists a nonzero chi covariant integral on K(X). Direct
    formalisation; lambda(u) = lambda_0(u chi^{-1}) for a left Haar
    integral lambda_0 of G (2.7.5) is a nonzero left chi covariant
    integral on K(G) by 2.7.9(1), and nu o mu^x = lambda. *)
Theorem weil_condition_sufficient :
  weil_condition chi DG DS ->
  exists nu : (X -> R) -> R, is_covariant_integral A chi nu /\ exists2 v, KX v & nu v <> 0.
Proof.
move=> hW.
have [mu hmu] := isotropy_left_haar_integral_exists hG hA hX R hR.
have [M hM] := coset_integral_exists hG hA hX hR hmu.
have [l0 hl0] := left_haar_integral_exists R hG.
have hl0D := monotone_daniell_is_daniell (nonzero_invariant_integral_monotone hl0).
have hci := character_inverse_continuous hchi0 hchic.
pose lambda := fun u => l0 (fun g => u g * (chi g)^-1).
have hlD : is_daniell_integral KG lambda := continuous_multiplier_daniell hH hlG hl0D hci.
have hlc : is_left_covariant_integral mul chi lambda.
  by apply: (haar_multiple_left_covariant hG hlD hchiM hchi0 hchic (r := 1) hl0)=> u hu; rewrite mul1r.
have [nu [hnu hfac]] := weil_condition_factorisation hmu hM hW hlc.
exists nu; split=> //.
have [u0 hu0 hn0] := nonzero_invariant_integral_nonzero hl0.
have hu1 : KG (fun g => u0 g * chi g) := continuous_multiplier_member hchic hu0.
exists (M (fun g => u0 g * chi g)).
  exact: (coset_integral_compact hM hu1).
rewrite hfac // /lambda.
have -> : (fun g => u0 g * chi g * (chi g)^-1) = u0.
  by apply: funext=> g; rewrite (mulfK (hchi0 g)).
exact: hn0.
Qed.

(** Source for [covariant_integral_exists_iff_weil]: Federer
    2.7.11(1), p. 128, "Nonzero chi covariant integrals on K(X) exist
    if and only if chi satisfies Weil's condition:
    chi(t) Delta_{G^x}(t) = Delta_G(t) whenever t in G^x". Direct
    formalisation. *)
Theorem covariant_integral_exists_iff_weil :
  (exists nu : (X -> R) -> R, is_covariant_integral A chi nu /\ exists2 v, KX v & nu v <> 0) <->
  weil_condition chi DG DS.
Proof.
split; last exact: weil_condition_sufficient.
by case=> nu [hnu hn]; exact: weil_condition_necessary hnu hn.
Qed.

End WeilCondition.

Section CovariantUniqueness.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (x : X).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hX : hausdorff_space X.
Variable chi : G -> R.
Hypothesis hchiM : forall g h, chi (mul g h) = chi g * chi h.
Hypothesis hchi0 : forall g, chi g != 0.
Hypothesis hchic : continuous (chi : G -> real_line_metric R).
Local Notation KG := (@compactly_supported_continuous_functions R G).
Local Notation KX := (@compactly_supported_continuous_functions R X).

(** Source for [covariant_integral_unique_multiple]: Federer
    2.7.11(2), p. 128, "Any two nonzero chi covariant integrals are
    constant real multiples of each other", with the proof "(2) follows
    from 2.7.10(6), 2.7.9(1) and the fact that im mu^x = K(X)". Direct
    formalisation: nu_2 = c nu_1 on K(X) for some real c <> 0. The
    modular functions, Weil's condition and the local compactness of X
    are not used; the isotropy group G^x with its restricted structure
    and a left Haar integral of it exist by isotropy_group_exists and
    2.7.5. *)
Theorem covariant_integral_unique_multiple (nu1 nu2 : (X -> R) -> R) :
  is_covariant_integral A chi nu1 -> is_covariant_integral A chi nu2 ->
  (exists2 v, KX v & nu1 v <> 0) -> (exists2 v, KX v & nu2 v <> 0) ->
  exists c : R, c != 0 /\ forall v, KX v -> nu2 v = c * nu1 v.
Proof.
move=> h1 h2 [v1 hv1 hn1] [v2 hv2 hn2].
have [mulS [invS [eS [hR _]]]] := isotropy_group_exists x hG hA hX.
have [mu hmu] := isotropy_left_haar_integral_exists hG hA hX R hR.
have [M hM] := coset_integral_exists hG hA hX hR hmu.
have [l0 hl0] := left_haar_integral_exists R hG.
have hmult (nu : (X -> R) -> R) : is_covariant_integral A chi nu ->
    exists r : R, forall u, KG u -> nu (M u) = r * l0 (fun g => u g / chi g).
  move=> hnu; have hnuD := covariant_integral_daniell hnu.
  have hlD := coset_integral_daniell hG hA hX hmu hM hnuD.
  have hlc := (coset_integral_covariant hG hA hX hR hmu hM chi hnuD).1 hnu.
  exact: (left_covariant_haar_multiple hG hlD hchiM hchi0 hchic hl0 hlc).
have [r1 hr1] := hmult nu1 h1.
have [r2 hr2] := hmult nu2 h2.
have hr0 (nu : (X -> R) -> R) (r : R) v : KX v -> nu v <> 0 ->
    (forall u, KG u -> nu (M u) = r * l0 (fun g => u g / chi g)) -> r != 0.
  move=> hv hn hr; apply/eqP=> hz; apply: hn.
  have [u hu <-] := coset_integral_onto hG hA hX hR hmu hM hv.
  by rewrite hr // hz mul0r.
have hr10 := hr0 nu1 r1 v1 hv1 hn1 hr1.
have hr20 := hr0 nu2 r2 v2 hv2 hn2 hr2.
exists (r2 / r1); split; first by rewrite mulf_neq0 ?invr_eq0.
move=> v hv; have [u hu <-] := coset_integral_onto hG hA hX hR hmu hM hv.
by rewrite hr1 // hr2 // mulrA (divfK hr10).
Qed.

End CovariantUniqueness.
