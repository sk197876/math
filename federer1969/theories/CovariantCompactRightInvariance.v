(** Federer (1969), 2.7.14, printed pp. 131–133, proof: "because Delta_G and
    chi map the compact subgroup S onto {1}". Let lambda be a monotone left
    chi covariant integral on K(G), G a locally compact Hausdorff
    topological group (2.7.1, p. 121, and 2.7.2, p. 122). By 2.7.9(3), p.
    127, lambda is right Delta_G chi^{-1} covariant, so that lambda_g u(g s)
    = Delta_G(s^{-1}) chi(s^{-1})^{-1} lambda(u) whenever u in K(G) and s in
    G. If S is a compact subgroup of G, the factor equals 1 for s in S, by
    the fact on compact groups quoted in 2.7.12, p. 129
    (CompactSubgroupCharacter.v). This module proves the resulting identity
    lambda_g u(g s) = lambda(u) for s in S, which is the form in which
    Federer's remark enters the proof of 2.7.14. The case in which lambda
    vanishes on K(G) is trivial; otherwise chi is a continuous homomorphism
    into R ~ {0} by 2.7.1, p. 122, and it is positive because lambda is
    monotone. The module also proves that a monotone left chi covariant
    integral which does not vanish on K(G) is positive on the nonzero
    members of K(G)+; Federer uses this fact for Haar integrals in 2.7.6, p.
    125, and it is needed in 2.7.14 for the inner regularity of open sets of
    infinite measure. The proof uses 2.7.9(1), p. 126: lambda(u) = r
    lambda_0(u chi^{-1}) for a left Haar integral lambda_0 of G. Neither.
    The local erratum has no entry for this argument; its entries for
    pp. 131–133 concern the statements and proof of 2.7.14–2.7.15. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground FunctionLatticeUP MonotoneDaniellIntegralUP
  MonotoneDaniellIntegralLaws DaniellIntegralNegation CompactSupportFunctionUP
  CompactSupportFunctionLattice CompactSupportProducts PositiveDifferenceFunctional
  TopologicalGroupUP TopologicalGroupLaws CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP
  GroupMultiplicationHomogeneous CovariantCharacterContinuity ModularFunctionUP ModularFunction
  HaarIntegralExistence InvariantIntegralPositivity CovariantHaarCharacterisation
  CompactSubgroupCharacter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CovariantCompactRightInvariance.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.
Local Notation K := (@compactly_supported_continuous_functions R G).
Variable chi : G -> R.
Variable lambda : (G -> R) -> R.
Hypothesis hl : is_monotone_daniell_integral K lambda.
Hypothesis hc : is_covariant_on K (left_multiplication_action mul) chi lambda.

(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121,
    used in this section. *)
Let hT := lch_group_topological hGc.
(** Source for [hgl]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hgl := topological_group_laws hT.
(** Source for [hAl]: G is a homogeneous space of itself under left
    multiplication, Federer 2.7.2, p. 122, used in this section. *)
Let hAl := left_multiplication_homogeneous hT.
(** Source for [hL]: K(G) is a lattice of functions, Federer 2.5.13,
    p. 106, used in this section. *)
Let hL := @compactly_supported_continuous_functions_lattice R G.

(** Source for [covariant_positive_witness]: if lambda(u) <> 0 for some
    u in K(G), then lambda(v) > 0 for some v in K(G)+; supporting the
    positivity of chi in "a continuous homomorphism of G into the
    multiplicative group of positive numbers", Federer 2.7.12, p. 129,
    as used in 2.7.14, p. 133. The proof writes u = u+ - u- (2.5.1,
    p. 91). Supporting lemma. *)
Lemma covariant_positive_witness :
  (exists u, K u /\ lambda u <> 0) -> exists v, [/\ K v, function_nonnegative v & 0 < lambda v].
Proof.
move=> [u [hu hnz]].
have [[hp hp0] [hn hn0]] := positive_parts_membership hL hu.
have hz : lambda (fun _ => 0) = 0 := monotone_daniell_integral_zero hl hu.
have hK0 : K (fun _ => 0) := @compactly_supported_zero_function R G.
have hge f : K f -> function_nonnegative f -> 0 <= lambda f.
  move=> hf hf0; rewrite -hz; exact: (monotone_daniell_integral_monotone hl hK0 hf hf0).
have he : (fun x => Order.max (- u x) 0 + u x) = (fun x => Order.max (u x) 0).
  apply: funext=> x; have h := f_equal (fun f => f x) (positive_parts_difference u).
  simpl in h; lra.
have hsplit : lambda (fun x => Order.max (u x) 0) =
    lambda (fun x => Order.max (- u x) 0) + lambda u.
  by rewrite -he; exact: (monotone_daniell_integral_add hl hn hu).
have hpn := hge _ hn hn0; have hpp := hge _ hp hp0.
have [hpos|hneg] := ltrP 0 (lambda u).
- exists (fun x => Order.max (u x) 0); split=> //.
  by rewrite hsplit; exact: ltr_wpDl.
- exists (fun x => Order.max (- u x) 0); split=> //.
  have hlt : lambda u < 0 by rewrite lt_def hneg andbT eq_sym; exact/eqP.
  have h2 : lambda (fun x => Order.max (- u x) 0) = lambda (fun x => Order.max (u x) 0) - lambda u.
    by rewrite hsplit addrK.
  by rewrite h2 subr_gt0; exact: lt_le_trans hlt hpp.
Qed.

(** Source for [covariant_character_positive]: chi(g) > 0 whenever
    g in G, for a monotone left chi covariant integral lambda which does
    not vanish on K(G), supporting "a continuous homomorphism of G into
    the multiplicative group of positive numbers", Federer 2.7.12,
    p. 129, as applied to chi in 2.7.14, p. 133: chi(g) lambda(v) =
    lambda(v o A_g) >= 0 for some v in K(G)+ with lambda(v) > 0, and
    chi(g) <> 0 by 2.7.1, p. 122. Supporting lemma. *)
Lemma covariant_character_positive : (exists u, K u /\ lambda u <> 0) -> forall g, 0 < chi g.
Proof.
move=> hnz g; have [v [hv hv0 hvp]] := covariant_positive_witness hnz.
have hz : lambda (fun _ => 0) = 0 := monotone_daniell_integral_zero hl hv.
have hK0 : K (fun _ => 0) := @compactly_supported_zero_function R G.
have hvg := compactly_supported_translate hgl hAl g hv.
have hge : 0 <= lambda (v \o left_multiplication_action mul g).
  rewrite -hz; apply: (monotone_daniell_integral_monotone hl hK0 hvg)=> x; exact: hv0.
rewrite hc // in hge.
have hne := covariant_character_nonzero hgl hAl hc hv (elimN eqP (lt0r_neq0 hvp)) g.
rewrite lt_def hne /=; rewrite -(pmulr_lge0 _ hvp); exact: hge.
Qed.

(** Source for [left_covariant_integral_positive]: a monotone left chi
    covariant integral lambda on K(G) which does not vanish on K(G)
    satisfies lambda(u) > 0 for every nonzero u in K(G)+. Supporting
    theorem, not stated by Federer, for the inner regularity of the
    open sets of infinite measure in the conclusion "alpha is a Radon
    measure" of 2.7.14, p. 131. By 2.7.9(1), p. 126, lambda(u) =
    r lambda_0(u chi^{-1}) for a left Haar integral lambda_0 (2.7.5,
    p. 125), which is positive by 2.7.6, p. 125; and r > 0 because
    lambda(v) > 0 for some v in K(G)+. *)
Theorem left_covariant_integral_positive : (exists u, K u /\ lambda u <> 0) ->
  forall u, K u -> function_nonnegative u -> (exists a, u a <> 0) -> 0 < lambda u.
Proof.
move=> hnz.
have [chiM chie chi0 chic] := covariant_character_homomorphism hT hAl (lch_group_locally_compact hGc)
  (lch_group_hausdorff hGc) (lch_group_locally_compact hGc)
  (monotone_covariant_integral hl hc) hnz.
have chip := covariant_character_positive hnz.
have [l0 hl0] := left_haar_integral_exists R hGc.
have hlD := monotone_daniell_is_daniell hl.
have [r hr] := left_covariant_haar_multiple hGc hlD chiM chi0 chic hl0 (monotone_covariant_integral hl hc).
have hinvc := character_inverse_continuous chi0 chic.
have hwK f : K f -> K (fun x => f x / chi x).
  move=> hf; have h := compact_support_continuous_multiplier hinvc hf.
  by have -> : (fun x => f x / chi x) = (fun x => (chi x)^-1 * f x) by apply: funext=> x; rewrite mulrC.
have hwpos f : K f -> function_nonnegative f -> (exists a, f a <> 0) -> 0 < l0 (fun x => f x / chi x).
  move=> hf hf0 [a ha]; apply: (left_haar_integral_positive hT hl0 (hwK f hf)).
  - by move=> x; apply: divr_ge0; [exact: hf0|exact: ltW (chip x)].
  - by exists a; apply/eqP; rewrite mulf_eq0 negb_or invr_eq0 (lt0r_neq0 (chip a)) andbT; apply/eqP.
have [v [hv hv0 hvp]] := covariant_positive_witness hnz.
have hvnz : exists a, v a <> 0.
  apply: contrapT=> hn; have hv1 : v = (fun _ => 0).
    by apply: funext=> x; apply: contrapT=> hx; apply: hn; exists x.
  by move: hvp; rewrite hv1 (monotone_daniell_integral_zero hl hv) ltxx.
have hrpos : 0 < r.
  have h1 := hwpos v hv hv0 hvnz; rewrite hr // in hvp.
  by rewrite -(pmulr_lgt0 _ h1).
move=> u hu hu0 hunz; rewrite hr //; apply: mulr_gt0=> //; exact: hwpos.
Qed.

(** Source for [left_covariant_compact_right_invariant]: "because
    Delta_G and chi map the compact subgroup S onto {1}", Federer
    2.7.14, p. 133, in the form lambda_g u(g s) = lambda(u) whenever
    u in K(G) and s in S, for a compact subgroup S of G. Direct
    formalisation of the consequence used in the proof: by 2.7.9(3),
    p. 127, lambda is right Delta_G chi^{-1} covariant, and
    Delta_G chi^{-1} is a continuous homomorphism into the positive
    numbers, which equals 1 on S (2.7.12, p. 129). *)
Theorem left_covariant_compact_right_invariant (S : set G) :
  is_subgroup mul inv e S -> compact S ->
  forall s u, S s -> K u -> lambda (fun g => u (mul g s)) = lambda u.
Proof.
move=> hS hSc s u hs hu.
have hus : K (fun g => u (mul g s)).
  have h := compactly_supported_translate hgl (right_multiplication_homogeneous hT) (inv s) hu.
  have -> : (fun g => u (mul g s)) = u \o right_multiplication_action mul inv (inv s).
    by apply: funext=> g; rewrite /= /right_multiplication_action (group_invK hgl).
  exact: h.
case: (pselect (exists u, K u /\ lambda u <> 0))=> [hnz|hz]; last first.
  have hz' f : K f -> lambda f = 0.
    by move=> hf; apply: contrapT=> hf0; apply: hz; exists f.
  by rewrite (hz' _ hu) (hz' _ hus).
have [chiM chie chi0 chic] := covariant_character_homomorphism hT hAl (lch_group_locally_compact hGc)
  (lch_group_hausdorff hGc) (lch_group_locally_compact hGc)
  (monotone_covariant_integral hl hc) hnz.
have chip := covariant_character_positive hnz.
have [D hD] := modular_function_exists R hGc.
have [DM De] := modular_function_homomorphism hGc hD.
have hlD := monotone_daniell_is_daniell hl.
have hright := left_covariant_right_modular hGc hlD chiM chi0 chic hD (monotone_covariant_integral hl hc).
pose c := fun g => D g / chi g.
have hcc : continuous (c : G -> real_line_metric R).
  have hDc := modular_function_continuous hD.
  have hinvc := character_inverse_continuous chi0 chic.
  move=> g; apply: (@continuousM R G (fun g => D g) (fun g => (chi g)^-1) g (hDc g) (hinvc g)).
have hcM g h : c (mul g h) = c g * c h.
  by rewrite /c DM chiM invfM mulrACA.
have hcp g : 0 < c g.
  by apply: divr_gt0; [exact: (modular_function_positive hD)|exact: chip].
have hc1 := compact_subgroup_positive_character_unit hgl hS hcc hcM hcp hSc.
have hlaw := covariant_integral_law hright (inv s) hu.
have -> : (fun g => u (mul g s)) = u \o right_multiplication_action mul inv (inv s).
  by apply: funext=> g; rewrite /= /right_multiplication_action (group_invK hgl).
by rewrite hlaw -/(c (inv s)) (hc1 _ (subgroup_inv hS hs)) mul1r.
Qed.

End CovariantCompactRightInvariance.
