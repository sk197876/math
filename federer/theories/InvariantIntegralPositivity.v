(** Federer (1969), 2.7.6, printed p. 125: "If we choose any particular
    nonzero v in K(G)+, we can use the equation in (1) to define a positive
    continuous function k on G ... However k is uniquely characterized by
    (2)". Both assertions use a property of Haar integrals which Federer
    does not state: a nonzero monotone invariant integral mu on K(X), for a
    homogeneous space X of G (2.7.1, p. 121), satisfies mu(u) > 0 for every
    nonzero u in K(X)+. For the proof let u in K(X)+, a in X with u(a) > 0,
    and c = u(a)/2. Since the action is transitive, the open sets {x :
    u(A(g,x)) > c}, g in G, cover X; finitely many of them, for g in a
    finite set D, cover the support of a given w in K(X). With s = sum_{g in
    D} u o A_g and M = sup im |w| one has |w| <= (M/c) s, hence |mu(w)| <=
    (M/c) card(D) mu(u) by the invariance and the monotonicity of mu.
    Therefore mu(u) = 0 would imply mu = 0 on K(X). If moreover X is a
    locally compact Hausdorff space, then a continuous real function f on X
    is determined by the values mu(f u), u in K(X): if mu(f1 u) = mu(f2 u)
    for u in K(X) and d = f1(b) - f2(b) <> 0, then f = d (f1 - f2) is
    positive at b, and a cutoff function u in K(X)+ with u(b) = 1 and
    support in {x : f(x) > 0} (2.5.13-2.5.14, pp. 106-108) gives mu(f u) >
    0, whereas mu(f u) = d (mu(f1 u) - mu(f2 u)) = 0. The statements are
    specialised to left and right Haar integrals of a topological group
    (2.7.2, p. 122). *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground TopologicalGroupUP HomogeneousSpaceUP
  HomogeneousSpaceLaws FunctionLatticeUP MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws
  DaniellIntegralNegation CompactSupportFunctionUP CompactSupportFunctionLattice
  CompactSupportUniformBound CompactSupportProducts DaniellSpaceCompactness DaniellFiniteSums
  CompactFiniteCover LocalizedCompactCutoff CovariantIntegralUP CovariantIntegralLaws
  HaarIntegralUP GroupMultiplicationHomogeneous.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section InvariantPositivity.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hG : is_group_laws mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Variable mu : (X -> R) -> R.
Hypothesis hmu : is_nonzero_monotone_invariant_integral A mu.
Local Notation K := (@compactly_supported_continuous_functions R X).
(** Source for [hL]: the lattice laws of K(X), Federer 2.5.13, p. 106,
    used in this section. *)
Let hL : is_function_lattice K := @compactly_supported_continuous_functions_lattice R X.
(** Source for [hK0]: the zero function belongs to K(X), Federer
    2.5.13, p. 106, used in this section. *)
Let hK0 : K (fun _ => 0) := @compactly_supported_zero_function R X.
(** Source for [hm]: mu is a monotone Daniell integral on K(X), part of
    "a nonzero monotone ... invariant integral", Federer 2.7.2, p. 122. *)
Let hm := nonzero_invariant_integral_monotone hmu.

(** Source for [invariant_integral_translate]: the invariance
    mu(u o A_g) = mu(u) whenever u in K(X), g in G, Federer 2.7.1,
    p. 122, with chi(g) = 1. Supporting lemma. *)
Lemma invariant_integral_translate u g : K u -> mu (u \o A g) = mu u.
Proof.
move=> hu; rewrite (covariant_integral_law (nonzero_invariant_integral_invariant hmu) g hu).
exact: mul1r.
Qed.

(** Source for [invariant_integral_domination]: supporting lemma for
    the positivity of Haar integrals used in Federer 2.7.6, p. 125: if
    u in K(X)+ and u(a) > 0, then for every w in K(X) there is
    C >= 0 with |mu(w)| <= C mu(u). The constant is (M/c) card(D),
    where c = u(a)/2, M bounds |w|, and the sets {x : u(A(g,x)) > c},
    g in D, cover the support of w. *)
Lemma invariant_integral_domination u a w :
  K u -> function_nonnegative u -> 0 < u a -> K w ->
  exists2 C : R, 0 <= C & `|mu w| <= C * mu u.
Proof.
move=> hu hu0 ha hw.
pose c := u a / 2.
have hc : 0 < c by rewrite /c divr_gt0.
pose U g := [set x | c < u (A g x)].
have hU g : open (U g).
  have hcont : continuous ((u \o A g) : X -> real_line_metric R).
    exact: (compactly_supported_translate hG hA g hu).1.
  exact: ((continuousP _).1 hcont _ (@open_gt R c)).
have hcov : real_function_support w `<=` cover [set: G] U.
  move=> x _; have [g hg] := homogeneous_transitive hA x a.
  by exists g=> //; rewrite /U /= hg /c ltr_pdivrMr // ltr_pMr // ltr1n.
have [D _ hD] := compact_open_finite_cover hw.2 (fun g _ => hU g) hcov.
pose s x := \sum_(g <- D) (u \o A g) x.
have huA : forall g, g \in D -> K (u \o A g).
  by move=> g _; exact (compactly_supported_translate hG hA g hu).
have hs : K s := function_lattice_sequence_sum hL hK0 huA.
have hmus : mu s = (\sum_(g <- D) 1) * mu u.
  rewrite /s (monotone_daniell_sequence_sum hL hm hK0 huA) mulr_suml.
  by apply: eq_bigr=> g _; rewrite mul1r; exact: invariant_integral_translate.
have [M [hM hwM]] := compact_support_uniform_bound hw.
have hMc : 0 <= M / c by rewrite divr_ge0 // ltW.
have hs0 x : 0 <= s x by rewrite /s; apply: sumr_ge0=> g _; exact: hu0.
have hbound x : `|w x| <= M / c * s x.
  case: (pselect (real_function_support w x))=> hx.
  - have [g hg hgx] := hD x hx.
    have hle : u (A g x) <= s x.
      exact: (@finite_nonnegative_real_sum_term R G D (fun g => u (A g x)) g hg (fun i _ => hu0 _)).
    apply: le_trans (hwM x) _.
    have hcs : c <= s x by apply: le_trans hle; exact: ltW hgx.
    have hh : M / c * c <= M / c * s x by rewrite ler_wpM2l.
    by rewrite divfK ?gt_eqF in hh.
  - by rewrite (real_function_zero_off_support hx) normr0; exact: mulr_ge0 hMc (hs0 x).
have hMs : K (fun x => M / c * s x) := compactly_supported_scale (M / c) hs.
have hle1 : mu w <= mu (fun x => M / c * s x).
  apply: (monotone_daniell_integral_monotone hm hw hMs)=> x.
  exact: le_trans (ler_norm _) (hbound x).
have hle2 : mu (fun x => - w x) <= mu (fun x => M / c * s x).
  apply: (monotone_daniell_integral_monotone hm (compactly_supported_opp hw) hMs)=> x.
  by apply: le_trans (hbound x); rewrite -normrN; exact: ler_norm.
rewrite (daniell_compact_support_opp (monotone_daniell_is_daniell hm) hw) in hle2.
rewrite (monotone_daniell_integral_scale hm hMc hs) hmus mulrA in hle1 hle2.
exists (M / c * \sum_(g <- D) 1).
  by apply: mulr_ge0 hMc _; apply: sumr_ge0=> g _; exact: ler01.
by rewrite ler_norml hle1 andbT lerNl.
Qed.

(** Source for [nonzero_invariant_integral_positive]: a nonzero
    monotone invariant integral mu on K(X) satisfies mu(u) > 0 for every
    nonzero u in K(X)+. Supporting theorem for "a positive continuous
    function k", Federer 2.7.6, p. 125, not stated by Federer: by
    invariant_integral_domination, mu(u) = 0 would give mu(w) = 0 for
    all w in K(X), contrary to "nonzero", 2.7.2, p. 122. *)
Theorem nonzero_invariant_integral_positive u :
  K u -> function_nonnegative u -> (exists a, u a <> 0) -> 0 < mu u.
Proof.
move=> hu hu0 [a ha].
have hpa : 0 < u a by rewrite lt_def (hu0 a) andbT; apply/eqP.
have hge : 0 <= mu u.
  rewrite -(monotone_daniell_integral_zero hm hu).
  exact: (monotone_daniell_integral_monotone hm hK0 hu).
rewrite lt_def hge andbT; apply/eqP=> h0.
have [w hw hw0] := nonzero_invariant_integral_nonzero hmu.
have [C hC hb] := invariant_integral_domination hu hu0 hpa hw.
rewrite h0 mulr0 normr_le0 in hb.
by apply: hw0; apply/eqP.
Qed.

Hypothesis hX : hausdorff_space X.
Hypothesis hlX : locally_compact [set: X].

(** Source for [nonzero_invariant_integral_multiplier_unique]: a
    continuous function f on X is determined by the values mu(f u),
    u in K(X). Supporting theorem for "k is uniquely characterized by
    (2)", Federer 2.7.6, p. 125, and for "hence f = f o A_g^{-1}",
    2.7.7, p. 126; Federer does not state it. The proof uses a cutoff
    function of 2.5.13-2.5.14, pp. 106-108, and
    nonzero_invariant_integral_positive. *)
Theorem nonzero_invariant_integral_multiplier_unique (f1 f2 : X -> R) :
  continuous (f1 : X -> real_line_metric R) -> continuous (f2 : X -> real_line_metric R) ->
  (forall u, K u -> mu (fun x => f1 x * u x) = mu (fun x => f2 x * u x)) -> f1 = f2.
Proof.
move=> h1 h2 hf; apply: funext=> b; apply: contrapT=> hb.
pose d := f1 b - f2 b.
pose f x := d * (f1 x - f2 x).
have hfc : continuous (f : X -> real_line_metric R).
  move=> x; apply: (@continuousM R X (fun _ => d) (fun x => f1 x - f2 x) x); first exact: cvg_cst.
  exact: (@continuousB R R^o X f1 f2 x (h1 x) (h2 x)).
have hfb : 0 < f b.
  have hd : d != 0 by rewrite /d subr_eq0; apply/eqP.
  by rewrite /f -/d -expr2 exprn_even_gt0.
pose V := [set x | 0 < f x].
have hV : open V := (continuousP _).1 hfc _ (@open_gt R 0).
have hbV : [set b] `<=` V by move=> x ->.
pose phi := localized_compact_cutoff R hX hlX (@compact_set1 X b) hV hbV.
have [[hphi hphi01 hphi1] hphiV] := localized_compact_cutoff_specification R hX hlX
  (@compact_set1 X b) hV hbV.
rewrite -/phi in hphi hphi01 hphi1 hphiV.
have hfphi : K (fun x => f x * phi x) := compact_support_continuous_multiplier hfc hphi.
have hfphi0 : function_nonnegative (fun x => f x * phi x).
  move=> x; case: (pselect (real_function_support phi x))=> hx.
  - by apply: mulr_ge0; [exact: ltW (hphiV x hx)|exact: (andP (hphi01 x)).1].
  - by rewrite (real_function_zero_off_support hx) mulr0.
have hpos := nonzero_invariant_integral_positive hfphi hfphi0.
have hnz : exists a, f a * phi a <> 0.
  by exists b; rewrite (hphi1 b erefl) mulr1; apply/eqP; rewrite gt_eqF.
have hd := monotone_daniell_is_daniell hm.
have hlin := daniell_compact_support_linear hd.
have hf1 : K (fun x => f1 x * phi x) := compact_support_continuous_multiplier h1 hphi.
have hf2 : K (fun x => f2 x * phi x) := compact_support_continuous_multiplier h2 hphi.
have hf2n : K (fun x => - (f2 x * phi x)) := compactly_supported_opp hf2.
have hsum : K (fun x => f1 x * phi x + - (f2 x * phi x)) := function_lattice_add hL hf1 hf2n.
have he : (fun x => f x * phi x) = (fun x => d * (f1 x * phi x + - (f2 x * phi x))).
  by apply: funext=> x; rewrite /f -mulrA [(f1 x - f2 x) * _]mulrBl.
have := hpos hnz.
rewrite he (hlin.2 d _ hsum) (hlin.1 _ _ hf1 hf2n) (daniell_compact_support_opp hd hf2).
by rewrite (hf phi hphi) subrr mulr0 ltxx.
Qed.

End InvariantPositivity.

Section HaarPositivity.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hT : is_topological_group mul inv e.
Local Notation K := (@compactly_supported_continuous_functions R G).
(** Source for [hG]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hG := topological_group_laws hT.

(** Source for [left_haar_integral_positive]: a left Haar integral
    lambda of G, Federer 2.7.2, p. 122, satisfies lambda(u) > 0 for
    every nonzero u in K(G)+. Supporting corollary for 2.7.6, p. 125. *)
Corollary left_haar_integral_positive (lambda : (G -> R) -> R) u :
  is_left_haar_integral mul lambda -> K u -> function_nonnegative u -> (exists a, u a <> 0) ->
  0 < lambda u.
Proof.
move=> hl; exact: (nonzero_invariant_integral_positive hG (left_multiplication_homogeneous hT) hl).
Qed.

(** Source for [right_haar_integral_positive]: a right Haar integral
    mu of G, Federer 2.7.2, p. 122, satisfies mu(u) > 0 for every
    nonzero u in K(G)+. Supporting corollary for 2.7.6, p. 125. *)
Corollary right_haar_integral_positive (mu : (G -> R) -> R) u :
  is_right_haar_integral mul inv mu -> K u -> function_nonnegative u -> (exists a, u a <> 0) ->
  0 < mu u.
Proof.
move=> hr; exact: (nonzero_invariant_integral_positive hG (right_multiplication_homogeneous hT) hr).
Qed.

Hypothesis hH : hausdorff_space G.
Hypothesis hlc : locally_compact [set: G].

(** Source for [left_haar_multiplier_unique]: for a left Haar integral
    lambda of G, a continuous function f on G is determined by the
    values lambda(f u), u in K(G). Supporting corollary for "hence
    f = f o A_g^{-1}", Federer 2.7.7, p. 126. *)
Corollary left_haar_multiplier_unique (lambda : (G -> R) -> R) (f1 f2 : G -> R) :
  is_left_haar_integral mul lambda ->
  continuous (f1 : G -> real_line_metric R) -> continuous (f2 : G -> real_line_metric R) ->
  (forall u, K u -> lambda (fun x => f1 x * u x) = lambda (fun x => f2 x * u x)) -> f1 = f2.
Proof.
move=> hl; have hA := left_multiplication_homogeneous hT.
exact: (nonzero_invariant_integral_multiplier_unique hG hA hl hH hlc).
Qed.

(** Source for [right_haar_multiplier_unique]: for a right Haar
    integral mu of G, a continuous function f on G is determined by
    the values mu(f u), u in K(G). Supporting corollary for "k is
    uniquely characterized by (2)", Federer 2.7.6, p. 125. *)
Corollary right_haar_multiplier_unique (mu : (G -> R) -> R) (f1 f2 : G -> R) :
  is_right_haar_integral mul inv mu ->
  continuous (f1 : G -> real_line_metric R) -> continuous (f2 : G -> real_line_metric R) ->
  (forall u, K u -> mu (fun x => f1 x * u x) = mu (fun x => f2 x * u x)) -> f1 = f2.
Proof.
move=> hr; have hA := right_multiplication_homogeneous hT.
exact: (nonzero_invariant_integral_multiplier_unique hG hA hr hH hlc).
Qed.

End HaarPositivity.
