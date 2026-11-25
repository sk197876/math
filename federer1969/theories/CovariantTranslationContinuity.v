(** Federer (1969), 2.7.18, printed p. 141: "If gamma is a chi covariant
    measure over X, v in L_1(gamma) and h in G, then int |v(gx) - v(hx)|
    dgamma x -> 0 as G contains g -> h. In fact, given epsilon > 0 we can
    choose w in K(X) with int |v - w| dgamma < epsilon and infer that, for
    every g in G, |v_g - v_h| <= |w_g - w_h| + |v - w|_g + |v - w|_h, int
    |v_g - v_h| dgamma <= int |w_g - w_h| dgamma + chi(g) epsilon + chi(h)
    epsilon; moreover chi(h) -> chi(g) and int |w_g - w_h| dgamma -> 0 as g
    -> h, because spt w is compact and w is uniformly continuous." The
    erratum (docs/references/ federer-erratum.tex, entry for p. 141 line 25)
    corrects "chi(h) -> chi(g)" to "chi(g) -> chi(h)". Here gx = A(g,x) and
    u_g = u o A_g as in 2.7.1, p. 122; L_1(gamma) is total_scalar_lp gamma 1
    of 2.5.7, p. 98 (as corrected in the erratum for p. 98), and int |f|
    dgamma is its seminorm finite_total_scalar_lp_norm gamma 1 f, which is
    the integral of |f| by total_scalar_lone_absolute_integral. The limit is
    the MathComp filter limit along the neighbourhoods of h in G. The proof
    follows Federer. The density of K(X) in L_1(gamma) is 2.5.3, p. 94,
    through regular_positive_lattice_lone_dense, applied to the positive and
    negative parts of v. The identity int |v - w|_g dgamma = chi(g) int |v -
    w| dgamma is covariant_translation_lone (CovariantMeasureImage.v); it
    requires chi(g) > 0. If the monotone integral mu associated with gamma
    is not 0, then chi is positive by covariant_character_positive and
    continuous by covariant_character_continuous (2.7.1, p. 122). If mu = 0,
    then chi is arbitrary, but gamma is also 1 covariant, and the argument
    is applied to the character 1. The convergence of int |w_g - w_h| dgamma
    = mu(|w_g - w_h|) is proved as the continuity of chi in
    CovariantCharacterContinuity.v: for g in a compact neighbourhood N of h,
    w_g - w_h vanishes outside the compact set {A(k^{-1}, y) : k in N, y in
    spt w}, on which it is uniformly small for g near h. Of the standing
    hypotheses of section 2.7 only those used are assumed: G is a
    topological group whose space is locally compact, X is a locally compact
    Hausdorff space, and A is a homogeneous action; G need not be Hausdorff.
    The corollary covariant_translation_continuity_lch restates the result
    under the standing hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground TopologicalProductMaps TopologicalGroupUP
  HomogeneousSpaceUP FunctionLatticeUP FunctionLatticeRegularityUP VectorFunctionLattice
  LatticeDominatedDifference MonotoneDaniellIntegralUP DaniellIntegralNegation
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactUniformNorm CompactSectionUniform
  CompactDaniellUniformBound RealIntegralFunctionalUP MeasureUP MeasureIntegralUP
  MeasureIntegralUniqueness SummableRealFunctionUP TotalScalarLpUP TotalScalarLpClosure
  TotalScalarLpLattice TotalScalarLpFiniteSeminorm FunctionLatticeSeminormUP
  FunctionSeminormDistance TotalScalarPairing RegularLatticeLoneDensity CovariantIntegralUP
  CovariantIntegralLaws CovariantCharacterContinuity CovariantMeasureImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [regular_vector_lattice_lone_dense]: "given
    epsilon > 0 we can choose w in K(X) with int |v - w| dgamma <
    epsilon", Federer 2.7.18, p. 141, by the density of L in L_1(phi)
    for an L regular measure phi representing a functional on L,
    2.5.3, p. 94. Supporting lemma: the positive density
    regular_positive_lattice_lone_dense is applied to max(v,0) and
    max(-v,0) for a vector lattice L. *)
Lemma regular_vector_lattice_lone_dense (R : realType) (X : choiceType) (L : set (X -> R))
    (F : (X -> R) -> R) (gamma : set X -> \bar R) (v : X -> R) (eta : R) :
  is_vector_function_lattice L -> is_measure gamma -> is_real_integral_functional gamma L F ->
  is_function_lattice_regular L gamma -> total_scalar_lp gamma 1 v -> 0 < eta ->
  exists w, L w /\ finite_total_scalar_lp_norm gamma 1 (fun x => v x - w x) < eta.
Proof.
move=> hV hm hF hr hv heta.
have hD := regular_positive_lattice_lone_dense hV.1 hm hF hr.
pose vp := fun x => Order.max (v x) 0.
pose vn := fun x => Order.max (-1 * v x) 0.
have hvp : total_scalar_lp gamma 1 vp := total_scalar_lp_positive_part hm hv.
have hvn : total_scalar_lp gamma 1 vn :=
  total_scalar_lp_positive_part hm (total_scalar_lp_scale hm (-1) hv).
have heta2 : 0 < eta / 2 by rewrite divr_gt0.
have hvp0 : positive_function_lattice (total_scalar_lp gamma 1) vp.
  by split=> // x; rewrite /vp le_max lexx orbT.
have hvn0 : positive_function_lattice (total_scalar_lp gamma 1) vn.
  by split=> // x; rewrite /vn le_max lexx orbT.
have [w1 [[hw1 _] h1]] := hD vp hvp0 (eta / 2) heta2.
have [w2 [[hw2 _] h2]] := hD vn hvn0 (eta / 2) heta2.
rewrite /function_seminorm_distance in h1 h2.
exists (fun x => w1 x - w2 x); split; first exact: (vector_function_lattice_difference hV hw1 hw2).
have hl1 := total_scalar_lp_subtract hm hvp (represented_lattice_in_total_lone hm hF hw1).
have hl2 := total_scalar_lp_subtract hm hvn (represented_lattice_in_total_lone hm hF hw2).
have hl3 := total_scalar_lp_scale hm (-1) hl2.
have hS := finite_total_scalar_lp_norm_laws hm 1.
have he : (fun x => v x - (w1 x - w2 x)) = (fun x => (vp x - w1 x) + -1 * (vn x - w2 x)).
  apply: funext=> x.
  have hpn : vp x - vn x = v x.
    by rewrite /vp /vn; case: (leP (v x) 0)=> hp0; case: (leP (-1 * v x) 0)=> hn0; lra.
  lra.
rewrite he; apply: le_lt_trans (function_seminorm_triangle hS hl1 hl3) _.
rewrite (function_seminorm_scale hS (-1) hl2) normrN1 mul1r.
lra.
Qed.

Section TranslationContinuity.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hT : is_topological_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hlG : locally_compact [set: G].
Hypothesis hX : hausdorff_space X.
Hypothesis hlX : locally_compact [set: X].
Local Notation K := (@compactly_supported_continuous_functions R X).
(** Source for [hG]: the group laws of the topological group G,
    Federer 2.7.1, p. 121, used in this section. *)
Let hG := topological_group_laws hT.

(** Source for [covariant_measure_positive_character]: a chi covariant
    measure gamma is c covariant for a continuous character c with
    c(g) > 0 for g in G, Federer 2.7.1, p. 122: if the associated
    integral mu is not 0, then c = chi is positive and continuous; if
    mu = 0, then c = 1. Supporting lemma for "chi(g) -> chi(h)" in
    2.7.18, p. 141 (erratum, p. 141 line 25). *)
Lemma covariant_measure_positive_character (chi : G -> R) (gamma : set X -> \bar R) :
  is_covariant_measure A chi gamma ->
  exists c : G -> R, [/\ is_covariant_measure A c gamma, forall g, 0 < c g &
    continuous (c : G -> real_line_metric R)].
Proof.
move=> [mu [hmono hc hm hi hr]].
case: (pselect (exists u, K u /\ mu u <> 0))=> hne.
- exists chi; split.
  + by exists mu; split.
  + exact: (covariant_character_positive hG hA hmono hc hne).
  + exact: (covariant_character_continuous hT hA hlG hX hlX
      (monotone_covariant_integral hmono hc) hne).
- have h0 : forall u, K u -> mu u = 0.
    by move=> u hu; apply/eqP/negPn/negP=> /eqP hu0; apply: hne; exists u.
  exists (fun _ => 1); split.
  + exists mu; split=> //.
    move=> u g hu; rewrite mul1r (h0 u hu).
    exact: (h0 _ (compactly_supported_translate hG hA g hu)).
  + by move=> g; exact: ltr01.
  + by move=> g; exact: cvg_cst.
Qed.

(** Source for [compact_translation_lone_small]: "int |w_g - w_h|
    dgamma -> 0 as g -> h, because spt w is compact and w is uniformly
    continuous", Federer 2.7.18, p. 141, for w in K(X) and a measure
    gamma representing a monotone Daniell integral mu on K(X). Here
    int |w_g - w_h| dgamma = mu(|w_g - w_h|); the bound of 2.5.13 for
    functions vanishing outside a fixed compact set and the uniform
    continuity of (x,g) |-> w(A(g,x)) on compact sets are applied as in
    the proof of the continuity of chi (CovariantCharacterContinuity.v). *)
Lemma compact_translation_lone_small (mu : (X -> R) -> R) (gamma : set X -> \bar R)
    (w : X -> R) (h : G) (eps : R) :
  is_monotone_daniell_integral K mu -> is_measure gamma -> is_real_integral_functional gamma K mu ->
  K w -> 0 < eps ->
  \forall g \near h, finite_total_scalar_lp_norm gamma 1 (fun x => w (A g x) - w (A h x)) < eps.
Proof.
move=> hmono hm hi hw heps.
have hd := monotone_daniell_is_daniell hmono.
have [N hN [hNc _]] := @hlG h I; rewrite withinET in hN.
have hh0 : N h := nbhs_singleton hN.
pose C := (fun p : G * X => A (inv p.1) p.2) @` (N `*` real_function_support w).
have hAc : continuous (fun q : G * X => A q.1 q.2) := homogeneous_action_continuous hA.
have hinvc : continuous (fun p : G * X => A (inv p.1) p.2).
  have h1 := @first_factor_map_continuous G G X inv (topological_group_inv_continuous hT).
  by move=> p; have := continuous_comp (h1 p) (@hAc (inv p.1, p.2)); exact.
have hCc : compact C.
  apply: continuous_compact; first exact: continuous_subspaceT.
  exact: (compact_setX hNc hw.2).
have [M [hM hbound]] := @compact_daniell_fixed_support_bound R X mu C hX hlX hCc hd.
have hM1 : 0 < M + 1 by rewrite ltr_wpDl.
pose d := eps / (M + 1).
have hdpos : 0 < d by rewrite /d divr_gt0.
pose k := fun p : X * G => w (A p.2 p.1).
have hk : continuous (k : X * G -> real_line_metric R).
  have hsw : continuous (fun p : X * G => (p.2, p.1)).
    by apply: topological_pair_continuous;
      [exact: second_projection_continuous|exact: first_projection_continuous].
  move=> p; have h1 := continuous_comp (hsw p) (@hAc (p.2, p.1)).
  by have := continuous_comp h1 (hw.1 (A p.2 p.1)); exact.
have [V [hVo [hVh hVu]]] := @compact_sections_locally_uniform R X G k C h d hk hCc hdpos.
have hVN : nbhs h (V `&` N) by apply: filterI=> //; exact: open_nbhs_nbhs.
apply: (filterS _ hVN)=> g [hgV hgN].
have hwg := compactly_supported_translate hG hA g hw.
have hwh := compactly_supported_translate hG hA h hw.
pose f := fun x => w (A g x) - w (A h x).
have hf : K f.
  exact: (vector_function_lattice_difference (@compact_support_vector_lattice R X) hwg hwh).
have hfa : K (fun x => `|f x|).
  exact: (lattice_absolute_difference_member (compactly_supported_continuous_functions_lattice R X)
    hwg hwh).
have hfz : forall x, ~ C x -> `|f x| = 0.
  move=> x hx.
  rewrite /f (translate_support_bound hT hA hgN hx).
  by rewrite (translate_support_bound hT hA hh0 hx) subrr normr0.
have hfe : forall x, C x -> `| `|f x| | <= d.
  by move=> x hx; rewrite normr_id; apply: ltW; exact: (hVu g x hgV hx).
have hb := hbound _ hfa hfz d hdpos hfe.
have hL1 : total_scalar_lp gamma 1 f := represented_lattice_in_total_lone hm hi hf.
have hNi := total_scalar_lone_absolute_integral hm hL1.
have hmi := hi _ hfa.
have he : finite_total_scalar_lp_norm gamma 1 f = mu (fun x => `|f x|).
  by have := measure_integral_unique hNi hmi=> -[].
rewrite -/f he; apply: le_lt_trans (ler_norm _) _; apply: le_lt_trans hb _.
have hlt : d * M < d * (M + 1) by rewrite ltr_pM2l // ltrDl ltr01.
by rewrite /d divfK ?gt_eqF // in hlt.
Qed.

(** Source for [covariant_translation_continuity]: Federer 2.7.18,
    p. 141: "If gamma is a chi covariant measure over X,
    v in L_1(gamma) and h in G, then int |v(gx) - v(hx)| dgamma x -> 0
    as G contains g -> h." Direct formalisation. The first two
    assertions record that the integrals exist: v o A_g belongs to
    L_1(gamma), and int |v(gx) - v(hx)| dgamma x is the L_1 seminorm
    of v o A_g - v o A_h. The proof follows Federer, with the
    correction "chi(g) -> chi(h)" of the erratum for p. 141 line 25. *)
Theorem covariant_translation_continuity (chi : G -> R) (gamma : set X -> \bar R) (v : X -> R)
    (h : G) :
  is_covariant_measure A chi gamma -> total_scalar_lp gamma 1 v ->
  [/\ forall g, total_scalar_lp gamma 1 (v \o A g),
    forall g, is_measure_integral gamma (real_total_integrand (fun x => `|v (A g x) - v (A h x)|))
      (finite_total_scalar_lp_norm gamma 1 (fun x => v (A g x) - v (A h x)))%:E &
    (fun g => finite_total_scalar_lp_norm gamma 1 (fun x => v (A g x) - v (A h x))) @ h --> (0 : R)].
Proof.
move=> hcov hv.
have [c [[mu [hmono hc hm hi hr]] hcpos hccont]] := covariant_measure_positive_character hcov.
have htr g (u : X -> R) : total_scalar_lp gamma 1 u ->
    total_scalar_lp gamma 1 (u \o A g) /\
    finite_total_scalar_lp_norm gamma 1 (u \o A g) = c g * finite_total_scalar_lp_norm gamma 1 u.
  exact: (covariant_translation_lone hG hA hc hm hi hr (hcpos g)).
have hvg g : total_scalar_lp gamma 1 (v \o A g) := (htr g v hv).1.
have hdiff g : total_scalar_lp gamma 1 (fun x => v (A g x) - v (A h x)).
  exact: (total_scalar_lp_subtract hm (hvg g) (hvg h)).
split=> //; first by move=> g; exact: (total_scalar_lone_absolute_integral hm (hdiff g)).
have hS := finite_total_scalar_lp_norm_laws hm 1.
apply/(@cvgr0Pnorm_lt R R^o)=> eps heps.
have hch := hcpos h.
have hc1 : 0 < 2 * c h + 1 by rewrite ltr_wpDl ?ltr01 // mulr_ge0 // ltW.
pose eta := eps / 2 / (2 * c h + 1).
have heta : 0 < eta by rewrite /eta !divr_gt0.
have hetaE : eta * (2 * c h + 1) = eps / 2 by rewrite /eta divfK ?gt_eqF.
have [w [hw hvw]] := regular_vector_lattice_lone_dense (@compact_support_vector_lattice R X) hm hi hr
  hv heta.
have hw1 : total_scalar_lp gamma 1 w := represented_lattice_in_total_lone hm hi hw.
have hvw1 : total_scalar_lp gamma 1 (fun x => v x - w x) := total_scalar_lp_subtract hm hv hw1.
have hvw0 : 0 <= finite_total_scalar_lp_norm gamma 1 (fun x => v x - w x).
  exact: (function_seminorm_nonnegative hS hvw1).
have hnear1 : \forall g \near h, ball (c h : real_line_metric R) 1 (c g).
  exact: (cvg_ball (hccont h) ltr01).
have heps2 : 0 < eps / 2 by rewrite divr_gt0.
have hnear2 := @compact_translation_lone_small mu gamma w h (eps / 2) hmono hm hi hw heps2.
apply: (filterS2 _ _ hnear1 hnear2)=> g hcg hwg.
have hcg1 : c g < c h + 1.
  by move: hcg; rewrite /ball /= ltr_norml=> /andP [hc1' hc2']; lra.
have hwgh : total_scalar_lp gamma 1 (fun x => w (A g x) - w (A h x)).
  apply: (represented_lattice_in_total_lone hm hi).
  exact: (vector_function_lattice_difference (@compact_support_vector_lattice R X)
    (compactly_supported_translate hG hA g hw) (compactly_supported_translate hG hA h hw)).
have [hvwg hNg] := htr g _ hvw1.
have [hvwh hNh] := htr h _ hvw1.
have hsc := total_scalar_lp_scale hm (-1) hvwh.
have hsum := total_scalar_lp_add hm hvwg hsc.
have hdec : (fun x => v (A g x) - v (A h x)) =
    (fun x => (w (A g x) - w (A h x)) +
      (((fun y => v y - w y) \o A g) x + -1 * ((fun y => v y - w y) \o A h) x)).
  by apply: funext=> x /=; lra.
have hN0 := function_seminorm_nonnegative hS (hdiff g).
rewrite ger0_norm // hdec.
apply: le_lt_trans (function_seminorm_triangle hS hwgh hsum) _.
have ht2 := function_seminorm_triangle hS hvwg hsc.
rewrite (function_seminorm_scale hS (-1) hvwh) normrN1 mul1r hNg hNh in ht2.
have hb1 : (c g + c h) * finite_total_scalar_lp_norm gamma 1 (fun x => v x - w x) <=
    (2 * c h + 1) * eta.
  apply: le_trans (ler_wpM2r hvw0 (ltW (_ : c g + c h < 2 * c h + 1))) _.
    lra.
  by rewrite ler_wpM2l ?ltW.
lra.
Qed.

End TranslationContinuity.

(** Source for [covariant_translation_continuity_lch]: Federer 2.7.18,
    p. 141, under the standing hypotheses of section 2.7, 2.7.1,
    p. 121: G is a locally compact Hausdorff topological group and X is
    a locally compact Hausdorff homogeneous space of G. Direct
    formalisation, as a corollary of covariant_translation_continuity. *)
Corollary covariant_translation_continuity_lch (R : realType) (G X : topologicalType)
    (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (chi : G -> R)
    (gamma : set X -> \bar R) (v : X -> R) (h : G) :
  is_locally_compact_hausdorff_group mul inv e -> is_homogeneous_space mul A ->
  hausdorff_space X -> locally_compact [set: X] ->
  is_covariant_measure A chi gamma -> total_scalar_lp gamma 1 v ->
  [/\ forall g, total_scalar_lp gamma 1 (v \o A g),
    forall g, is_measure_integral gamma (real_total_integrand (fun x => `|v (A g x) - v (A h x)|))
      (finite_total_scalar_lp_norm gamma 1 (fun x => v (A g x) - v (A h x)))%:E &
    (fun g => finite_total_scalar_lp_norm gamma 1 (fun x => v (A g x) - v (A h x))) @ h --> (0 : R)].
Proof.
move=> hGl hA hX hlX hcov hv.
exact: (covariant_translation_continuity (lch_group_topological hGl) hA
  (lch_group_locally_compact hGl) hX hlX h hcov hv).
Qed.
