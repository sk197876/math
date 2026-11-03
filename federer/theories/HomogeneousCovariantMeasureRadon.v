(** Federer (1969), 2.7.15, printed p. 133: "Corollary. Every chi covariant
    measure over X is a Radon measure. Proof. We readopt the hypothesis of
    2.7.10, with the additional assumption that nu is chi covariant. It
    follows from 2.7.10(6) that nu o mu^x is left chi covariant, hence from
    2.7.14 that alpha is a Radon measure. For any open subset V of X with
    compact closure, we can choose an open subset U of G with compact
    closure such that A^x(U) = V. Then the characteristic function u of U is
    alpha measurable, hence beta^x(u) is a gamma measurable function and V =
    {y: beta^x(u)(y) > 0} is gamma measurable." Here gamma is the K(X)
    regular measure associated with a monotone chi covariant integral nu on
    K(X), X a locally compact Hausdorff homogeneous space of the locally
    compact Hausdorff topological group G (2.7.1, p. 121). The point x, the
    isotropy group G^x, a left Haar integral mu of G^x (2.7.5, p. 125), the
    epimorphism mu^x of 2.7.10, the K(G) regular measure alpha associated
    with nu o mu^x, the K(G^x) regular measure beta associated with mu and
    the map beta^x of 2.7.13 are constructed in the proof. Of 2.7.14 only
    the measurability of the open sets of G with compact closure is used
    (CovariantMeasureOpenMeasurability.v). The set U is {g: f(g) > 0} cap
    (A^x)^{-1}(V) for f in K(G)+ with Clos V subset A^x{g: f(g) > 0}
    (2.7.10(5)). The equality V = {y: beta^x(u)(y) > 0} holds at the gamma
    almost all points y at which the fibre formula of 2.7.13 holds: there
    beta^x(u)(g x) = beta{s: g s in U}, and the set {s: g s in U} is open in
    G^x, nonempty for some g with g x = y if y in V, and empty for every
    such g otherwise; beta is positive on nonempty open sets (2.7.6, p.
    125). As in 2.7.14 the inner regularity of open sets of infinite measure
    requires the alternative hypothesis that nu does not vanish on K(X) or
    that X is a countable union of compact sets; it is obtained from the
    orbits of an open subgroup of G which is a countable union of compact
    sets (OpenSigmaCompactSubgroup.v) and the positivity of nu, which
    follows from 2.7.10(5), (6) and the positivity of nonzero left covariant
    integrals. The nonzero hypothesis is Federer's erratum p. 3, book
    p. 133 line 4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground FunctionLatticeUP MonotoneDaniellIntegralUP
  MonotoneDaniellIntegralLaws DaniellIntegralNegation CompactSupportFunctionUP CompactSupportFunctionLattice
  CompactSupportProducts
  CompactCutoffUP CompactCutoff LocalizedCompactCutoffUP LocalizedCompactCutoff
  FunctionLatticeLevelMeasurability FunctionLatticeRegularityUP RealIntegralFunctionalUP
  PartialFunctionUP MeasurableFunctionUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure
  MeasureIntegralUP MeasureIntegralUniqueness MeasurableFunctionBorel TopologicalBorel
  CountableOrderIntervals ExtendedRealOrderTopology SummableRealFunctionUP CharacteristicFunctionUP
  CharacteristicFunctionSealed MeasureCharacteristicIntegral CompactSupportMeasureFinite RadonMeasureUP
  CompactOpenContentUP CompactOpenContentMeasureBound TopologicalGroupUP TopologicalGroupLaws
  HomogeneousSpaceUP HomogeneousSpaceLaws CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP
  HaarIntegralLaws GroupMultiplicationHomogeneous InvariantIntegralPositivity IsotropyGroupTopology
  CosetIntegralUP
  CosetIntegralLaws CosetIntegralExistence CosetLoneIntegralUP CosetLoneClass
  CosetLoneIntegralEpimorphism CovariantCompactRightInvariance CovariantMeasureOpenMeasurability
  RegularMeasureRadonCriteria OpenSigmaCompactSubgroup CovariantMeasureRadon.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_measurable_strict_level]: the sets {y: t < h(y)}
    of a measurable real function are measurable, used for
    "V = {y: beta^x(u)(y) > 0} is gamma measurable", Federer 2.7.15,
    p. 133. Supporting lemma. *)
Lemma real_measurable_strict_level (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (hm : is_measure mu) (h : X -> R) (t : R) :
  is_measure_measurable_function mu (real_total_integrand h) -> measure_measurable mu [set y | t < h y].
Proof.
move=> hh; rewrite -real_total_strict_upper_level.
apply: (@measurable_function_borel_preimage R X (extended_real_line R) mu hm _ hh).
apply: open_borel_set; exact: order_strict_upper_ray_open.
Qed.

(** Source for [positive_integral_open_positive]: phi(V) > 0 for every
    nonempty open V when the represented integral is positive on the
    nonzero members of K(X)+, supporting the inner regularity in "is a
    Radon measure", Federer 2.7.14–2.7.15, pp. 131–133: a cutoff w with
    w(y) = 1 and spt w subset V has 0 < A(w) <= phi(V) (2.5.14,
    p. 107). Supporting lemma. *)
Lemma positive_integral_open_positive (R : realType) (X : topologicalType) (mu : set X -> \bar R)
    (A : (X -> R) -> R) : hausdorff_space X -> locally_compact [set: X] -> is_measure mu ->
  is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A ->
  (forall v, @compactly_supported_continuous_functions R X v -> function_nonnegative v ->
    (exists a, v a <> 0) -> 0 < A v) ->
  forall V, open V -> (exists y, V y) -> (0 < mu V)%E.
Proof.
move=> hX hlX hm hA hpos V hV [y hy].
have hyV : [set y] `<=` V by move=> z ->.
pose w := @localized_compact_cutoff R X [set y] V hX hlX (@compact_set1 X y) hV hyV.
have [[hwK hwr hw1] hws] := @localized_compact_cutoff_specification R X [set y] V hX hlX
  (@compact_set1 X y) hV hyV.
have hp : 0 < A w.
  apply: hpos hwK _ _.
  - by move=> z; have /andP[] := hwr z.
  - by exists y; rewrite hw1 //; exact: (elimN eqP (oner_neq0 R)).
have hle := @compact_open_test_representing_measure_bound R X mu A hm hA V w (conj hwK (conj hwr hws)).
by apply: lt_le_trans hle; rewrite lte_fin.
Qed.

Section HomogeneousCovariantMeasureRadon.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hX : hausdorff_space X.
Hypothesis hlX : locally_compact [set: X].
Local Notation KG := (@compactly_supported_continuous_functions R G).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Variable chi : G -> R.
Variable nu : (X -> R) -> R.
Hypothesis hnu : is_monotone_daniell_integral KX nu.
Hypothesis hcov : is_covariant_on KX A chi nu.
Variable gamma : set X -> \bar R.
Hypothesis hg : is_measure gamma.
Hypothesis hgrep : is_real_integral_functional gamma KX nu.
Hypothesis hgreg : is_function_lattice_regular KX gamma.

(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121,
    used in this section. *)
Let hT := lch_group_topological hGc.
(** Source for [hgl]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hgl := topological_group_laws hT.
(** Source for [hGH]: G is Hausdorff, Federer 2.7.1, p. 121, used in
    this section. *)
Let hGH := lch_group_hausdorff hGc.
(** Source for [hGl]: G is locally compact, Federer 2.7.1, p. 121, used
    in this section. *)
Let hGl := lch_group_locally_compact hGc.

Section Point.
Variable x : X.
Local Notation S := (isotropy_subgroup A x).
Local Notation KS := (@compactly_supported_continuous_functions R S).
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hR : is_subgroup_restriction mul inv e S mulS invS eS.
Hypothesis hSG : is_locally_compact_hausdorff_group mulS invS eS.
Variable mu : (S -> R) -> R.
Hypothesis hmu : is_left_haar_integral mulS mu.
Variable M : (G -> R) -> X -> R.
Hypothesis hM : is_coset_integral mul A x mu M.

(** Source for [coset_composite_monotone]: "nu o mu^x" is a monotone
    Daniell integral on K(G), Federer 2.7.10(6), p. 128, as used in
    2.7.15, p. 133. Supporting lemma. *)
Lemma coset_composite_monotone : is_monotone_daniell_integral KG (fun u => nu (M u)).
Proof. exact: (coset_integral_monotone_daniell hGc hA hX hmu hM hnu). Qed.

(** Source for [coset_composite_covariant]: "It follows from 2.7.10(6)
    that nu o mu^x is left chi covariant", Federer 2.7.15, p. 133.
    Direct formalisation. *)
Lemma coset_composite_covariant :
  is_covariant_on KG (left_multiplication_action mul) chi (fun u => nu (M u)).
Proof.
have hci := monotone_covariant_integral hnu hcov.
have h := (coset_integral_covariant hGc hA hX hR hmu hM chi (monotone_daniell_is_daniell hnu)).1 hci.
exact: covariant_integral_law h.
Qed.

(** Source for [coset_composite_nonzero]: if nu does not vanish on
    K(X), neither does nu o mu^x on K(G), since mu^x maps K(G) onto K(X)
    (2.7.10, p. 127). Supporting lemma. *)
Lemma coset_composite_nonzero : (exists v, KX v /\ nu v <> 0) -> exists u, KG u /\ nu (M u) <> 0.
Proof.
move=> [v [hv hnz]]; have [u hu hMu] := coset_integral_onto hGc hA hX hR hmu hM hv.
by exists u; rewrite hMu.
Qed.

(** Source for [homogeneous_covariant_integral_positive]: a monotone chi
    covariant integral nu on K(X) which does not vanish on K(X) satisfies
    nu(v) > 0 for every nonzero v in K(X)+. Supporting lemma, not stated
    by Federer, for the inner regularity in "Every chi covariant measure
    over X is a Radon measure", 2.7.15, p. 133: by 2.7.10(5), v = mu^x(u)
    with u = ([v/mu^x(f)] o A^x) . f in K(G)+, u <> 0, and
    nu(v) = (nu o mu^x)(u) > 0 because nu o mu^x is a nonzero monotone
    left chi covariant integral. *)
Lemma homogeneous_covariant_integral_positive : (exists v, KX v /\ nu v <> 0) ->
  forall v, KX v -> function_nonnegative v -> (exists a, v a <> 0) -> 0 < nu v.
Proof.
move=> hnz v hv hv0 [a ha].
have hlnz := coset_composite_nonzero hnz.
have [f hf hcf] := coset_integral_cover x hGc hA hv.
have [hspt hq] := coset_integral_quotient_compact hGc hA hX hR hmu hM hv hf hcf.
pose u := fun g => v (A g x) / M f (A g x) * f g.
have hMu : M u = v := coset_integral_quotient hGc hA hX hR hmu hM hv hf hcf.
have hqc : continuous ((fun g => v (A g x) / M f (A g x)) : G -> real_line_metric R).
  move=> g; apply: (@continuous_comp G X (real_line_metric R) (orbit_map A x)
    (fun y => v y / M f y) g); last exact: hq.1.
  exact: (orbit_map_continuous hA).
have hu : KG u := compact_support_continuous_multiplier hqc hf.1.
have hMf0 := coset_integral_nonnegative hGc hA hX hmu hM hf.1 hf.2.
have hu0 : function_nonnegative u.
  move=> g; apply: mulr_ge0; last exact: hf.2.
  apply: divr_ge0; [exact: hv0|exact: hMf0].
have hunz : exists g, u g <> 0.
  apply: contrapT=> hn; apply: ha.
  have [g hg'] := homogeneous_transitive hA x a.
  have hz : u = (fun _ => 0) by apply: funext=> g'; apply: contrapT=> hne; apply: hn; exists g'.
  rewrite -hMu -hg' (coset_integral_value hM g hu) hz.
  exact: (monotone_daniell_integral_zero (nonzero_invariant_integral_monotone hmu)
    (@compactly_supported_zero_function R S)).
rewrite -hMu.
exact: (left_covariant_integral_positive hGc coset_composite_monotone coset_composite_covariant hlnz hu hu0 hunz).
Qed.

Variable alpha : set G -> \bar R.
Hypothesis ha : is_measure alpha.
Hypothesis harep : is_real_integral_functional alpha KG (fun u => nu (M u)).
Hypothesis hareg : is_function_lattice_regular KG alpha.
Variable beta : set S -> \bar R.
Hypothesis hb : is_measure beta.
Hypothesis hbrep : is_real_integral_functional beta KS mu.
Variable B : (G -> R) -> X -> R.
Hypothesis hB : is_coset_lone_integral mul A x alpha beta gamma B.

(** Source for [isotropy_open_positive]: beta(W) > 0 for every
    nonempty open subset W of G^x, beta the K(G^x) regular measure
    associated with a left Haar integral mu of G^x; used for
    "V = {y: beta^x(u)(y) > 0}", Federer 2.7.15, p. 133, and resting on
    the positivity of Haar integrals (2.7.6, p. 125). Supporting lemma. *)
Lemma isotropy_open_positive (W : set S) : open W -> (exists s, W s) -> (0 < beta W)%E.
Proof.
have hTS := lch_group_topological hSG.
apply: (positive_integral_open_positive (lch_group_hausdorff hSG) (lch_group_locally_compact hSG) hb hbrep).
move=> w hw hw0 hwnz; exact: (left_haar_integral_positive hTS hmu hw hw0 hwnz).
Qed.

(** Source for [coset_section_characteristic_value]: if u is the
    characteristic function of U subset G and the fibre formula
    "beta^x(u)(g x) = integral u(g s) d beta s" of 2.7.13, p. 130, holds
    at y = g x, then beta^x(u)(y) = beta{s: g s in U}; supporting
    "V = {y: beta^x(u)(y) > 0}", Federer 2.7.15, p. 133. The set
    {s: g s in U} is beta measurable because s |-> u(g s) is beta
    measurable. Supporting lemma. *)
Lemma coset_section_characteristic_value (U : set G) (y : X) (r : R) g :
  coset_fibre_integral mul A x beta (CharacteristicFunction.value R U) y r -> A g x = y ->
  r%:E = beta [set s : S | U (mul g (set_val s))].
Proof.
move=> hfib hgy; have hi := hfib g hgy.
have [hon hoff] := @CharacteristicFunction.laws R G U.
pose c := fun s : S => CharacteristicFunction.value R U (mul g (set_val s)).
have hchar : is_characteristic_function [set s : S | U (mul g (set_val s))] c.
  by split=> s hs; [exact: hon|exact: hoff].
have hTm : measure_measurable beta [set s : S | U (mul g (set_val s))].
  have -> : [set s : S | U (mul g (set_val s))] = [set s | 2^-1 < c s].
    apply/seteqP; split=> s hs.
    - by rewrite /= /c (hon _ hs) invf_lt1 ?ltr1n // ltr0n.
    - apply: contrapT=> hn; move: hs; rewrite /= /c (hoff _ hn) ltNge invr_ge0 ler0n //.
  exact: (@real_measurable_strict_level R S beta hb c 2^-1 hi.1).
have hc := measure_characteristic_integral hb hchar hTm.
exact: (measure_integral_unique hi hc).
Qed.

(** Source for [homogeneous_open_compact_closure_measurable_at]: "For
    any open subset V of X with compact closure, we can choose an open
    subset U of G with compact closure such that A^x(U) = V. Then the
    characteristic function u of U is alpha measurable, hence beta^x(u)
    is a gamma measurable function and V = {y: beta^x(u)(y) > 0} is
    gamma measurable", Federer 2.7.15, p. 133. Direct formalisation for
    the constructed measures, with the equality of V and
    {y: beta^x(u)(y) > 0} gamma almost everywhere. *)
Lemma homogeneous_open_compact_closure_measurable_at (V : set X) :
  open V -> compact (closure V) -> measure_measurable gamma V.
Proof.
move=> hV hVc.
have hl := coset_composite_monotone.
have hlc := coset_composite_covariant.
have hinv S' : is_subgroup mul inv e S' -> compact S' ->
    forall s u, S' s -> KG u -> nu (M (fun g => u (mul g s))) = nu (M u).
  by move=> hS hSc s u hs hu; exact: (left_covariant_compact_right_invariant hGc hl hlc hS hSc hs hu).
have [hvK hvr hv1] := @compact_cutoff_specification R X (closure V) hX hlX hVc.
pose v := @compact_cutoff R X (closure V) hX hlX hVc.
have [f hf hcf] := coset_integral_cover x hGc hA hvK.
pose U := [set g | 0 < f g /\ V (A g x)].
have hUo : open U.
  apply: openI; first exact: (@real_strict_upper_level_open R G f 0 hf.1.1).
  exact: (@open_comp _ _ (orbit_map A x) V (fun g _ => orbit_map_continuous hA x g) hV).
have hUc : compact (closure U).
  apply: (subclosed_compact (@closed_closure _ _) hf.1.2); apply: closureS=> g [hgp _] hz.
  by move: hgp; rewrite hz ltxx.
have hUV : orbit_map A x @` U = V.
  apply/seteqP; split=> [_ [g [_ hgV] <-] //|y hy].
  have hyc : real_function_support v y.
    apply: subset_closure; rewrite /= /v hv1; [exact: (elimN eqP (oner_neq0 R))|exact: subset_closure].
  have [g hgp hgy] := hcf y hyc.
  by exists g=> //; split=> //; rewrite /orbit_map in hgy; rewrite hgy.
have hUm : measure_measurable alpha U.
  exact: (covariant_open_compact_closure_measurable hGc hl hinv ha harep hUo hUc).
have hUf : (alpha U < +oo)%E.
  apply: le_lt_trans (compact_support_representing_measure_compact_finite ha harep hGH hGl hUc).
  apply: (measure_mono ha); exact: subset_closure.
pose u := CharacteristicFunction.value R U.
have [_ hint] := characteristic_finite_integral ha hUm hUf.
have hid := coset_lone_integral_identity hB hint.
have hsum : summable_real_functions alpha u by exists (fine (alpha U)).
have hfib := coset_lone_integral_fibre hB hsum.
pose E := [set y | coset_fibre_integral mul A x beta u y (B u y)].
have hEV y : E y -> (V y <-> 0 < B u y).
  move=> hy; split=> hyV.
  - rewrite -hUV in hyV; have [g hgU hgy] := hyV.
    rewrite -lte_fin (coset_section_characteristic_value hy hgy).
    apply: isotropy_open_positive.
    + have hc : continuous (fun s : S => mul g (set_val s)).
        move=> s; apply: (@continuous_comp S G G set_val (mul g) s).
        * exact: (@set_type_val_continuous G S s).
        * exact: (left_translation_continuous hT g (set_val s)).
      exact: (@open_comp _ _ (fun s : S => mul g (set_val s)) U (fun s _ => hc s) hUo).
    + by exists eS; rewrite /= (subgroup_restriction_unit hR) (group_mulg1 hgl).
  - have [g hgy] := homogeneous_transitive hA x y.
    rewrite -lte_fin (coset_section_characteristic_value hy hgy) in hyV.
    have [s hs] : exists s : S, U (mul g (set_val s)).
      apply: contrapT=> hn.
      have h0 : [set s : S | U (mul g (set_val s))] = set0.
        by apply/seteqP; split=> s // hs; apply: hn; exists s.
      by move: hyV; rewrite h0 (measure_empty hb) ltxx.
    rewrite -hUV; exists (mul g (set_val s))=> //.
    by rewrite /orbit_map (isotropy_coset_orbit hA).
have hEm : measure_measurable gamma E.
  have hc := measure_null_measurable hg hfib.
  by have := measure_measurable_complement hc; rewrite setCK.
have hBm := @real_measurable_strict_level R X gamma hg (B u) 0 hid.1.
have -> : V = (E `&` [set y | 0 < B u y]) `|` (V `&` ~` E).
  apply/seteqP; split=> y.
  - move=> hy; case: (pselect (E y))=> hEy; last by right.
    by left; split=> //; apply/(hEV y hEy).
  - case=> [[hEy hpos]|[hy _]] //; exact/(hEV y hEy).
apply: (measure_measurable_union hg); first exact: (measure_measurable_intersection hg hEm hBm).
apply: (measure_null_measurable hg); apply: (measure_null_subset hg _ hfib).
by move=> y [].
Qed.

End Point.

(** Source for [homogeneous_open_compact_closure_measurable]: every open
    subset V of X with compact closure is gamma measurable, Federer
    2.7.15, p. 133. Direct formalisation; the point x, a left Haar
    integral mu of G^x (2.7.5, 2.7.10), mu^x (2.7.10), alpha, beta and
    beta^x (2.7.13) are constructed. For empty V there is nothing to
    prove. *)
Theorem homogeneous_open_compact_closure_measurable (V : set X) :
  open V -> compact (closure V) -> measure_measurable gamma V.
Proof.
move=> hV hVc; case: (pselect (exists y, V y))=> [[x _]|hn]; last first.
  apply: (measure_null_measurable hg); apply: (measure_null_subset hg _ (measure_empty hg)).
  by move=> y hy; apply: hn; exists y.
have [mulS [invS [eS [hR hSG]]]] := isotropy_group_exists x hGc hA hX.
have [mu hmu] := isotropy_left_haar_integral_exists hGc hA hX R hR.
have [M hM] := coset_integral_exists hGc hA hX hR hmu.
have hl := coset_composite_monotone hmu hM.
have hlc := coset_composite_covariant hR hmu hM.
have [alpha [_ ha harep hareg _]] := covariant_measure_exists hl hlc.
have [beta [_ hb hbrep _ _]] := nonzero_invariant_measure_exists hmu.
have [B [hB _ _ _ _]] := coset_lone_integral_epimorphism hGc hA hX hR hmu hM ha hb hg harep hareg
  hbrep hgrep hgreg.
exact: (homogeneous_open_compact_closure_measurable_at hR hSG hmu hM ha harep hb hbrep hB hV hVc).
Qed.

(** Source for [homogeneous_covariant_integral_radon]: "Every chi
    covariant measure over X is a Radon measure", Federer 2.7.15,
    p. 133, for the K(X) regular measure gamma associated with a monotone
    chi covariant integral nu on K(X). Direct formalisation with the
    added alternative hypothesis that nu does not vanish on K(X) or that
    X is a countable union of compact sets, as in 2.7.14. *)
Theorem homogeneous_covariant_integral_radon :
  (exists v, KX v /\ nu v <> 0) \/ is_sigma_compact_space X -> is_radon_measure gamma.
Proof.
move=> halt; have hrc := homogeneous_open_compact_closure_measurable.
case: halt=> [hnz|[C [hC hXC]]]; last exact: (regular_radon_sigma_compact hX hlX hg hgrep hgreg hrc hC hXC).
have [x hx] : exists x : X, True.
  have [v [hv hvz]] := hnz; apply: contrapT=> hn; apply: hvz.
  have -> : v = (fun _ => 0) by apply: funext=> y; exfalso; apply: hn; exists y.
  exact: (monotone_daniell_integral_zero hnu (@compactly_supported_zero_function R X)).
have [mulS [invS [eS [hR hSG]]]] := isotropy_group_exists x hGc hA hX.
have [mu hmu] := isotropy_left_haar_integral_exists hGc hA hX R hR.
have [M hM] := coset_integral_exists hGc hA hX hR hmu.
have hpos := homogeneous_covariant_integral_positive hR hmu hM hnz.
have [H [hH hHo [D [hD hHD]]]] := open_sigma_compact_subgroup hGc.
apply: (regular_radon_partition hX hlX hg hgrep hgreg (cell := subgroup_orbit A H)).
- by move=> y; exact: (subgroup_orbit_open hA hHo y).
- by move=> y; exact: (subgroup_orbit_self hGc hA hH y).
- by move=> y z hyz; exact: (subgroup_orbit_eq hGc hA hH hyz).
- by move=> y; exact: (subgroup_orbit_sigma_compact hA hD hHD y).
- exact: (positive_integral_open_positive hX hlX hg hgrep hpos).
- exact: hrc.
Qed.

End HomogeneousCovariantMeasureRadon.

(** Source for [homogeneous_covariant_measure_radon]: "Every chi
    covariant measure over X is a Radon measure", Federer 2.7.15, p. 133.
    Direct formalisation for is_covariant_measure, with the added
    alternative hypothesis that gamma(K) <> 0 for some compact K (which
    holds exactly when the associated integral does not vanish on K(X))
    or that X is a countable union of compact sets. *)
Theorem homogeneous_covariant_measure_radon (R : realType) (G X : topologicalType)
    (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (chi : G -> R)
    (gamma : set X -> \bar R) :
  is_locally_compact_hausdorff_group mul inv e -> is_homogeneous_space mul A ->
  hausdorff_space X -> locally_compact [set: X] -> is_covariant_measure A chi gamma ->
  (exists C, compact C /\ gamma C <> 0%E) \/ is_sigma_compact_space X -> is_radon_measure gamma.
Proof.
move=> hGc hA hX hlX [nu [hnu hcov hg hgrep hgreg]] halt.
apply: (homogeneous_covariant_integral_radon hGc hA hX hlX hnu hcov hg hgrep hgreg).
case: halt=> [[C [hC hCz]]|hs]; last by right.
left; apply: contrapT=> hn; apply: hCz.
apply: (regular_vanishing_compact_null hX hlX hg hgrep _ hC)=> u hu.
by apply: contrapT=> hu0; apply: hn; exists u.
Qed.
