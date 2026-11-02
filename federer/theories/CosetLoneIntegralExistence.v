(** Federer (1969), 2.7.13, proof, printed p. 130: "Next we follow the
    method of 2.5.3 to prove that the characteristic function of every alpha
    measurable set with finite alpha measure belongs to Phi. If w in K(G)+,
    t > 0 and u is the characteristic function of {g: w(g) > t}, then u_h =
    h^{-1}[inf{w, t+h} - inf{w, t}] increases to u as h decreases to 0, and
    Lebesgue's increasing convergence theorem implies T(u_h) increases to
    T(u) as h decreases to 0, E(u) = X, u in Phi. Similarly we treat the
    characteristic function of any set with finite alpha measure in
    F_j[K(G)], for j = 1, 2. Therefore, if u is the characteristic function
    of any set with alpha measure 0, there exists a w in Phi with w >= u and
    integral w d alpha = 0, hence T(w) and T(u) are gamma almost equal to 0,
    hence u in Phi. Moreover all alpha measurable sets with finite alpha
    measure are obtained by subtracting sets of alpha measure zero from sets
    in F_2[K(G)]. Now it becomes clear that Phi equals the class of all
    alpha summable functions with domain G, and that beta^x may be defined
    by extension of T|Phi." The widths h are the reciprocals 1/(n+1), and
    F_0, F_1, F_2 are the classes of 2.5.3, p. 94
    (FunctionLatticeLevelFamilies.v); the alpha measurable sets of finite
    measure are reduced to F_2 by the K(G) regularity of alpha. The passage
    "Now it becomes clear" is carried out by Federer's expansion 2.3.3, p.
    76, of a nonnegative alpha summable function u as the sum of r_n
    chi_{A_n} with alpha measurable sets A_n, whose partial sums increase to
    u at every point, and by u = (|u| + u)/2 - (|u| - u)/2. The extension of
    T|Phi is a choice of the representative of T(u) for every alpha summable
    u. The local erratum has no entry for pp. 130–131. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality functions
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostUP MeasurableFunctionUP
  MeasureAlmostBasic MeasureCountableClosure MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence ExtendedRealOrderLimit NonnegativeSum NonnegativeSumContinuity
  NonnegativeSumNatPrefix CharacteristicFunctionUP CharacteristicFunctionSealed SummableRealFunctionUP
  SummableRealArithmetic RealTotalCharacteristicBounds FunctionLatticeUP FunctionLatticeRamp
  FunctionLatticeLevelFamilies FunctionLatticeLevelRamps FunctionLatticeLevelMeasurability
  FunctionLatticeRegularityUP MonotoneDaniellIntegralUP RealIntegralFunctionalUP CompactSupportFunctionUP
  CompactSupportFunctionLattice WeightedCharacteristicExpansionUP WeightedCharacteristicExpansion
  PositiveVanishingWeightsSealed TopologicalGroupUP HomogeneousSpaceUP HomogeneousSpaceLaws
  IsotropyGroupTopology CosetIntegralUP CosetIntegralLaws SummableIncreasingLimits CosetLoneIntegralUP
  CosetLoneIntegralLaws CosetLoneClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CosetLoneIntegralExistence.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (x : X).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hX : hausdorff_space X.
Local Notation S := (isotropy_subgroup A x).
Local Notation KG := (@compactly_supported_continuous_functions R G).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KS := (@compactly_supported_continuous_functions R S).
Variable mu : (S -> R) -> R.
Variable M : (G -> R) -> X -> R.
Hypothesis hM : is_coset_integral mul A x mu M.
Variable nu : (X -> R) -> R.
Variables (alpha : set G -> \bar R) (beta : set S -> \bar R) (gamma : set X -> \bar R).
Hypotheses (ha : is_measure alpha) (hb : is_measure beta) (hc : is_measure gamma).
Hypothesis harep : is_real_integral_functional alpha KG (fun u => nu (M u)).
Hypothesis hareg : is_function_lattice_regular KG alpha.
Hypothesis hbrep : is_real_integral_functional beta KS mu.
Hypothesis hcrep : is_real_integral_functional gamma KX nu.
Local Notation Phi := (coset_lone_class mul A x alpha beta gamma).
Local Notation chi T := (@CharacteristicFunction.value R G T).

(** Source for [hLG]: the lattice laws of K(G), Federer 2.5.13,
    p. 106, used in this section. *)
Let hLG : is_function_lattice KG := @compactly_supported_continuous_functions_lattice R G.

Local Notation Phi_compact := (coset_lone_class_compact hG hA hX hM hc harep hbrep hcrep).
Local Notation Phi_increasing := (coset_lone_class_increasing hA ha hb hc).
Local Notation Phi_subtract := (coset_lone_class_subtract ha hb hc).

(** Source for [coset_lone_class_strict_level]: "If w in K(G)+, t > 0
    and u is the characteristic function of {g: w(g) > t}, then
    u_h = h^{-1}[inf{w, t+h} - inf{w, t}] increases to u as h decreases
    to 0, and Lebesgue's increasing convergence theorem implies T(u_h)
    increases to T(u) as h decreases to 0, E(u) = X, u in Phi",
    Federer 2.7.13, proof, p. 130, with h = 1/(n+1). Direct
    formalisation of the F_0 case. *)
Lemma coset_lone_class_strict_level w t : positive_function_lattice KG w -> 0 < t ->
  Phi (chi [set g | t < w g]).
Proof.
move=> hw ht.
have hS : function_lattice_strict_levels KG [set g | t < w g] by exists w, t; split=> //; split.
have hmeas := represented_lattice_strict_level_measurable ha harep hS.
have hfin := represented_lattice_strict_level_finite ha harep hS.
have [_ hint] := characteristic_finite_integral ha hmeas hfin.
apply: (Phi_increasing (f := fun n => real_lattice_ramp w t (t + (n.+1)%:R^-1))).
- move=> n; apply: Phi_compact.
  have hlt : t < t + (n.+1)%:R^-1 by rewrite ltrDl invr_gt0 ltr0n.
  by have [] := real_lattice_ramp_member hLG hw.1 (ltW ht) hlt.
- exact: real_lattice_reciprocal_level_ramps_increase (@CharacteristicFunction.laws R G _).
- by exists (fine (alpha [set g | t < w g])).
Qed.

(** Source for [coset_lone_class_increasing_level]: "Similarly we
    treat the characteristic function of any set with finite alpha
    measure in F_j[K(G)], for j = 1", Federer 2.7.13, proof, p. 130:
    the characteristic functions of an increasing sequence of sets of
    F_0 increase to that of its union. Direct formalisation of the
    F_1 case. *)
Lemma coset_lone_class_increasing_level V : function_lattice_increasing_levels KG V ->
  (alpha V < +oo)%E -> Phi (chi V).
Proof.
move=> hV hfin; have hmeas := represented_lattice_increasing_level_measurable ha harep hV.
have [_ hint] := characteristic_finite_integral ha hmeas hfin.
have [W [hW [hWmon hVW]]] := hV.
apply: (Phi_increasing (f := fun n => chi (W n))).
- move=> n; have [w [t [hw [ht ->]]]] := hW n; exact: coset_lone_class_strict_level.
- rewrite hVW; exact: characteristic_union_increase.
- by exists (fine (alpha V)).
Qed.

(** Source for [finite_hull_measurable]: the sets of F_2[K(G)] of
    Federer 2.5.3, p. 94, are alpha measurable, as intersections of
    sequences of alpha measurable sets of F_1 (2.1.3(2), p. 54), and have
    finite alpha measure, since alpha(A_1) < oo; supporting 2.7.13,
    proof, p. 130. Supporting lemma. *)
Lemma finite_hull_measurable W : function_lattice_finite_hulls KG alpha W ->
  measure_measurable alpha W /\ (alpha W < +oo)%E.
Proof.
move=> [V [hV [hVmon [hV0 hWV]]]]; split.
- rewrite hWV; apply: (measure_measurable_countable_intersection ha (countableP setT))=> n _.
  have h := represented_lattice_increasing_level_measurable ha harep (hV n); exact: h.
- apply: (le_lt_trans _ hV0); apply: (measure_mono ha); rewrite hWV=> g hg; exact: hg 0%N I.
Qed.

(** Source for [coset_lone_class_finite_hull]: "Similarly we treat
    the characteristic function of any set with finite alpha measure
    in F_j[K(G)], for j = 2", Federer 2.7.13, proof, p. 130: for
    W = intersection of the decreasing V_n in F_1 with
    alpha(V_1) < oo, chi_{V_1} - chi_{V_n} increases to
    chi_{V_1} - chi_W. Direct formalisation of the F_2 case. *)
Lemma coset_lone_class_finite_hull W : function_lattice_finite_hulls KG alpha W -> Phi (chi W).
Proof.
move=> hW; have [hWm hWfin] := finite_hull_measurable hW.
have [V [hV [hVmon [hV0 hWV]]]] := hW.
have hVfin n : (alpha (V n) < +oo)%E.
  exact: le_lt_trans (measure_mono ha (hVmon 0%N n (leq0n n))) hV0.
have hVm n := represented_lattice_increasing_level_measurable ha harep (hV n).
have [_ hWi] := characteristic_finite_integral ha hWm hWfin.
have [_ hV0i] := characteristic_finite_integral ha (hVm 0%N) hV0.
have hd : Phi (fun g => chi (V 0%N) g - chi W g).
  apply: (Phi_increasing (f := fun n g => chi (V 0%N) g - chi (V n) g)).
  - move=> n; apply: Phi_subtract; exact: coset_lone_class_increasing_level.
  - rewrite hWV; exact: characteristic_intersection_increase.
  - exists (fine (alpha (V 0%N)) - fine (alpha W)).
    have h := real_total_integral_subtract ha hV0i hWi; exact: h.
have h := Phi_subtract (coset_lone_class_increasing_level (hV 0%N) hV0) hd.
have -> : chi W = (fun g => chi (V 0%N) g - (chi (V 0%N) g - chi W g)).
  by apply: funext=> g; rewrite opprB addrC subrK.
exact: h.
Qed.

(** Source for [coset_lone_class_null]: "Therefore, if u is the
    characteristic function of any set with alpha measure 0, there
    exists a w in Phi with w >= u and integral w d alpha = 0, hence
    T(w) and T(u) are gamma almost equal to 0, hence u in Phi",
    Federer 2.7.13, proof, p. 130. The function w is the
    characteristic function of a set of F_2[K(G)] of measure 0
    containing the null set, which exists by K(G) regularity
    (2.5.3, p. 94). Direct formalisation. *)
Lemma coset_lone_class_null N : alpha N = 0%E -> Phi (chi N).
Proof.
move=> hN.
have hNfin : (alpha N < +oo)%E by rewrite hN ltry.
have [W [hNW [hW [hNWe hWfin]]]] := function_lattice_regular_hull hareg hNfin.
have [hWm _] := finite_hull_measurable hW.
have [hWe hWi] := characteristic_finite_integral ha hWm hWfin.
have hW0 : is_measure_integral alpha (real_total_integrand (chi W)) 0%E.
  by rewrite -hNWe hN /= in hWi.
apply: (coset_lone_class_dominated_null hA ha hb hc (coset_lone_class_finite_hull hW) hW0)=> g.
have /andP [h0 _] := characteristic_value_bounds R N g.
by rewrite h0 /=; exact: characteristic_value_le.
Qed.

(** Source for [measurable_hull_null_difference]: "all alpha
    measurable sets with finite alpha measure are obtained by
    subtracting sets of alpha measure zero from sets in F_2[K(G)]",
    Federer 2.7.13, proof, p. 130: if S is alpha measurable,
    S subset W and alpha(S) = alpha(W) < oo, then alpha(W ~ S) = 0,
    by the Caratheodory condition (2.1.2, p. 54). Supporting lemma. *)
Lemma measurable_hull_null_difference (T W : set G) : measure_measurable alpha T -> T `<=` W ->
  alpha T = alpha W -> (alpha W < +oo)%E -> alpha (W `\` T) = 0%E.
Proof.
move=> hT hTW he hWfin.
have hsplit := hT W.
have hWT : W `&` T = T by apply/seteqP; split=> g; [case|move=> h; split=> //; exact: hTW].
rewrite hWT -he in hsplit.
have hTr : alpha T = (fine (alpha T))%:E.
  by rewrite fineK // ge0_fin_numE ?(measure_nonnegative ha) // he.
have hz0 := measure_nonnegative ha (W `\` T).
move: hsplit hz0; rewrite hTr; case: (alpha (W `\` T))=> [s| |].
- move=> h _; have h' : (fine (alpha T) + s)%:E = (fine (alpha T) + 0)%:E by rewrite EFinD -h addr0.
  by have := EFin_inj h'=> /addrI ->.
- by move=> h; rewrite addey // in h.
- by [].
Qed.

(** Source for [coset_lone_class_measurable]: "the characteristic
    function of every alpha measurable set with finite alpha measure
    belongs to Phi", Federer 2.7.13, proof, p. 130: chi_T = chi_W -
    chi_{W ~ T} with W in F_2[K(G)], alpha(W ~ T) = 0. Direct
    formalisation. *)
Lemma coset_lone_class_measurable T : measure_measurable alpha T -> (alpha T < +oo)%E -> Phi (chi T).
Proof.
move=> hT hfin.
have [W [hTW [hW [hTWe hWfin]]]] := function_lattice_regular_hull hareg hfin.
have hN := measurable_hull_null_difference hT hTW hTWe hWfin.
have h := Phi_subtract (coset_lone_class_finite_hull hW) (coset_lone_class_null hN).
have -> : chi T = (fun g => chi W g - chi (W `\` T) g).
  apply: funext=> g.
  have hsT := @CharacteristicFunction.laws R G T.
  have hsW := @CharacteristicFunction.laws R G W.
  have hsN := @CharacteristicFunction.laws R G (W `\` T).
  case: (pselect (T g))=> hg.
  - rewrite (characteristic_on_set hsT hg) (characteristic_on_set hsW (hTW g hg)).
    by rewrite (characteristic_off_set hsN (fun h => h.2 hg)) subr0.
  - rewrite (characteristic_off_set hsT hg); case: (pselect (W g))=> hWg.
    + by rewrite (characteristic_on_set hsW hWg) (characteristic_on_set hsN (conj hWg hg)) subrr.
    + by rewrite (characteristic_off_set hsW hWg) (characteristic_off_set hsN (fun h => hWg h.1)) subrr.
exact: h.
Qed.

(** Source for [nat_prefix_nonnegative_sum]: the partial sums of a
    series of nonnegative real terms, Federer 2.1.1, p. 51, as finite
    sums; supporting the expansion 2.3.3, p. 76, used in 2.7.13,
    proof, p. 130. Supporting lemma. *)
Lemma nat_prefix_nonnegative_sum (c : nat -> R) N : (forall k, 0 <= c k) ->
  nonnegative_sum [set k | (k < N)%N] (fun k => (c k)%:E) = (\sum_(k < N) c k)%:E.
Proof.
move=> hc0; elim: N=> [|N ih]; first by rewrite nonnegative_sum_nat_prefix_zero big_ord0.
rewrite nonnegative_sum_nat_prefix_succ; last by move=> k; rewrite lee_fin.
by rewrite ih big_ord_recr EFinD.
Qed.

(** Source for [coset_lone_class_nonnegative]: "Now it becomes clear
    that Phi equals the class of all alpha summable functions", Federer
    2.7.13, proof, p. 130, for nonnegative u. By 2.3.3, p. 76,
    u = sum of r_n chi_{A_n} with alpha measurable A_n and positive
    weights r_n; r_n alpha(A_n) <= integral u d alpha < oo, the
    partial sums belong to Phi and increase to u at every point.
    Supporting lemma. *)
Lemma coset_lone_class_nonnegative u : summable_real_functions alpha u -> (forall g, 0 <= u g) -> Phi u.
Proof.
move=> [a hu] hu0.
pose r := @PositiveVanishingWeights.value R.
have hr := @PositiveVanishingWeights.laws R.
have hfe : is_measure_measurable_function alpha (partial_function_total (fun g => ((u g)%:E : extended_real_line R))).
  have h : is_measure_integral alpha (partial_function_total (fun g => ((u g)%:E : extended_real_line R))) a%:E.
    apply: (measure_integral_graph_equivalent _ hu)=> g z; split; first by move=> [y [<- <-]].
    by move=> <-; exists (u g).
  exact: h.1.
have hpos : forall g, (0 <= (u g)%:E)%E by move=> g; rewrite lee_fin.
have [As [ch [hexp hgreedy]]] := measurable_weighted_characteristic_expansion ha hfe hpos hr.
have hch k : ch k = chi (As k).
  apply: funext=> g; apply: (characteristic_function_unique (expansion_characteristic_laws hexp k)).
  exact: CharacteristicFunction.laws.
have hch0 k g : 0 <= ch k g by rewrite hch; have /andP [] := characteristic_value_bounds R (As k) g.
have hr0 k : 0 < r k := expansion_weights_positive hr k.
have hfin k : (alpha (As k) < +oo)%E.
  have hle := real_total_integral_level_lower_bound ha (expansion_sets_measurable hexp k) (hr0 k) hu hu0.
  have hle' : ((r k)%:E * alpha (As k) <= a%:E)%E.
    apply: hle=> g hg; have := (hgreedy k g).1 hg; rewrite lee_fin=> h.
    apply: le_trans h; rewrite lerDl; apply: sumr_ge0=> j _; apply: mulr_ge0; [exact: ltW|exact: hch0].
  move: hle'; case: (alpha (As k))=> [s| |] h.
  - exact: ltry.
  - by rewrite gt0_muley ?lte_fin // leye_eq in h.
  - by [] || rewrite ltNye.
pose P N g := \sum_(k < N) r k * ch k g.
have hP N : Phi (P N).
  elim: N=> [|N ih].
    have -> : P 0%N = (fun _ => 0) by apply: funext=> g; rewrite /P big_ord0.
    have h := coset_lone_class_zero mul ha hb hc; exact: h.
  have -> : P N.+1 = (fun g => P N g + r N * chi (As N) g).
    by apply: funext=> g; rewrite /P big_ord_recr /= hch.
  apply: (coset_lone_class_add ha hb hc ih); apply: (coset_lone_class_scale ha hb hc).
  exact: coset_lone_class_measurable (expansion_sets_measurable hexp N) (hfin N).
apply: (Phi_increasing (f := P) hP); last by exists a.
move=> g.
have hlim := @nonnegative_sum_increasing_limit R [the choiceType of (nat : Type)] setT
  (fun N => [set k | (k < N)%N]) (fun k => (r k * ch k g)%:E).
have he N : nonnegative_sum [set k | (k < N)%N] (fun k => (r k * ch k g)%:E) = (P N g)%:E.
  by apply: nat_prefix_nonnegative_sum=> k; apply: mulr_ge0; [exact: ltW|exact: hch0].
rewrite -(expansion_pointwise_sum hexp g).
have -> : (fun N => (P N g)%:E) = (fun N => nonnegative_sum [set k | (k < N)%N] (fun k => (r k * ch k g)%:E)).
  by apply: funext=> N; rewrite he.
apply: hlim.
- by move=> n m hnm k /= hk; exact: leq_trans hk hnm.
- by [].
- by move=> k _; exists k.+1=> /=.
Qed.

(** Source for [coset_lone_class_summable]: "Now it becomes clear that
    Phi equals the class of all alpha summable functions with domain
    G", Federer 2.7.13, proof, p. 130: u = (|u| + u)/2 - (|u| - u)/2
    with both terms nonnegative and alpha summable. Direct
    formalisation of the inclusion; the reverse inclusion holds by the
    definition of Phi. *)
Theorem coset_lone_class_summable u : summable_real_functions alpha u -> Phi u.
Proof.
move=> hu; have hau := summable_real_absolute ha hu.
have hp : Phi (fun g => `|u g| + u g).
  apply: coset_lone_class_nonnegative; first by have h := summable_real_add ha hau hu; exact: h.
  move=> g; rewrite -lerBlDr sub0r; have := ler_norm (- u g); by rewrite normrN.
have hq : Phi (fun g => `|u g| - u g).
  apply: coset_lone_class_nonnegative; first by have h := summable_real_subtract ha hau hu; exact: h.
  by move=> g; rewrite subr_ge0; exact: ler_norm.
have h := coset_lone_class_scale ha hb hc (2^-1) (Phi_subtract hp hq).
have -> : u = (fun g => 2^-1 * ((`|u g| + u g) - (`|u g| - u g))).
  apply: funext=> g.
  by rewrite opprB addrC addrA subrK mulrDr [2^-1 * _]mulrC -splitr.
exact: h.
Qed.

(** Source for [coset_lone_integral_exists]: "Then there exists a ...
    beta^x: L_1(alpha) -> L_1(gamma) such that, for each alpha summable
    function u, beta^x(u)(g x) = integral u(g s) d beta s whenever
    g in G, integral beta^x(u) d gamma = integral u d alpha", Federer
    2.7.13, p. 130, with "beta^x may be defined by extension of T|Phi"
    from the proof. Direct formalisation of the existence; the values
    on functions which are not alpha summable are 0. *)
Theorem coset_lone_integral_exists : exists B, is_coset_lone_integral mul A x alpha beta gamma B.
Proof.
have /choice [B hB] : forall u : G -> R, exists b : X -> R, summable_real_functions alpha u ->
    (forall a : R, is_measure_integral alpha (real_total_integrand u) a%:E ->
      is_measure_integral gamma (real_total_integrand b) a%:E) /\
    measure_almost_everywhere gamma [set y | coset_fibre_integral mul A x beta u y (b y)].
  move=> u; case: (pselect (summable_real_functions alpha u))=> hu.
  - have [b hb'] := coset_lone_class_laws (coset_lone_class_summable hu).
    by exists b.
  - by exists (fun _ => 0)=> h; exfalso; exact: hu h.
exists B; split.
- by move=> u a hu; exact: (hB u (ex_intro _ a hu)).1 a hu.
- by move=> u hu; exact: (hB u hu).2.
Qed.

(** Source for [coset_lone_integral_extends]: "mu^x = T|K(G)", Federer
    2.7.13, proof, p. 130: for u in K(G), beta^x(u) = mu^x(u) gamma
    almost everywhere, by the fibre formula and 2.7.10(1), p. 127.
    Direct formalisation. *)
Theorem coset_lone_integral_extends B : is_coset_lone_integral mul A x alpha beta gamma B ->
  forall u, KG u -> measure_almost_everywhere gamma [set y | B u y = M u y].
Proof.
move=> hB u hu.
have hs : summable_real_functions alpha u by exists (nu (M u)); have h := harep hu; exact: h.
apply: (measure_almost_everywhere_mono hc _ (coset_lone_integral_fibre hB hs))=> y /= h.
exact (coset_fibre_integral_unique hA h (coset_lone_class_compact_fibre hG hA hX hM hbrep (y := y) hu)).
Qed.

End CosetLoneIntegralExistence.
