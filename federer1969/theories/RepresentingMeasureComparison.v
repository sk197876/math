(** Federer (1969), 2.7.16, pp. 134–135, uses repeatedly that a measure is
    determined by the integral it represents: "f_#(L^n) is a Haar measure of
    R^n, hence f_#(L^n) = chi(f) L^n", and "L^n is the unique ... Haar
    measure". By 2.7.7, p. 125, two Haar integrals are proportional; this
    module passes from proportional integrals to proportional measures
    without assuming K(X) regularity of either measure. By 2.5.3, p. 94, a
    measure phi representing a functional A on a lattice L satisfies phi{f >
    t} = lim A(ramp), so measures representing c B and B are proportional on
    the classes F0 and F1 of 2.5.3. On a locally compact Hausdorff space
    with a countable base, every open set belongs to F1 (2.5.14, p. 107).
    For Borel regular measures on a metric space covered by countably many
    open sets of finite measure, the open outer approximation of 2.2.3, p.
    61, extends the proportionality to all sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import FunctionLatticeUP FunctionLatticeRamp FunctionLatticeLevelFamilies
  FunctionLatticeLevelIntegral FunctionLatticeLevelMeasurability RealIntegralFunctionalUP
  MeasureUP MeasureBasic MeasureContinuityBelow ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum
  TopologicalBorel BorelRegularMeasureUP BorelRegularApproximation CountableOpenBaseUP
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportOpenBase
  CompactSupportMeasureFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_order_limit_scale]: supporting lemma for
    Federer 2.7.16, p. 135, with 2.1.1, p. 51: multiplication by a
    positive real number c preserves limits in the extended real line. *)
Lemma extended_order_limit_scale (R : realType) (u : nat -> \bar R) (l : \bar R) (c : R) :
  (0 < c)%R -> extended_order_limit u l -> extended_order_limit (fun n => c%:E * u n) (c%:E * l).
Proof.
move=> hc [hlo hup]; split.
- move=> a ha.
  have ha' : c^-1%:E * a < l by rewrite lte_pdivrMl.
  have [N hN] := hlo _ ha'; exists N=> n hn.
  by rewrite -lte_pdivrMl //; exact: hN.
- move=> b hb.
  have hb' : l < c^-1%:E * b by rewrite lte_pdivlMl.
  have [N hN] := hup _ hb'; exists N=> n hn.
  by rewrite -lte_pdivlMl //; exact: hN.
Qed.

Section ScaledLevels.
Variable R : realType.
Variable X : choiceType.
Variable L : set (X -> R).
Hypothesis hL : is_function_lattice L.
Variables (mu nu : set X -> \bar R) (A B : (X -> R) -> R) (c : R).
Hypotheses (hm : is_measure mu) (hn : is_measure nu).
Hypotheses (hA : is_real_integral_functional mu L A) (hB : is_real_integral_functional nu L B).
Hypothesis hc : (0 < c)%R.
Hypothesis hAB : forall f, L f -> A f = (c * B f)%R.

(** Source for [represented_scaled_strict_level]: Federer 2.5.3, p. 94,
    first display, phi{f > t} = lim h^-1 lambda[inf{f, t+h} - inf{f, t}],
    applied to measures representing c B and B; supporting Federer
    2.7.16, p. 135. The two measures are proportional on F0. *)
Lemma represented_scaled_strict_level S :
  function_lattice_strict_levels L S -> mu S = c%:E * nu S.
Proof.
move=> [f [t [hf [ht ->]]]].
have hu := represented_lattice_strict_level_integral_limit hL hm hA hf ht.
have hv := represented_lattice_strict_level_integral_limit hL hn hB hf ht.
have hv' := extended_order_limit_scale hc hv.2.
have he : (fun n => (A (real_lattice_ramp f t (t + (n.+1%:R)^-1)%R))%:E) =
    (fun n => c%:E * (B (real_lattice_ramp f t (t + (n.+1%:R)^-1)%R))%:E).
  apply: funext=> n; rewrite hAB ?EFinM //.
  have hab : (t < t + (n.+1%:R)^-1)%R by rewrite ltrDl invr_gt0 ltr0n.
  exact: (real_lattice_ramp_member hL hf.1 (ltW ht) hab).1.
rewrite he in hu; exact: extended_order_limit_unique hu.2 hv'.
Qed.

(** Source for [represented_scaled_increasing_level]: Federer 2.5.3,
    p. 94, passage from F0 to F1 by 2.1.3(4), p. 55, for measures
    representing c B and B; supporting Federer 2.7.16, p. 135. *)
Lemma represented_scaled_increasing_level S :
  function_lattice_increasing_levels L S -> mu S = c%:E * nu S.
Proof.
move=> [V [hV [hmono ->]]].
have hmu n := represented_lattice_strict_level_measurable hm hA (hV n).
have hnu n := represented_lattice_strict_level_measurable hn hB (hV n).
have hlimu := measure_continuity_below hm hmu hmono.
have hlimv := measure_continuity_below hn hnu hmono.
have hv' := extended_order_limit_scale hc hlimv.2.
have heq : (fun n => mu (V n)) = (fun n => c%:E * nu (V n)).
  apply: funext=> n; exact: represented_scaled_strict_level (hV n).
rewrite heq in hlimu; exact: extended_order_limit_unique hlimu.2 hv'.
Qed.

End ScaledLevels.

Section BorelRegularComparison.
Variable R : realType.
Variable T : pseudoMetricType R.
Variable W : nat -> set T.
Hypothesis hWo : forall k, open (W k).
Hypothesis hWT : forall x, exists k, W k x.

(** Source for [borel_regular_open_outer]: supporting lemma for Federer
    2.7.16, p. 135: a Borel regular measure covered by countably many open
    sets of finite measure is approximated from outside by open sets, by
    2.2.3, p. 61 *)
Lemma borel_regular_open_outer (mu : set T -> \bar R) :
  is_measure mu -> is_borel_regular_measure mu -> (forall k, mu (W k) < +oo) ->
  forall S (e : R), (0 < e)%R -> mu S < +oo ->
  exists V, open V /\ S `<=` V /\ mu V <= mu S + e%:E.
Proof.
move=> hm hr hfin S e he hS.
have [Bs [hSB [hBs heq]]] := borel_regular_cover hr S.
have hBm := borel_regular_borel_measurable hm hr hBs.
have hW k : open (W k) /\ mu (W k) < +oo by split; [exact: hWo|exact: hfin].
have hcover : Bs `<=` \bigcup_k W k by move=> x _; have [k hk] := hWT x; exists k.
have [O [hO [hBO hOB]]] := borel_regular_open_approximation hm hr hBm hW hcover he.
exists O; split=> //; split; first exact: subset_trans hSB hBO.
rewrite heq (hBm O).
have hOB' : O `&` Bs = Bs.
  by apply/seteqP; split=> y; [move=> []|move=> hy; split=> //; exact: hBO].
rewrite hOB'; exact: leeD (lexx _) (ltW hOB).
Qed.

(** Source for [borel_regular_open_scaled]: supporting lemma for
    Federer 2.7.16, p. 135: two Borel regular measures with mu = c nu on
    open sets, both finite on the covering open sets W_k, satisfy
    mu = c nu, by the open outer approximation of 2.2.3, p. 61. *)
Lemma borel_regular_open_scaled (mu nu : set T -> \bar R) (c : R) :
  is_measure mu -> is_measure nu -> is_borel_regular_measure mu -> is_borel_regular_measure nu ->
  (forall k, mu (W k) < +oo) -> (forall k, nu (W k) < +oo) -> (0 < c)%R ->
  (forall V, open V -> mu V = c%:E * nu V) -> forall S, mu S = c%:E * nu S.
Proof.
move=> hm hn hrm hrn hfm hfn hc hV S.
have hc0 : (0 : \bar R) < c%:E by rewrite lte_fin.
apply/eqP; rewrite eq_le; apply/andP; split.
- have [hfin|hinf] := ltP (nu S) +oo; last first.
    by move: hinf; rewrite leye_eq=> /eqP ->; rewrite gt0_muley ?leey.
  apply/lee_addgt0Pr=> e he.
  have hec : (0 < e / c)%R by rewrite divr_gt0.
  have [V [hVo [hSV hVle]]] := borel_regular_open_outer hn hrn hfn hec hfin.
  apply: le_trans (measure_mono hm hSV) _; rewrite (hV V hVo).
  have hle : c%:E * nu V <= c%:E * (nu S + (e / c)%:E).
    by rewrite lee_pmul2l ?fin_numE //.
  apply: (le_trans hle).
  have hfn' : nu S \is a fin_num by rewrite ge0_fin_numE ?(measure_nonnegative hn).
  rewrite muleDr ?fin_num_adde_defl // -EFinM mulrCA divff ?mulr1 //; exact: lt0r_neq0.
- have [hfin|hinf] := ltP (mu S) +oo; last first.
    by move: hinf; rewrite leye_eq=> /eqP ->; rewrite leey.
  apply/lee_addgt0Pr=> e he.
  have [V [hVo [hSV hVle]]] := borel_regular_open_outer hm hrm hfm he hfin.
  apply: le_trans hVle; rewrite (hV V hVo) lee_pmul2l ?fin_numE //.
  exact: (@measure_mono R T nu hn _ _ hSV).
Qed.

End BorelRegularComparison.

Section RepresentedComparison.
Variable R : realType.
Variable T : pseudoMetricType R.
Hypothesis hh : hausdorff_space T.
Hypothesis hl : locally_compact [set: T].
Variable U : nat -> set T.
Hypothesis hU : is_countable_open_base U.
Variable W : nat -> set T.
Hypothesis hWo : forall k, open (W k).
Hypothesis hWc : forall k, exists2 C, compact C & W k `<=` C.
Hypothesis hWT : forall x, exists k, W k x.
Local Notation K := (@compactly_supported_continuous_functions R T).

(** Source for [represented_borel_regular_scaled]: supporting theorem
    for Federer 2.7.16, p. 135, "f_#(L^n) is a Haar measure of R^n, hence
    f_#(L^n) = chi(f) L^n": on a locally compact Hausdorff metric space
    with a countable base, covered by countably many open sets with
    compact closure, two Borel regular measures representing c B and B
    on K(T) satisfy mu = c nu. Neither measure is assumed K(T) regular;
    the proof combines 2.5.3, p. 94, 2.5.14, p. 107, and 2.2.3, p. 61. *)
Theorem represented_borel_regular_scaled (mu nu : set T -> \bar R) (A B : (T -> R) -> R) (c : R) :
  is_measure mu -> is_measure nu -> is_borel_regular_measure mu -> is_borel_regular_measure nu ->
  is_real_integral_functional mu K A -> is_real_integral_functional nu K B ->
  (0 < c)%R -> (forall f, K f -> A f = (c * B f)%R) -> forall S, mu S = c%:E * nu S.
Proof.
move=> hm hn hrm hrn hA hB hc hAB.
have hL := @compactly_supported_continuous_functions_lattice R T.
have hfin (phi : set T -> \bar R) (C : (T -> R) -> R) : is_measure phi ->
    is_real_integral_functional phi K C -> forall k, phi (W k) < +oo.
  move=> hphi hC k; have [D hD hWD] := hWc k.
  apply: le_lt_trans (measure_mono hphi hWD) _.
  exact: compact_support_representing_measure_compact_finite hphi hC hh hl D hD.
apply: (borel_regular_open_scaled hWo hWT hm hn hrm hrn (hfin _ _ hm hA) (hfin _ _ hn hB) hc).
move=> V hV.
have hlev := @compact_support_open_is_increasing_level R T U hh hl hU V hV.
exact: (represented_scaled_increasing_level hL hm hn hA hB hc hAB hlev).
Qed.

End RepresentedComparison.
