(** Federer (1969), 2.7.13, proof, printed p. 130: "With each u: G -> R we
    associate T(u): E(u) = {g x: integral u(g s) d beta s in R} -> R, T(u)(g
    x) = integral u(g s) d beta s whenever g x in E(u). We consider the
    class Phi of those functions u for which gamma[X ~ E(u)] = 0 and
    integral T(u) d gamma = integral u d alpha in R. Referring to 2.7.10 we
    see that K(G) subset Phi and mu^x = T|K(G)." This module defines Phi and
    proves its closure properties used in "the method of 2.5.3": Phi
    contains K(G), is a vector space, is closed under increasing limits with
    alpha summable limit (Lebesgue's increasing convergence theorem, 2.4.7,
    p. 84, applied on each coset and on X), and contains every function v
    with 0 <= v <= w for some w in Phi with integral w d alpha = 0 ("hence
    T(w) and T(u) are gamma almost equal to 0"). The function T(u) is
    represented by a gamma summable function b on X which satisfies the
    fibre formula at gamma almost all points; this avoids the choice of a
    representative g of each point g x. Here gamma represents nu on K(X),
    beta represents mu on K(G^x), and alpha represents nu o mu^x on K(G)
    (2.5.2, p. 92); the regularity of the three measures is not used in this
    module. The functions of the sequences below increase at every point of
    G, as in the printed proof, so that the increasing convergence theorem
    applies on every coset g G^x. The local erratum has no entry for pp.
    130–131. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality functions
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralUniqueness MeasureCharacteristicIntegral ExtendedRealOrderLimit
  ExtendedIncreasingLimitSupremum CharacteristicFunctionUP CharacteristicFunctionSealed
  SummableRealFunctionUP SummableRealArithmetic LatticeL1ApproximationLaws
  RealIntegralIncreasingContinuity FunctionLatticeUP MonotoneDaniellIntegralUP RealIntegralFunctionalUP
  CompactSupportFunctionUP TopologicalGroupUP HomogeneousSpaceUP HomogeneousSpaceLaws IsotropyGroupTopology
  CosetIntegralUP CosetIntegralLaws SummableIncreasingLimits CosetLoneIntegralUP CosetLoneIntegralLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coset_lone_class]: "We consider the class Phi of those
    functions u for which gamma[X ~ E(u)] = 0 and integral T(u)
    d gamma = integral u d alpha in R", Federer 2.7.13, proof, p. 130.
    Definition: u is alpha summable with integral a, and some gamma
    summable function b with integral a satisfies the fibre formula
    integral u(g s) d beta s = b(g x) at gamma almost all points g x;
    b is T(u) extended by 0 off E(u). *)
Definition coset_lone_class (R : realType) (G X : topologicalType) (mul : G -> G -> G)
    (A : G -> X -> X) (x : X) (alpha : set G -> \bar R) (beta : set (isotropy_subgroup A x) -> \bar R)
    (gamma : set X -> \bar R) : set (G -> R) :=
  [set u | exists (a : R) (b : X -> R), [/\ is_measure_integral alpha (real_total_integrand u) a%:E,
    is_measure_integral gamma (real_total_integrand b) a%:E &
    measure_almost_everywhere gamma [set y | coset_fibre_integral mul A x beta u y (b y)]]].

Arguments coset_lone_class [R G X] mul A x alpha beta gamma.

Section CharacteristicSequences.
Variable R : realType.
Variable T : Type.
Local Notation chi S := (@CharacteristicFunction.value R T S).

(** Source for [characteristic_value_bounds]: a characteristic
    function takes the values 0 and 1, Federer 2.2.14, p. 70;
    supporting 2.7.13, p. 130. Supporting lemma. *)
Lemma characteristic_value_bounds (S : set T) t : 0 <= chi S t <= 1.
Proof.
have hs := @CharacteristicFunction.laws R T S.
case: (pselect (S t))=> h.
- by rewrite (characteristic_on_set hs h) ler01 lexx.
- by rewrite (characteristic_off_set hs h) lexx ler01.
Qed.

(** Source for [characteristic_value_le]: S subset S' implies
    chi_S <= chi_S', Federer 2.2.14, p. 70; supporting "there exists a
    w in Phi with w >= u", 2.7.13, p. 130. Supporting lemma. *)
Lemma characteristic_value_le (S S' : set T) t : S `<=` S' -> chi S t <= chi S' t.
Proof.
move=> hSS; have hs := @CharacteristicFunction.laws R T S.
have hs' := @CharacteristicFunction.laws R T S'.
case: (pselect (S t))=> h.
- by rewrite (characteristic_on_set hs h) (characteristic_on_set hs' (hSS t h)).
- by rewrite (characteristic_off_set hs h); have /andP [] := characteristic_value_bounds S' t.
Qed.

(** Source for [eventually_constant_increases]: a nondecreasing real
    sequence which is eventually equal to c increases to c, Federer
    2.1.1, p. 51; supporting 2.7.13, p. 130. Supporting lemma. *)
Lemma eventually_constant_increases (u : nat -> R) c :
  (forall n m, (n <= m)%N -> u n <= u m) -> (exists N, forall n, (N <= n)%N -> u n = c) ->
  extended_increases_to (fun n => (u n)%:E) c%:E.
Proof.
move=> hmon [N hN]; split=> [n m hnm|]; first by rewrite lee_fin; exact: hmon.
by split=> [b hb|b hb]; exists N=> n hn; rewrite hN.
Qed.

(** Source for [characteristic_union_increase]: the characteristic
    functions of an increasing sequence of sets increase to the
    characteristic function of the union, as used for the sets of F_1
    in Federer 2.7.13, p. 130 ("Similarly we treat ... F_j[K(G)]"),
    with F_1 from 2.5.3, p. 94. Supporting lemma. *)
Lemma characteristic_union_increase (V : nat -> set T) :
  (forall n m, (n <= m)%N -> V n `<=` V m) ->
  real_functions_increase_to (fun n => chi (V n)) (chi (\bigcup_(n in setT) V n)).
Proof.
move=> hV t; apply: eventually_constant_increases.
  by move=> n m hnm; apply: characteristic_value_le; exact: hV.
have hU := @CharacteristicFunction.laws R T (\bigcup_(n in setT) V n).
case: (pselect ((\bigcup_(n in setT) V n) t))=> h.
- have [N _ hN] := h; exists N=> n hn.
  have hs := @CharacteristicFunction.laws R T (V n).
  by rewrite (characteristic_on_set hs (hV N n hn t hN)) (characteristic_on_set hU h).
- exists 0%N=> n _; have hs := @CharacteristicFunction.laws R T (V n).
  rewrite (characteristic_off_set hU h) (characteristic_off_set hs) // => hn.
  by apply: h; exists n.
Qed.

(** Source for [characteristic_intersection_increase]: for a
    decreasing sequence V of sets, chi_{V_0} - chi_{V_n} increases to
    chi_{V_0} - chi_W with W the intersection, as used for the sets of
    F_2 in Federer 2.7.13, p. 130, with F_2 from 2.5.3, p. 94.
    Supporting lemma. *)
Lemma characteristic_intersection_increase (V : nat -> set T) :
  (forall n m, (n <= m)%N -> V m `<=` V n) ->
  real_functions_increase_to (fun n t => chi (V 0%N) t - chi (V n) t)
    (fun t => chi (V 0%N) t - chi (\bigcap_(n in setT) V n) t).
Proof.
move=> hV t; apply: eventually_constant_increases.
  by move=> n m hnm; rewrite lerD2l lerN2; apply: characteristic_value_le; exact: hV.
have hI := @CharacteristicFunction.laws R T (\bigcap_(n in setT) V n).
case: (pselect ((\bigcap_(n in setT) V n) t))=> h.
- exists 0%N=> n _; have hs := @CharacteristicFunction.laws R T (V n).
  by rewrite (characteristic_on_set hI h) (characteristic_on_set hs (h n I)).
- have [N hN] : exists N, ~ V N t.
    apply: contrapT=> hn; apply: h=> n _; apply: contrapT=> hn'; apply: hn; by exists n.
  exists N=> n hn; have hs := @CharacteristicFunction.laws R T (V n).
  rewrite (characteristic_off_set hI h) (characteristic_off_set hs) // => hvn.
  exact: hN (hV N n hn t hvn).
Qed.

End CharacteristicSequences.

Section CharacteristicIntegrals.
Variable R : realType.
Variable T : choiceType.
Variable phi : set T -> \bar R.
Hypothesis hphi : is_measure phi.
Local Notation chi S := (@CharacteristicFunction.value R T S).

(** Source for [characteristic_finite_integral]: the characteristic
    function of a phi measurable set S with phi(S) < oo is phi
    summable with integral phi(S), Federer 2.4.5, p. 83; supporting
    "the characteristic function of every alpha measurable set with
    finite alpha measure", 2.7.13, p. 130. Supporting lemma. *)
Lemma characteristic_finite_integral (S : set T) : measure_measurable phi S -> (phi S < +oo)%E ->
  phi S = (fine (phi S))%:E /\ is_measure_integral phi (real_total_integrand (chi S)) (fine (phi S))%:E.
Proof.
move=> hS hfin.
have he : phi S = (fine (phi S))%:E.
  by rewrite fineK // ge0_fin_numE // (measure_nonnegative hphi).
split=> //; rewrite -he.
have h := measure_characteristic_integral hphi (@CharacteristicFunction.laws R T S) hS; exact: h.
Qed.

End CharacteristicIntegrals.

Section CosetLoneClass.
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
Hypothesis hbrep : is_real_integral_functional beta KS mu.
Hypothesis hcrep : is_real_integral_functional gamma KX nu.
Local Notation Phi := (coset_lone_class mul A x alpha beta gamma).

(** Source for [coset_lone_class_compact_fibre]: "mu^x = T|K(G)",
    Federer 2.7.13, proof, p. 130, with 2.7.10(1), p. 127: for u in
    K(G) the function s |-> u(g s) belongs to K(G^x), and its beta
    integral is mu_s[u(g s)] = mu^x(u)(g x), at every point g x.
    Supporting lemma. *)
Lemma coset_lone_class_compact_fibre u y : KG u -> coset_fibre_integral mul A x beta u y (M u y).
Proof.
move=> hu g hg; rewrite -hg (coset_integral_value hM g hu).
have h := hbrep (coset_section_compact x hG hA hX g hu); exact: h.
Qed.

(** Source for [coset_lone_class_compact]: "Referring to 2.7.10 we see
    that K(G) subset Phi", Federer 2.7.13, proof, p. 130: for u in K(G)
    take T(u) = mu^x(u) in K(X), whose gamma integral is
    nu(mu^x(u)) = integral u d alpha. Direct formalisation. *)
Lemma coset_lone_class_compact u : KG u -> Phi u.
Proof.
move=> hu; exists (nu (M u)), (M u); split.
- have h := harep hu; exact: h.
- have h := hcrep (coset_integral_compact hM hu); exact: h.
- apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_true hc))=> y _.
  exact: coset_lone_class_compact_fibre.
Qed.

(** Source for [coset_lone_class_zero]: the zero function belongs to
    Phi, supporting the finite linear combinations in Federer 2.7.13,
    proof, p. 130. Supporting lemma. *)
Lemma coset_lone_class_zero : Phi (fun _ => 0).
Proof.
exists 0, (fun _ => 0); split.
- exact: real_total_zero_integral ha.
- exact: real_total_zero_integral hc.
- apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_true hc))=> y _ g _.
  exact: real_total_zero_integral hb.
Qed.

(** Source for [coset_lone_class_add]: Phi is closed under addition,
    used when "all alpha measurable sets with finite alpha measure are
    obtained by subtracting sets of alpha measure zero from sets in
    F_2[K(G)]", Federer 2.7.13, proof, p. 130; by the additivity of
    the integrals for alpha, gamma and beta (2.4.4(4), p. 82).
    Supporting lemma. *)
Lemma coset_lone_class_add u v : Phi u -> Phi v -> Phi (fun g => u g + v g).
Proof.
move=> [a [b [hua hb1 hb2]]] [a' [b' [hva hb1' hb2']]].
exists (a + a'), (fun y => b y + b' y); split.
- have h := real_total_integral_add ha hua hva; exact: h.
- have h := real_total_integral_add hc hb1 hb1'; exact: h.
- apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_and hc hb2 hb2'))=> y /= [h1 h2].
  exact (coset_fibre_integral_add hb h1 h2).
Qed.

(** Source for [coset_lone_class_scale]: Phi is closed under
    multiplication by real numbers, supporting Federer 2.7.13, proof,
    p. 130; by 2.4.4(3), p. 82. Supporting lemma. *)
Lemma coset_lone_class_scale c u : Phi u -> Phi (fun g => c * u g).
Proof.
move=> [a [b [hua hb1 hb2]]]; exists (c * a), (fun y => c * b y); split.
- have h := real_total_integral_scale ha c hua; exact: h.
- have h := real_total_integral_scale hc c hb1; exact: h.
- apply: (measure_almost_everywhere_mono hc _ hb2)=> y /= h1.
  exact (coset_fibre_integral_scale hb c h1).
Qed.

(** Source for [coset_lone_class_subtract]: Phi is closed under
    subtraction, "subtracting sets of alpha measure zero from sets in
    F_2[K(G)]", Federer 2.7.13, proof, p. 130. Supporting lemma. *)
Lemma coset_lone_class_subtract u v : Phi u -> Phi v -> Phi (fun g => u g - v g).
Proof.
move=> hu hv; have h := coset_lone_class_add hu (coset_lone_class_scale (-1) hv).
have -> : (fun g => u g - v g) = (fun g => u g + -1 * v g) by apply: funext=> g; rewrite mulN1r.
exact: h.
Qed.

(** Source for [coset_lone_class_increasing]: "u_h increases to u as
    h decreases to 0, and Lebesgue's increasing convergence theorem
    implies T(u_h) increases to T(u) as h decreases to 0, E(u) = X,
    u in Phi", Federer 2.7.13, proof, p. 130, for arbitrary functions
    u_n in Phi increasing at every point of G to an alpha summable u.
    The increasing convergence theorem (2.4.7, p. 84) is applied to
    the functions b_n representing T(u_n), which increase gamma almost
    everywhere since the fibre integrals increase, and then on each
    coset g G^x to the functions s |-> u_n(g s). Supporting lemma. *)
Lemma coset_lone_class_increasing (f : nat -> G -> R) u : (forall n, Phi (f n)) ->
  real_functions_increase_to f u -> summable_real_functions alpha u -> Phi u.
Proof.
move=> hf hinc [a hu].
have /choice [p hp] : forall n, exists p : R * (X -> R),
    [/\ is_measure_integral alpha (real_total_integrand (f n)) p.1%:E,
      is_measure_integral gamma (real_total_integrand p.2) p.1%:E &
      measure_almost_everywhere gamma [set y | coset_fibre_integral mul A x beta (f n) y (p.2 y)]].
  by move=> n; have [a' [b' hab]] := hf n; exists (a', b').
have hp1 n : is_measure_integral alpha (real_total_integrand (f n)) (p n).1%:E by case: (hp n).
have hp2 n : is_measure_integral gamma (real_total_integrand (p n).2) (p n).1%:E by case: (hp n).
have hp3 n : measure_almost_everywhere gamma
    [set y | coset_fibre_integral mul A x beta (f n) y ((p n).2 y)] by case: (hp n).
have hlima := real_integral_increasing_continuity ha hp1 hu hinc.
have hbound n : (p n).1 <= a.
  by have := extended_increases_to_upper hlima n; rewrite lee_fin.
have hmonb n : measure_almost_everywhere gamma [set y | (p n).2 y <= (p n.+1).2 y].
  apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_and hc (hp3 n) (hp3 n.+1)))=> y /= [hy1 hy2].
  apply: (coset_fibre_integral_le hA hb _ hy1 hy2)=> g.
  by have := (hinc g).1 n n.+1 (leqnSn n); rewrite lee_fin.
have [b [a' [hb' hlimb hconv]]] := summable_almost_increasing_limit hc hp2 hmonb hbound.
have ha' : a' = a by have := extended_order_limit_unique hlimb.2 hlima.2; case.
rewrite ha' in hb'.
have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] gamma hc setT
  (fun n => [set y | coset_fibre_integral mul A x beta (f n) y ((p n).2 y)]) (countableP setT)
  (fun n _ => hp3 n).
exists a, b; split=> //.
apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_and hc hall hconv))=> y /= [hy hyc] g hg.
apply: (summable_increasing_limit_integral hb (fun n => hy n I g hg)).
- by move=> s; exact: hinc.
- exact: hyc.2.
Qed.

(** Source for [coset_lone_class_dominated_null]: "if u is the
    characteristic function of any set with alpha measure 0, there
    exists a w in Phi with w >= u and integral w d alpha = 0, hence
    T(w) and T(u) are gamma almost equal to 0, hence u in Phi",
    Federer 2.7.13, proof, p. 130, for every function v with
    0 <= v <= w. The representative of T(v) is the zero function: at
    gamma almost all points g x the function s |-> w(g s) has beta
    integral 0, hence so has s |-> v(g s). Supporting lemma. *)
Lemma coset_lone_class_dominated_null w v : Phi w ->
  is_measure_integral alpha (real_total_integrand w) 0%E -> (forall g, 0 <= v g <= w g) -> Phi v.
Proof.
move=> [a [b [hwa hb1 hb2]]] hw0 hvw.
have ha0 : a = 0 by have := measure_integral_unique hwa hw0; case.
rewrite ha0 in hb1.
have hw0' g : 0 <= w g by have /andP [h1 h2] := hvw g; exact: le_trans h1 h2.
have hbnn : measure_almost_everywhere gamma [set y | 0 <= b y].
  apply: (measure_almost_everywhere_mono hc _ hb2)=> y /= h.
  exact (coset_fibre_integral_nonnegative hA hb hw0' h).
have hbz := summable_total_nonnegative_zero_almost hc hb1 hbnn.
exists 0, (fun _ => 0); split.
- have h := summable_total_dominated_zero_integral ha hw0 hvw; exact: h.
- exact: real_total_zero_integral hc.
- apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_and hc hb2 hbz))=> y /= [h hy0] g hg.
  have hwg := h g hg; rewrite hy0 in hwg.
  have h' := summable_total_dominated_zero_integral hb hwg (fun s => hvw (mul g (set_val s))); exact: h'.
Qed.

(** Source for [coset_lone_class_laws]: every function of Phi
    satisfies the two laws of beta^x with the representative b of
    T(u): its integral identity for every value of integral u d alpha,
    and the fibre formula gamma almost everywhere, Federer 2.7.13,
    p. 130. Supporting lemma for the extension of T|Phi to beta^x. *)
Lemma coset_lone_class_laws u : Phi u -> exists b : X -> R,
  (forall a : R, is_measure_integral alpha (real_total_integrand u) a%:E ->
    is_measure_integral gamma (real_total_integrand b) a%:E) /\
  measure_almost_everywhere gamma [set y | coset_fibre_integral mul A x beta u y (b y)].
Proof.
move=> [a [b [hua hb1 hb2]]]; exists b; split=> // a' ha'.
by have := measure_integral_unique hua ha'; case=> <-.
Qed.

End CosetLoneClass.
