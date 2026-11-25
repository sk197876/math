(** Federer (1969), 2.5.17, p. 111: "we see from 2.5.13, 2.5.6, 2.5.3 that
    there exist Borel regular measures psi^+ and psi^- satisfying the
    conditions: (1) mu(f) = int f dpsi^+ - int f dpsi^- whenever f in K(R),
    (2) psi^+{x : a < x < b} + psi^-{x : a < x < b} <= V_a^b g for a < b."
    Federer then speaks of "the" measures induced by g and draws the
    consequences at points of continuity of g, the equality in (2) for
    continuous g, and psi^- = 0 for nondecreasing g. This module proves
    these statements for every pair of measures induced by g in the sense of
    [is_induced_measure_pair], and shows that the pair is unique. The
    positive and negative variations of 2.5.5 are determined by their
    supremum formulas, and a K(R)+ regular measure representing a functional
    on K(R)+ is unique by 2.5.3. The remaining laws follow from the
    arguments of StieltjesContinuityPoints.v,
    StieltjesContinuousIntegrator.v, StieltjesBorelRegularity.v and
    StieltjesSegmentIdentity.v, which use only these hypotheses on the
    measures. For nondecreasing g the negative variation vanishes on K(R)+,
    so psi^- vanishes on every open interval and hence on R. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground ExtendedRealBoundsUP ExtendedRealBounds
  CurveVariationUP CurveArcLength FunctionLatticeUP FunctionLatticeLaws
  FunctionLatticeRegularityUP FunctionLatticeRegularUniqueness PositiveLatticeRegularity
  LatticeAdditiveFunctional DaniellIntegralUP MonotoneDaniellIntegralUP DaniellVariationUP
  DaniellVariationBounds DaniellVariationFunctionals DaniellSignedVariationIntegral
  DaniellCoverUP RegularDaniellEnvelope RealIntegralFunctionalUP MeasureUP MeasureBasic
  MeasureAlmostBasic MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral
  SummableRealFunctionUP RadonMeasureUP BorelRegularMeasureUP CompactSupportFunctionUP
  CompactSupportFunctionLattice StieltjesSums StieltjesIntegral StieltjesDaniellIntegral
  IntervalBumpFunctions StieltjesInducedMeasures StieltjesMonotone StieltjesContinuityPoints
  StieltjesContinuousIntegrator StieltjesBorelRegularity StieltjesSegmentIdentity
  StieltjesImageMeasures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [daniell_positive_variation_unique]: the positive
    variation of 2.5.5, p. 96, is defined by the formula
    "mu^+(f) = sup{mu(k) : k in L, 0 <= k <= f}" for f in L+; two
    functions satisfying it agree on L+. Supporting lemma for the
    uniqueness of the measures induced by g in Federer 2.5.17, p. 111. *)
Lemma daniell_positive_variation_unique (R : realType) (X : Type) (L : set (X -> R))
    (A P P' : (X -> R) -> R) :
  is_daniell_positive_variation L A P -> is_daniell_positive_variation L A P' ->
  forall f, positive_function_lattice L f -> P f = P' f.
Proof. by move=> hP hP' f hf; have := extended_real_supremum_unique (hP f hf) (hP' f hf) => -[]. Qed.

Section InducedPairs.
Variable R : realType.
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation KRp := (positive_function_lattice KR).

(** Source for [induced_measure_pair_unique]: Federer 2.5.17, p. 111,
    refers to "the Daniell integral and measures induced by g". Direct
    formalisation of this uniqueness: two pairs of K(R)+ regular measures
    representing the positive and negative variations of the induced
    Daniell integral coincide as set functions. The variations are
    unique by 2.5.5, p. 96, and the regular representing measures by
    2.5.3, p. 94. No hypothesis on the variation of k is needed. *)
Theorem induced_measure_pair_unique (k : R -> R) (psip psim psip' psim' : set R -> \bar R) :
  is_induced_measure_pair k psip psim -> is_induced_measure_pair k psip' psim' ->
  psip = psip' /\ psim = psim'.
Proof.
move=> [P [Q [hP [hQ [hm [hn [hr [hs [hi hj]]]]]]]]]
  [P' [Q' [hP' [hQ' [hm' [hn' [hr' [hs' [hi' hj']]]]]]]]].
have hL := @compactly_supported_continuous_functions_lattice R R.
have hLp : is_function_lattice KRp := positive_lattice_is_lattice hL.
have hiP : is_real_integral_functional psip' KRp P.
  by move=> f hf; rewrite (daniell_positive_variation_unique hP hP' hf); exact: hi' f hf.
have hjQ : is_real_integral_functional psim' KRp Q.
  by move=> f hf; rewrite (daniell_positive_variation_unique hQ hQ' hf); exact: hj' f hf.
split; apply/funext=> S.
- exact: (@function_lattice_regular_representation_unique R R KRp P hLp psip psip' hm hm' hi hiP
    hr hr' S).
- exact: (@function_lattice_regular_representation_unique R R KRp Q hLp psim psim' hn hn' hj hjQ
    hs hs' S).
Qed.

Variable k : R -> R.
Hypothesis hk : curve_locally_finite_variation (k : R -> real_line_metric R).

(** Source for [induced_measure_pair_laws]: Federer 2.5.17, p. 111,
    for every pair psi^+, psi^- of measures induced by k: they are Borel
    regular (and Radon, 2.5.14, p. 107); "(1) mu(f) = int f dpsi^+ -
    int f dpsi^- whenever f in K(R), (2) psi^+{x : a < x < b} +
    psi^-{x : a < x < b} <= V_a^b g for a < b"; they vanish at the points
    of continuity of k; "int_a^b f dg = int_{x : a <= x <= b} f dpsi^+ -
    int_{x : a <= x <= b} f dpsi^- provided g is continuous at a and b,
    a < b, f in K(R); in particular g(b) - g(a) = psi^+{x : a <= x <= b}
    - psi^-{x : a <= x <= b}"; "if g is a continuous function, then
    equality holds in (2)". Direct formalisation; (2) and its equality
    case are stated for a <= b, which includes the trivial case a = b. *)
Theorem induced_measure_pair_laws (psip psim : set R -> \bar R) :
  is_induced_measure_pair k psip psim ->
  is_measure psip /\ is_measure psim /\
  is_radon_measure psip /\ is_radon_measure psim /\
  is_borel_regular_measure psip /\ is_borel_regular_measure psim /\
  is_function_lattice_regular KR psip /\ is_function_lattice_regular KR psim /\
  (forall f, KR f -> exists u v : R,
    is_measure_integral psip (real_total_integrand f) u%:E /\
    is_measure_integral psim (real_total_integrand f) v%:E /\ induced_daniell k f = u - v) /\
  (forall a b : R, a <= b -> (psip `]a, b[ + psim `]a, b[ <= (total_variation k a b)%:E)%E) /\
  (forall x : R, k @ x --> k x -> psip [set x] = 0%E /\ psim [set x] = 0%E) /\
  (forall a b : R, a < b -> k @ a --> k a -> k @ b --> k b ->
    (k b - k a)%:E = (psip `]a, b[ - psim `]a, b[)%E /\
    (k b - k a)%:E = (psip `[a, b] - psim `[a, b])%E) /\
  (forall (f : R -> R) (a b : R), KR f -> a < b -> k @ a --> k a -> k @ b --> k b ->
    exists u v : R,
      is_measure_subset_integral psip `[a, b] (real_total_integrand f) u%:E /\
      is_measure_subset_integral psim `[a, b] (real_total_integrand f) v%:E /\
      stieltjes_integral k f a b = u - v) /\
  (continuous k -> forall a b : R, a <= b ->
    (psip `]a, b[ + psim `]a, b[)%E = (total_variation k a b)%:E).
Proof.
move=> [P [Q [hP [hQ [hm [hn [hr [hs [hi hj]]]]]]]]].
have hL := @compactly_supported_continuous_functions_lattice R R.
have hD := induced_daniell_is_daniell hk.
have hform : forall f, KR f -> exists u v : R,
    is_measure_integral psip (real_total_integrand f) u%:E /\
    is_measure_integral psim (real_total_integrand f) v%:E /\ induced_daniell k f = u - v.
  by move=> f hf; exact (daniell_signed_variation_integral hL hD hP hQ hm hn hi hj hf).
have hLp : is_function_lattice KRp := positive_lattice_is_lattice hL.
have henvP := regular_representing_measure_envelope hLp hm hi hr.
have henvQ := regular_representing_measure_envelope hLp hn hj hs.
have hbound := induced_cost_bound hk hP hQ henvP henvQ.
have hbp : forall t u, t <= u -> (psip `]t, u[ <= (total_variation k t u)%:E)%E.
  move=> t u htu; apply: le_trans _ (hbound t u htu).
  exact: lee_paddr (measure_nonnegative hn _) (lexx _).
have hbm : forall t u, t <= u -> (psim `]t, u[ <= (total_variation k t u)%:E)%E.
  move=> t u htu; apply: le_trans _ (hbound t u htu).
  exact: lee_paddl (measure_nonnegative hm _) (lexx _).
have hpoint : forall x : R, k @ x --> k x -> psip [set x] = 0%E /\ psim [set x] = 0%E.
  by move=> x hc; split; [exact (induced_point_mass_zero hk hm hbp hc) |
    exact (induced_point_mass_zero hk hn hbm hc)].
have hincr : forall a b : R, a < b -> k @ a --> k a -> k @ b --> k b ->
    (k b - k a)%:E = (psip `]a, b[ - psim `]a, b[)%E /\
    (k b - k a)%:E = (psip `[a, b] - psim `[a, b])%E.
  move=> a b hab hca hcb.
  have hopen := induced_increment_open hk hP hQ henvP henvQ hm hn hbound hab hca hcb.
  split=> //.
  have [h0a h0a'] := hpoint a hca.
  have [h0b h0b'] := hpoint b hcb.
  by rewrite (measure_segment_open_interval hm h0a h0b) (measure_segment_open_interval hn h0a' h0b').
have [hradp hborp] := positive_regular_radon hm hi hr.
have [hradm hborm] := positive_regular_radon hn hj hs.
do 6!(split=> //).
split; first exact ((@function_lattice_regular_positive_iff R R KR psip).1 hr).
split; first exact ((@function_lattice_regular_positive_iff R R KR psim).1 hs).
do 4!(split=> //).
split; first exact (segment_identity_core hk hm hn hi hj hform hpoint).
move=> hc a b hab; apply/le_anti; rewrite hbound //=.
apply: (continuous_variation_le_induced hk hm hn hi hj hbound _ hab)=> t u htu.
exact: (hincr t u htu (hc t) (hc u)).1.
Qed.

Hypothesis hmono : forall x y : R, x <= y -> k x <= k y.

(** Source for [induced_negative_variation_monotone_zero]: for
    nondecreasing k the induced Daniell integral is monotone, so its
    negative variation sup{-mu(h) : h in K(R), 0 <= h <= f} vanishes on
    K(R)+, Federer 2.5.17, p. 111, with 2.5.5, p. 96. Supporting lemma
    for "hence psi^- = 0". *)
Lemma induced_negative_variation_monotone_zero (Q : (R -> R) -> R) :
  is_daniell_negative_variation KR (induced_daniell k) Q -> forall f, KRp f -> Q f = 0.
Proof.
move=> hQ f hf; apply/le_anti/andP; split.
- apply: (daniell_positive_variation_least hQ hf)=> h [hh [hh0 _]].
  by rewrite oppr_le0; exact (induced_daniell_nonnegative hk hmono hh hh0).
- have hL := @compactly_supported_continuous_functions_lattice R R.
  have hz : KR (fun _ => 0) := @compactly_supported_zero_function R R.
  have hzi : lattice_positive_order_interval KR f (fun _ => 0).
    by split=> //; split=> x //; exact: hf.2.
  have hz0 : induced_daniell k (fun _ => 0) = 0.
    have h := induced_daniell_scale hk 0 hz.
    by rewrite !mul0r in h; exact h.
  have := extended_real_supremum_upper (hQ f hf) (ex_intro _ (fun _ => 0) (conj hzi erefl)).
  by rewrite hz0 oppr0 lee_fin.
Qed.

(** Source for [induced_measure_pair_monotone]: "In case the function g
    is nondecreasing, the induced Daniell integral mu is monotone, hence
    psi^- = 0", Federer 2.5.17, p. 111. Direct formalisation for every
    pair induced by k: psi^- is the zero set function and psi^+
    represents mu on K(R). *)
Theorem induced_measure_pair_monotone (psip psim : set R -> \bar R) :
  is_induced_measure_pair k psip psim ->
  psim = (fun _ => 0%E) /\ is_real_integral_functional psip KR (induced_daniell k).
Proof.
move=> hpair; have hpair' := hpair.
move: hpair' => [P [Q [hP [hQ [hm [hn [hr [hs [hi hj]]]]]]]]].
have hL := @compactly_supported_continuous_functions_lattice R R.
have hD := induced_daniell_is_daniell hk.
have hLp : is_function_lattice KRp := positive_lattice_is_lattice hL.
have hQ0 := induced_negative_variation_monotone_zero hQ.
have hAQ := negative_variation_monotone_daniell hL hD hQ.
have henvQ := regular_representing_measure_envelope hLp hn hj hs.
have hbump : forall a b n, KRp (interval_bump a b n).
  by move=> a b n; split; [exact: interval_bump_member | move=> x; exact: interval_bump_ge0].
have hopen : forall a b : R, psim `]a, b[ = 0%E.
  move=> a b; apply/eqP; rewrite eq_le (measure_nonnegative hn) andbT.
  have hsup := bump_cost_open_interval a b hAQ henvQ.
  apply: (extended_real_supremum_least hsup)=> z [n ->].
  by rewrite (hQ0 _ (hbump a b n)).
have hT : psim setT = 0%E.
  have -> : setT = \bigcup_(n in [set: nat]) `](- n%:R : R), n%:R[.
    apply/seteqP; split=> y // _.
    have /andP[_ hy] := truncn_itv (normr_ge0 y).
    exists (Num.truncn `|y|).+1=> //; move: hy; rewrite /= in_itv /= ltr_norml.
    by [].
  by apply: (measure_null_countable_union hn (countableP _))=> n _; exact: hopen.
have hzero : psim = (fun _ => 0%E).
  by apply/funext=> S; exact (measure_null_subset hn (subsetT S) hT).
split=> // f hf.
have [u [v [hu [hv he]]]] := daniell_signed_variation_integral hL hD hP hQ hm hn hi hj hf.
have hfp : KRp (fun x => Order.max (f x) 0).
  by split; [exact (function_lattice_positive_part hL hf) | move=> x; rewrite le_max lexx orbT].
have hfn : KRp (fun x => Order.max (- f x) 0).
  by split; [exact (function_lattice_negative_part hL hf) | move=> x; rewrite le_max lexx orbT].
have hv0 := positive_representation_signed hn hj hf.
rewrite (hQ0 _ hfp) (hQ0 _ hfn) subr0 in hv0.
have [e] := measure_integral_unique hv hv0.
by rewrite he e subr0.
Qed.

End InducedPairs.
