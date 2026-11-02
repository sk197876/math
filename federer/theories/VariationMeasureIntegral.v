(** Federer (1969), 2.5.6, p. 98: "One calls mu+ + mu- the variation
    integral, and psi+ + psi- the variation measure, corresponding to mu."
    Under the hypotheses of 2.5.5, pp. 96–97, the variation integral is a
    monotone Daniell integral on L+, and the variation measure represents it
    on L+. The integral of a nonnegative function with respect to psi+ +
    psi- is the sum of its two integrals; the proof applies the
    characteristic expansion of 2.3.3, p. 76, simultaneously to both
    measures, and integrates the resulting series by 2.4.8, p. 84. Federer
    does not assert that the variation measure is L+ regular; it is proved
    here as a supporting result, so that the variation measure is the L+
    regular measure associated with the variation integral by 2.5.3, p. 94.
    The local erratum has no entry for 2.5.6. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureBasic
  WeightedCharacteristicExpansionUP GreedyCharacteristicSystemUP GreedyCharacteristicSystemSealed
  GreedySystemRepresentation PositiveVanishingWeightsSealed WeightedCharacteristicIntegral
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence DensityCharacteristicIntegral
  NonnegativeSum NonnegativeSumAdd NonnegativeSumSupport SummableRealFunctionUP RealIntegralFunctionalUP
  FunctionLatticeUP FunctionLatticeLaws FunctionLatticeLevelFamilies FunctionLatticeLevelFamilyLaws
  FunctionLatticeRegularityUP FunctionLatticeRegularUniqueness MonotoneDaniellIntegralUP
  MonotoneDaniellIntegralSum DaniellIntegralUP DaniellVariationUP DaniellVariationFunctionals
  DaniellVariationRepresentation VariationIntegralMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [variation_measure_nonnegative_integral]: supporting
    additivity of the integral in the measure, for the variation
    measure psi+ + psi- of Federer 2.5.6, p. 98. The
    greedy sets of 2.3.3, p. 76, depend only on the function, so they
    expand it for psi+, psi- and their sum at once; 2.4.8,
    p. 84, integrates the three series. Infinite values of the
    function and of the integrals are allowed. *)
Theorem variation_measure_nonnegative_integral (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (f : X -> extended_real_line R) a b :
  (forall x, 0 <= f x) ->
  is_measure_integral mu (partial_function_total f) a ->
  is_measure_integral nu (partial_function_total f) b ->
  is_measure_integral (variation_measure mu nu) (partial_function_total f) (a+b).
Proof.
move=> hp ha hb.
have hs := variation_measure_laws hm hn.
pose r := @PositiveVanishingWeights.value R; have hr := @PositiveVanishingWeights.laws R.
pose p := @GreedyCharacteristicSystem.value R X f r.
have hgr := @GreedyCharacteristicSystem.laws R X f r.
have hem := @greedy_system_weighted_representation R X mu hm f r p.1 p.2 ha.1 hp hr hgr.
have hen := @greedy_system_weighted_representation R X nu hn f r p.1 p.2 hb.1 hp hr hgr.
have hes : is_weighted_characteristic_expansion (variation_measure mu nu) f r p.1 p.2.
  constructor.
  - move=> n; exact: variation_measure_common_measurable
      (expansion_sets_measurable hem n) (expansion_sets_measurable hen n).
  - exact: expansion_characteristic_laws hem.
  - exact: expansion_pointwise_sum hem.
have hpos := expansion_weights_positive hr.
have him := @weighted_characteristic_expansion_integral R X mu hm f r p.1 p.2 hpos hem.
have hin := @weighted_characteristic_expansion_integral R X nu hn f r p.1 p.2 hpos hen.
have his := @weighted_characteristic_expansion_integral R X _ hs f r p.1 p.2 hpos hes.
have hrn n : 0 <= (r n)%:E by rewrite lee_fin; exact: ltW (hpos n).
have hsum : nonnegative_sum setT (fun n => (r n)%:E * variation_measure mu nu (p.1 n))=
    nonnegative_sum setT (fun n => (r n)%:E * mu (p.1 n))+
    nonnegative_sum setT (fun n => (r n)%:E * nu (p.1 n)).
  rewrite -nonnegative_sum_add.
  - apply: nonnegative_sum_ext=> n _; rewrite /variation_measure.
    exact: ge0_muleDr (measure_nonnegative hm _) (measure_nonnegative hn _).
  - move=> n _; exact: mule_ge0 (hrn n) (measure_nonnegative hm _).
  - move=> n _; exact: mule_ge0 (hrn n) (measure_nonnegative hn _).
rewrite hsum (measure_integral_unique him ha) (measure_integral_unique hin hb) in his.
exact: his.
Qed.

(** Source for [variation_measure_real_integral]: the real-valued
    case used for f in L+ in Federer 2.5.6, p. 98: the integral
    of f for psi+ + psi- is the sum of the integrals of f for psi+ and
    for psi-. *)
Lemma variation_measure_real_integral (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (f : X -> R) (a b : R) :
  (forall x, (0 <= f x)%R) ->
  is_measure_integral mu (real_total_integrand f) a%:E ->
  is_measure_integral nu (real_total_integrand f) b%:E ->
  is_measure_integral (variation_measure mu nu) (real_total_integrand f) (a+b)%R%:E.
Proof.
move=> hp ha hb.
pose F x : extended_real_line R := (f x)%:E.
have hF x : 0 <= F x by rewrite /F lee_fin.
have ha' : is_measure_integral mu (partial_function_total F) a%:E.
  exact: measure_integral_graph_equivalent (real_total_embedding_graph f) ha.
have hb' : is_measure_integral nu (partial_function_total F) b%:E.
  exact: measure_integral_graph_equivalent (real_total_embedding_graph f) hb.
have hs := @variation_measure_nonnegative_integral R X mu nu hm hn F a%:E b%:E hF ha' hb'.
rewrite -EFinD in hs.
apply: (@measure_integral_graph_equivalent R X _ _ _ _ _ hs)=> x y.
exact: iff_sym (real_total_embedding_graph f x y).
Qed.

(** Source for [variation_measure_represents_variation_integral]:
    the variation measure psi+ + psi- represents the variation
    integral mu+ + mu- on L+, Federer 2.5.6, p. 98, for any
    measures psi+ and psi- with mu+(f) = integral f dpsi+ and
    mu-(f) = integral f dpsi- whenever f in L+, as in 2.5.5,
    p. 96. Regularity of psi+ and psi- is not needed. *)
Theorem variation_measure_represents_variation_integral (R : realType) (X : choiceType)
    (L : set (X -> R)) (P Q : (X -> R) -> R) (mu nu : set X -> \bar R)
    (hm : is_measure mu) (hn : is_measure nu) :
  is_real_integral_functional mu (positive_function_lattice L) P ->
  is_real_integral_functional nu (positive_function_lattice L) Q ->
  is_real_integral_functional (variation_measure mu nu) (positive_function_lattice L)
    (variation_integral P Q).
Proof.
move=> hP hQ f hf.
exact: (@variation_measure_real_integral R X mu nu hm hn f (P f) (Q f) hf.2 (hP f hf) (hQ f hf)).
Qed.

(** Source for [daniell_variation_integral_monotone]: the
    variation integral mu+ + mu- of Federer 2.5.6, p. 98,
    is a monotone Daniell integral on L+ in the sense of 2.5.2,
    p. 92, because mu+ and mu- are, by the proof of 2.5.5,
    p. 97. *)
Theorem daniell_variation_integral_monotone (R : realType) (X : Type)
    (L : set (X -> R)) (A P Q : (X -> R) -> R) :
  is_function_lattice L -> is_daniell_integral L A ->
  is_daniell_positive_variation L A P -> is_daniell_negative_variation L A Q ->
  is_monotone_daniell_integral (positive_function_lattice L) (variation_integral P Q).
Proof.
move=> hL hA hP hQ.
exact: (monotone_daniell_integral_sum (positive_variation_monotone_daniell hL hA hP)
  (negative_variation_monotone_daniell hL hA hQ)).
Qed.

(** Source for [variation_measure_regular]: supporting result for
    the variation measure of Federer 2.5.6, p. 98: the sum of
    two L regular measures (2.5.3, p. 94) is L regular. Federer
    does not state this. The F2 hulls of the two summands are
    intersected termwise; F1 is closed under binary intersection. *)
Theorem variation_measure_regular (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (mu nu : set X -> \bar R)
    (hm : is_measure mu) (hn : is_measure nu) :
  is_function_lattice_regular L mu -> is_function_lattice_regular L nu ->
  is_function_lattice_regular L (variation_measure mu nu).
Proof.
move=> hr hs S; split.
- move=> hS.
  have hmS : mu S < +oo.
    apply: le_lt_trans _ hS; rewrite /variation_measure -[X in X <= _]adde0.
    exact: leeD (lexx _) (measure_nonnegative hn S).
  have hnS : nu S < +oo.
    apply: le_lt_trans _ hS; rewrite /variation_measure -[X in X <= _]add0e.
    exact: leeD (measure_nonnegative hm S) (lexx _).
  have [W1 [hSW1 [[V [hV [hVd [hV0 hW1]]]] [hmW1 _]]]] := (hr S).1 hmS.
  have [W2 [hSW2 [[U [hU [hUd [hU0 hW2]]]] [hnW2 _]]]] := (hs S).1 hnS.
  pose W := \bigcap_(n in setT) (V n `&` U n).
  have hWW : W = W1 `&` W2.
    rewrite hW1 hW2; apply/seteqP; split=> x.
    + by move=> hx; split=> n _; have [] := hx n Logic.I.
    + by move=> [h1 h2] n _; split; [exact: h1 n Logic.I | exact: h2 n Logic.I].
  have hmW : mu W = mu S.
    apply/le_anti/andP; split.
    + rewrite hmW1; apply: (measure_mono hm); rewrite hWW; exact: subIsetl.
    + apply: (measure_mono hm)=> x hx; rewrite hWW; split; [exact: hSW1 | exact: hSW2].
  have hnW : nu W = nu S.
    apply/le_anti/andP; split.
    + rewrite hnW2; apply: (measure_mono hn); rewrite hWW; exact: subIsetr.
    + apply: (measure_mono hn)=> x hx; rewrite hWW; split; [exact: hSW1 | exact: hSW2].
  exists W; split.
    by move=> x hx; rewrite hWW; split; [exact: hSW1 | exact: hSW2].
  split.
    exists (fun n => V n `&` U n); split.
      move=> n; exact (function_lattice_increasing_levels_intersection hL (hV n) (hU n)).
    split.
      move=> n k hnk x [h1 h2]; split; [exact: hVd n k hnk x h1 | exact: hUd n k hnk x h2].
    split=> //.
    rewrite /variation_measure; apply: lte_add_pinfty.
    + exact: le_lt_trans (measure_mono hm (@subIsetl _ (V 0%N) (U 0%N))) hV0.
    + exact: le_lt_trans (measure_mono hn (@subIsetr _ (V 0%N) (U 0%N))) hU0.
  by rewrite /variation_measure hmW hnW; split.
- by move=> [W [_ [_ [-> hW]]]].
Qed.

(** Source for [variation_measure_associated]: in the
    situation of Federer 2.5.5, pp. 96–97, the variation
    measure psi+ + psi- of 2.5.6, p. 98, is the L+ regular
    measure associated by 2.5.2–2.5.3, pp. 92–94, with the
    monotone Daniell integral mu+ + mu-: it is L+ regular, it
    represents mu+ + mu- on L+, and every L+ regular measure
    representing mu+ + mu- on L+ equals it. Only the regularity
    and the representations of psi+ and psi- are used; that
    mu+ and mu- arise from a Daniell integral is not needed. *)
Theorem variation_measure_associated (R : realType) (X : choiceType)
    (L : set (X -> R)) (P Q : (X -> R) -> R) (mu nu : set X -> \bar R) :
  is_function_lattice L ->
  is_measure mu -> is_measure nu ->
  is_function_lattice_regular (positive_function_lattice L) mu ->
  is_function_lattice_regular (positive_function_lattice L) nu ->
  is_real_integral_functional mu (positive_function_lattice L) P ->
  is_real_integral_functional nu (positive_function_lattice L) Q ->
  [/\ is_measure (variation_measure mu nu),
    is_function_lattice_regular (positive_function_lattice L) (variation_measure mu nu),
    is_real_integral_functional (variation_measure mu nu) (positive_function_lattice L)
      (variation_integral P Q) &
    forall phi : set X -> \bar R, is_measure phi ->
      is_function_lattice_regular (positive_function_lattice L) phi ->
      is_real_integral_functional phi (positive_function_lattice L) (variation_integral P Q) ->
      phi = variation_measure mu nu].
Proof.
move=> hL hm hn hr hs hmu hnu.
have hpos := positive_function_lattice_laws hL.
have hsm := variation_measure_laws hm hn.
have hsr := variation_measure_regular hpos hm hn hr hs.
have hsi := variation_measure_represents_variation_integral hm hn hmu hnu.
split=> // phi hphi hphir hphii.
apply: funext=> S.
exact: (@function_lattice_regular_representation_unique R X _ (variation_integral P Q) hpos
  phi (variation_measure mu nu) hphi hsm hphii hsi hphir hsr S).
Qed.

(** Source for [daniell_variation_measure_representation]: the
    complete situation of Federer 2.5.6, p. 98, after 2.5.5,
    pp. 96–97: for a Daniell integral mu on a nonempty lattice L
    there are L+ regular measures psi+ and psi- representing mu+
    and mu-, and their sum, the variation measure, is the L+ regular
    measure representing the monotone Daniell integral mu+ + mu- on
    L+. Nonemptiness is the boundary condition of 2.5.5 recorded in
    DaniellVariationRepresentation.v. *)
Theorem daniell_variation_measure_representation (R : realType) (X : choiceType)
    (L : set (X -> R)) (A P Q : (X -> R) -> R) :
  is_function_lattice L -> is_daniell_integral L A ->
  is_daniell_positive_variation L A P -> is_daniell_negative_variation L A Q ->
  (exists f, L f) -> exists mu nu : set X -> \bar R,
    is_measure mu /\ is_measure nu /\
    is_real_integral_functional mu (positive_function_lattice L) P /\
    is_real_integral_functional nu (positive_function_lattice L) Q /\
    is_monotone_daniell_integral (positive_function_lattice L) (variation_integral P Q) /\
    is_function_lattice_regular (positive_function_lattice L) (variation_measure mu nu) /\
    is_real_integral_functional (variation_measure mu nu) (positive_function_lattice L)
      (variation_integral P Q).
Proof.
move=> hL hA hP hQ hne.
have [mu [nu [hm [hn [hr [hs [hmu [hnu _]]]]]]]] :=
  @daniell_variations_regular_representation R X L A P Q hL hA hP hQ hne.
have [_ hsr hsi _] := variation_measure_associated hL hm hn hr hs hmu hnu.
exists mu, nu; do 4!(split=> //); split; last by split.
exact: daniell_variation_integral_monotone hL hA hP hQ.
Qed.
