(** Federer (1969), 2.5.11, p. 102: there is no phi measurable function k
    with mu(f)=integral f k d phi for all f in L. Suppose k were such a
    function. For u in Y_1 the characteristic function of {u} x Y_2 gives
    1=integral k(u,v) d beta_2 v, so the beta_2 measurable set {v: k(u,v)>0}
    has positive measure and the set {v: k(u,v)<=0} has cardinal at most
    aleph-one; hence card{(u,v): k(u,v)<=0} <= (card Y_1) aleph-one =
    aleph-one. For v in Y_2 the characteristic function of Y_1 x {v} gives
    0=integral k(u,v) d beta_1 u, so {u: k(u,v)<=0} is nonempty, which gives
    card{(u,v): k(u,v)<=0} >= card Y_2 = aleph-two. The two line integrals
    are obtained from the restrictions of phi to the lines, 2.4.10, p. 85,
    and the image measures, 2.4.18, p. 90, in place of the identity
    L_1(phi)=L. This answers the question of 2.5.10, pp. 100-101, in the
    negative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import CardinalSuccessorUP CardinalInjection CardinalMeasureUP CardinalMeasureLaws
  AlephOneArithmetic CardinalProductExample CardinalProductStrips
  MeasureUP MeasureBasic MeasureAlmostUP MeasureRestriction MeasurePushforward
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition PartialZeroExtension
  MeasurableFunctionUP MeasurableFunctionBorel MeasurableGraphEquivalence TopologicalBorel
  CountableOrderIntervals ExtendedRealOrderTopology PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralComparison MeasureDensityNullSets
  MeasureStepIntegralIdentification SummableRealFunctionUP RealTotalCharacteristicBounds
  TotalScalarLpUP TotalScalarMeasurability TotalScalarCutoff RestrictedIntegralIdentity
  RestrictedFunctionMeasurability PushforwardIntegral PushforwardMeasurabilityTransfer
  FunctionLatticeUP FunctionLatticeLevelMeasurability RealLatticeDensityUP
  CharacteristicFunctionUP CharacteristicFunctionSealed RealIntegralFunctionalUP
  FunctionLatticeRegularityUP
  RealNormUP NormMetric
  MonotoneDaniellIntegralUP
  DaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [reciprocal_below_positive]: Archimedean background
    for Federer 2.5.11, p. 102: a positive real exceeds the reciprocal
    of some positive integer. *)
Lemma reciprocal_below_positive (R : realType) (x : R) :
  (0 < x)%R -> exists n : nat, (n.+1%:R^-1 < x)%R.
Proof.
move=> hx; have hxi : (0 < x^-1)%R by rewrite invr_gt0.
exists (Num.bound x^-1).
rewrite -[x in (_ < x)%R]invrK ltf_pV2 ?posrE ?ltr0n //.
apply: lt_le_trans (archi_boundP (ltW hxi)) _.
by rewrite ler_nat.
Qed.

Section Counterexample.
Variable R : realType.
Variables J1 J2 : choiceType.
Hypothesis h1 : is_cardinal_successor (@setT nat) (@setT J1).
Hypothesis h2 : is_cardinal_successor (@setT J1) (@setT J2).
Variable phi : set (J1 * J2) -> \bar R.
Hypothesis hm : is_measure phi.
Hypothesis hA : is_real_integral_functional phi (@example_lattice R J1 J2 h1) (@example_lambda R J1 J2 h1).
Hypothesis hr : is_function_lattice_regular (@example_lattice R J1 J2 h1) phi.

Local Notation beta1 := (@example_beta1 R J1).
Local Notation beta2 := (@example_beta2 R J1 J2).
Local Notation hb1 := (@example_beta1_measure R J1).
Local Notation hb2 := (@example_beta2_measure R J1 J2 h1).
Local Notation L := (@example_lattice R J1 J2 h1).
Local Notation mu := (@example_mu R J1 J2 h1).
Local Notation chi := (@example_rectangle_characteristic R J1 J2).
Local Notation scalar_space := [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)].

(** Source for [example_lattice_summable]: every member of L is phi
    summable, Federer 2.5.2, p. 92, the easy inclusion in the identity
    L_1(phi)=L of 2.5.11, p. 102. *)
Lemma example_lattice_summable (f : J1 * J2 -> R) : L f -> summable_real_functions phi f.
Proof. by move=> hf; exists (@example_lambda R J1 J2 h1 f); exact (hA hf). Qed.

(** Source for [line_cutoff_integral]: supporting identification of
    integral f k d phi, with f the characteristic function of a line
    S, with the integral of k for phi restricted to S, Federer 2.4.10,
    p. 85, used in 2.5.11, p. 102. *)
Lemma line_cutoff_integral (S : set (J1 * J2)) (k : J1 * J2 -> R) (a : \bar R) :
  measure_measurable phi S ->
  is_measure_integral phi
    (real_total_integrand (fun x => (@CharacteristicFunction.value R (J1 * J2) S x * k x)%R)) a ->
  is_measure_integral (measure_restrict phi S) (real_total_integrand k) a.
Proof.
move=> hS hint; apply: (restricted_integral_zero_extension_iff hm (real_total_integrand k) a hS).2.
apply: (measure_integral_graph_equivalent _ hint)=> x y.
rewrite total_scalar_cutoff_integrand_graph !real_total_integrand_graph /total_scalar_cutoff.
by rewrite mulrC; exact: iff_refl.
Qed.

(** Source for [precompose_graph]: supporting graph identity of the
    composition of 2.4.18, p. 90, with a total map, used for the
    sections in Federer 2.5.11, p. 102. *)
Lemma precompose_graph (X Y Z : Type) (u : X -> Y) (f : partial_function Y Z) x z :
  partial_function_graph (partial_function_precompose u f) x z <-> partial_function_graph f (u x) z.
Proof. exact: iff_refl. Qed.

(** Source for [vertical_section_integral]: the identity
    1=mu(f)=integral k(u,v) d beta_2 v in Federer 2.5.11, p. 102, for
    the characteristic function f of {u} x Y_2, together with the
    beta_2 measurability of the section. *)
Lemma vertical_section_integral (k : J1 * J2 -> R) (u : J1) :
  is_real_lattice_density phi L mu k ->
  is_measure_measurable_function beta2 (real_total_integrand (fun v => k (u, v))) /\
  is_measure_integral beta2 (real_total_integrand (fun v => k (u, v))) 1.
Proof.
move=> [hk hrep].
have [hLu hmu] := @example_vertical_line_values R J1 J2 h1 h2 u.
have hint := hrep _ hLu; rewrite hmu in hint.
have hres := line_cutoff_integral (@vertical_line_phi_measurable R J1 J2 h1 h2 phi hm hA u) hint.
rewrite (@phi_restrict_vertical R J1 J2 h1 h2 phi hm hA hr u) in hres.
have hkr := measurable_function_for_restricted_measure hm ([set u] `*` setT) hk.
rewrite (@phi_restrict_vertical R J1 J2 h1 h2 phi hm hA hr u) in hkr.
have hpre := measurable_function_pushforward_precompose (vertical_embedding_injective (u := u)) hkr.
have hsec : @is_measure_measurable_function R J2 scalar_space beta2 (total_scalar_function (fun v => k (u, v))).
  by apply: (measurable_function_graph_equivalent _ hpre)=> v y; split.
have hsec' : is_measure_measurable_function beta2 (real_total_integrand (fun v => k (u, v))).
  exact (measurable_partial_real_embedding hb2 (total_scalar_real_measurable hb2 hsec)).
have hgraph : forall v y,
    partial_function_graph (partial_function_precompose (vertical_embedding u) (real_total_integrand k)) v y <->
    partial_function_graph (real_total_integrand (fun v => k (u, v))) v y.
  by move=> v y; rewrite precompose_graph !real_total_integrand_graph; exact: iff_refl.
have hpre' : is_measure_measurable_function beta2
    (partial_function_precompose (vertical_embedding u) (real_total_integrand k)).
  by apply: (measurable_function_graph_equivalent _ hsec')=> v y; rewrite hgraph.
split=> //.
apply: (measure_integral_graph_equivalent (f := partial_function_precompose (vertical_embedding u)
  (real_total_integrand k)) hgraph).
exact ((measure_pushforward_integral_iff hb2 hpre' 1).2 hres).
Qed.

(** Source for [horizontal_section_integral]: the identity
    0=mu(g)=integral k(u,v) d beta_1 u in Federer 2.5.11, p. 102, for
    the characteristic function g of Y_1 x {v}, together with the
    beta_1 measurability of the section. *)
Lemma horizontal_section_integral (k : J1 * J2 -> R) (v : J2) :
  is_real_lattice_density phi L mu k ->
  is_measure_measurable_function beta1 (real_total_integrand (fun u => k (u, v))) /\
  is_measure_integral beta1 (real_total_integrand (fun u => k (u, v))) 0.
Proof.
move=> [hk hrep].
have [hLv hmu] := @example_horizontal_line_values R J1 J2 h1 v.
have hint := hrep _ hLv; rewrite hmu in hint.
have hres := line_cutoff_integral (@horizontal_line_phi_measurable R J1 J2 h1 phi hm hA v) hint.
rewrite (@phi_restrict_horizontal R J1 J2 h1 phi hm hA hr v) in hres.
have hkr := measurable_function_for_restricted_measure hm (setT `*` [set v]) hk.
rewrite (@phi_restrict_horizontal R J1 J2 h1 phi hm hA hr v) in hkr.
have hpre := measurable_function_pushforward_precompose (horizontal_embedding_injective (v := v)) hkr.
have hsec : @is_measure_measurable_function R J1 scalar_space beta1 (total_scalar_function (fun u => k (u, v))).
  by apply: (measurable_function_graph_equivalent _ hpre)=> u y; split.
have hsec' : is_measure_measurable_function beta1 (real_total_integrand (fun u => k (u, v))).
  exact (measurable_partial_real_embedding hb1 (total_scalar_real_measurable hb1 hsec)).
have hgraph : forall u y,
    partial_function_graph (partial_function_precompose (horizontal_embedding v) (real_total_integrand k)) u y <->
    partial_function_graph (real_total_integrand (fun u => k (u, v))) u y.
  by move=> u y; rewrite precompose_graph !real_total_integrand_graph; exact: iff_refl.
have hpre' : is_measure_measurable_function beta1
    (partial_function_precompose (horizontal_embedding v) (real_total_integrand k)).
  by apply: (measurable_function_graph_equivalent _ hsec')=> u y; rewrite hgraph.
split=> //.
apply: (measure_integral_graph_equivalent (f := partial_function_precompose (horizontal_embedding v)
  (real_total_integrand k)) hgraph).
exact ((measure_pushforward_integral_iff hb1 hpre' 0).2 hres).
Qed.

(** Source for [real_total_positive_level_measurable]: supporting
    measurability of {x: t<g(x)} for a measurable total real g, by
    2.3.2(1), p. 73, used for the sections in Federer 2.5.11, p. 102. *)
Lemma real_total_positive_level_measurable (K : choiceType) (nu : set K -> \bar R)
    (hn : is_measure nu) (g : K -> R) (t : R) :
  is_measure_measurable_function nu (real_total_integrand g) ->
  measure_measurable nu [set x | (t < g x)%R].
Proof.
move=> hg; rewrite -(real_total_strict_upper_level g t).
apply: (@measurable_function_borel_preimage R K (extended_real_line R) nu hn _ hg).
by apply: open_borel_set; exact: order_strict_upper_ray_open.
Qed.

(** Source for [vertical_section_small]: the inference in Federer
    2.5.11, p. 102, that {v: k(u,v)>0} has positive beta_2 measure,
    its complement has beta_2 measure zero, and therefore
    card{v: k(u,v)<=0} <= aleph-one. *)
Lemma vertical_section_small (k : J1 * J2 -> R) (u : J1) :
  is_real_lattice_density phi L mu k -> [set v | (k (u, v) <= 0)%R] #<= @setT J1.
Proof.
move=> hd; have [hmeas hint] := vertical_section_integral u hd.
pose g := fun v => k (u, v).
pose P := [set v | (0 < g v)%R].
have hP : measure_measurable beta2 P by exact (real_total_positive_level_measurable hb2 0%R hmeas).
have hP1 : beta2 P = 1.
  have [h0|h1'] := cardinal_measure_values R (@setT J1) P; last exact: h1'.
  exfalso.
  pose zero := partial_function_total (fun _ : J2 => (0 : extended_real_line R)).
  have hsub : ~` (partial_extended_le_locus (real_total_integrand g) zero) `<=` P.
    move=> v hv; rewrite /P; apply: contrapT=> hn; apply: hv.
    exists (g v)%:E, 0; split; first by rewrite real_total_integrand_graph.
    by split=> //; rewrite lee_fin leNgt; apply/negP.
  have hle := measure_mono hb2 hsub; rewrite /example_beta2 h0 in hle.
  have hae : measure_almost_everywhere beta2 (partial_extended_le_locus (real_total_integrand g) zero).
    rewrite /measure_almost_everywhere; apply/le_anti/andP.
    by split; [exact: hle|exact: (measure_nonnegative hb2)].
  have := measure_integral_monotone hb2 hint (measure_extended_zero_integral hb2) hae.
  by rewrite (lt_geF lte01).
have [hsmall|hco] := (cardinal_measure_measurable_iff R (@aleph_one_sigma_small J1 J2 setT h1) P).1 hP.
- move: hP1; rewrite /example_beta2 (cardinal_measure_small R hsmall).
  by move/eqP; rewrite eq_sym eqe oner_eq0.
- have -> : [set v | (k (u, v) <= 0)%R] = ~` P.
    by apply/seteqP; split=> v; rewrite /P /= leNgt; [move/negP|move/negP].
  exact: hco.
Qed.

(** Source for [horizontal_section_nonpositive_point]: the inference
    in Federer 2.5.11, p. 102, that {u: k(u,v)<=0} is nonempty, since
    a positive function would have positive beta_1 integral. *)
Lemma horizontal_section_nonpositive_point (k : J1 * J2 -> R) (v : J2) :
  is_real_lattice_density phi L mu k -> exists u, (k (u, v) <= 0)%R.
Proof.
move=> hd; have [hmeas hint] := horizontal_section_integral v hd.
pose g := fun u => k (u, v).
apply: contrapT=> hn.
have hpos : forall u, (0 < g u)%R.
  by move=> u; rewrite ltNge; apply/negP=> h; apply: hn; exists u.
pose P := fun n : nat => [set u | (n.+1%:R^-1 < g u)%R].
have hPm : forall n, measure_measurable beta1 (P n).
  by move=> n; exact (real_total_positive_level_measurable hb1 (n.+1%:R^-1)%R hmeas).
have hcov : \bigcup_n P n = setT.
  apply/seteqP; split=> // u _.
  by have [n hn'] := reciprocal_below_positive (hpos u); exists n.
have hlarge : ~ (\bigcup_n P n #<= @setT nat) by rewrite hcov; exact: h1.2.1.
have [n hn'] := cardinal_measure_union_large (@countable_sigma_small J1) hlarge.
have hc : (0 < n.+1%:R^-1 :> R)%R by rewrite invr_gt0 ltr0n.
have := real_total_integral_level_lower_bound hb1 (hPm n) hc hint (fun u => ltW (hpos u))
  (fun u hu => ltW hu).
rewrite /example_beta1 (cardinal_measure_large R hn') mule1 lee_fin.
by rewrite leNgt hc.
Qed.

(** Source for [example_no_density]: the conclusion of Federer 2.5.11,
    p. 102: there exists no phi measurable function k such that
    mu(f)=integral f k d phi whenever f in L. The two cardinality
    estimates card{(u,v): k(u,v)<=0} <= aleph-one and >= aleph-two
    are incompatible. *)
Theorem example_no_density (k : J1 * J2 -> R) : ~ is_real_lattice_density phi L mu k.
Proof.
move=> hd.
pose S := [set p : J1 * J2 | (k p <= 0)%R].
have hS : S #<= @setT J1.
  apply: aleph_one_section_bound h1 (card_lexx _) _ => u.
  exact (vertical_section_small u hd).
have hchoice : forall v, exists u, (k (u, v) <= 0)%R.
  by move=> v; exact (horizontal_section_nonpositive_point v hd).
have h2S : @setT J2 #<= S.
  apply: (@cardinal_bound_of_injection _ _ setT S (fun v => (sval (cid (hchoice v)), v))).
  - move=> v _; exact (svalP (cid (hchoice v))).
  - by move=> v w _ _ [_ ->].
exact (h2.2.1 (card_le_trans h2S hS)).
Qed.

End Counterexample.

(** Source for [federer_2_5_10_negative_answer]: the sentence
    "Example 2.5.11 shows that in general the answer is no" in Federer
    2.5.10, p. 100. Under the cardinal hypotheses of 2.5.11 there are a
    lattice L, a monotone Daniell integral lambda, its L regular measure
    phi, and a Daniell integral mu on L with mu(|f|) <= lambda(|f|), such
    that no phi measurable k represents mu on L. Since L consists of phi
    summable functions, no k represents mu on all phi summable functions. *)
Theorem federer_2_5_10_negative_answer (R : realType) (J1 J2 : choiceType)
    (h1 : is_cardinal_successor (@setT nat) (@setT J1))
    (h2 : is_cardinal_successor (@setT J1) (@setT J2)) :
  exists (L : set (J1 * J2 -> R)) (lambda mu : (J1 * J2 -> R) -> R) (phi : set (J1 * J2) -> \bar R),
    is_function_lattice L /\ is_monotone_daniell_integral L lambda /\
    is_measure phi /\ is_real_integral_functional phi L lambda /\ is_function_lattice_regular L phi /\
    is_daniell_integral L mu /\
    (forall f, L f -> (mu (fun x => `|f x|%R) <= lambda (fun x => `|f x|%R))%R) /\
    (forall f, L f -> summable_real_functions phi f) /\
    forall k : J1 * J2 -> R, ~ is_real_lattice_density phi L mu k.
Proof.
have [phi [hm [hA hr]]] := @example_regular_measure_exists R J1 J2 h1.
exists (@example_lattice R J1 J2 h1), (@example_lambda R J1 J2 h1), (@example_mu R J1 J2 h1), phi.
split; first exact: example_lattice_is_lattice.
split; first exact: example_lambda_monotone_daniell.
split=> //; split=> //; split=> //.
split; first exact: example_mu_daniell.
split; first by move=> f hf; exact: example_mu_dominated.
split; first by move=> f hf; exact (example_lattice_summable hA hf).
by move=> k; exact (example_no_density h2 hm hA hr (k := k)).
Qed.
