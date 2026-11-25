(** Supporting results for Federer (1969), 2.7.18, printed p. 141. The
    printed proof uses, for v - w in L_1(gamma) and g in G, "int |v - w|_g
    dgamma = chi(g) int |v - w| dgamma", where u_g = u o A_g (2.7.1, p.
    122). Here gamma is a K(X) regular measure representing on K(X) a
    functional mu with mu(u o A_g) = chi(g) mu(u) for u in K(X), as for the
    chi covariant measures of 2.7.1. By 2.5.19, p. 113, and 2.4.18, p. 90,
    the image measure A_g#(gamma) represents u |-> mu(u o A_g) = chi(g)
    mu(u) on K(X); it is K(X) regular because A_g is a homeomorphism
    (RegularPushforwardBijection.v); if chi(g) > 0, then chi(g) gamma is a
    K(X) regular measure representing the same functional
    (MeasureScaleIntegral.v). The uniqueness in 2.5.3, p. 94, gives
    A_g#(gamma) = chi(g) gamma, and 2.4.18 gives int u o A_g dgamma = chi(g)
    int u dgamma for every gamma integrable u. The condition chi(g) > 0
    holds whenever mu <> 0, since mu is monotone and chi(g) <> 0 by 2.7.1.
    Federer uses these facts without comment. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionPrecomposition TopologicalGroupUP HomogeneousSpaceUP HomogeneousSpaceLaws
  FunctionLatticeUP LatticeAdditiveFunctional LatticeDominatedDifference VectorFunctionLattice
  MonotoneDaniellIntegralUP CompactSupportFunctionUP CompactSupportFunctionLattice
  CompactUniformNorm DaniellSpacePushforward FunctionLatticeRegularityUP
  FunctionLatticeRegularUniqueness RealIntegralFunctionalUP MeasureUP MeasurePushforward
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  PushforwardIntegral PushforwardMeasurabilityTransfer SummableRealFunctionUP TotalScalarLpUP
  TotalScalarLpFiniteSeminorm TotalLoneSummability TotalScalarPairing CovariantIntegralUP
  CovariantIntegralLaws MeasureScaleIntegral RegularPushforwardBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [precompose_total_integrand_graph]: the graph of
    f o u, viewed as an integrand, is that of the composition of u
    with the integrand f, supporting Federer 2.4.18, p. 90, as used in
    2.7.18, p. 141. *)
Lemma precompose_total_integrand_graph (R : realType) (S T : Type) (u : S -> T) (f : T -> R) x y :
  partial_function_graph (partial_function_precompose u (real_total_integrand f)) x y <->
  partial_function_graph (real_total_integrand (f \o u)) x y.
Proof.
split=> h.
- by apply/real_total_integrand_graph; exact: (real_total_integrand_graph f (u x) y).1 h.
- by apply/(real_total_integrand_graph f (u x) y); exact: (real_total_integrand_graph (f \o u) x y).1 h.
Qed.

Section CovariantMeasureImage.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hG : is_group_laws mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Local Notation K := (@compactly_supported_continuous_functions R X).

(** Source for [covariant_character_positive]: chi(g) > 0 for g in G
    when the monotone chi covariant integral mu is not 0. Federer
    2.7.1, p. 122, gives chi(g) <> 0; monotonicity gives
    chi(g) mu(|u|) = mu(|u| o A_g) >= 0 and mu(|u|) >= |mu(u)| > 0.
    Supporting lemma for 2.7.18, p. 141. *)
Lemma covariant_character_positive (chi : G -> R) (mu : (X -> R) -> R) :
  is_monotone_daniell_integral K mu -> is_covariant_on K A chi mu ->
  (exists u, K u /\ mu u <> 0) -> forall g, 0 < chi g.
Proof.
move=> hm hc [u [hu hmu]] g.
have hV := @compact_support_vector_lattice R X.
have hadd : is_lattice_additive_functional K mu.
  by move=> f1 f2 h1 h2; exact: monotone_daniell_integral_add hm f1 f2 h1 h2.
have hz := compactly_supported_zero_function R X.
have ha : K (fun x => `|u x|).
  have h := lattice_absolute_difference_member hV.1 hu hz.
  by rewrite (_ : (fun x => `|u x|) = (fun x => `|u x - 0|)) //; apply: funext=> x; rewrite subr0.
have hn := vector_function_lattice_negation hV hu.
have hle1 : mu u <= mu (fun x => `|u x|).
  by apply: (monotone_daniell_integral_monotone hm hu ha)=> x; exact: ler_norm.
have hle2 : mu (fun x => - u x) <= mu (fun x => `|u x|).
  by apply: (monotone_daniell_integral_monotone hm hn ha)=> x; rewrite -normrN; exact: ler_norm.
rewrite (vector_lattice_additive_negation hV hadd hu) in hle2.
have hpos : 0 < mu (fun x => `|u x|).
  have hne : 0 < `|mu u| by rewrite normr_gt0; apply/eqP.
  by apply: (lt_le_trans hne); rewrite ler_norml hle1 andbT -lerNl.
have hag := compactly_supported_translate hG hA g ha.
have h0 : 0 <= mu ((fun x => `|u x|) \o A g).
  rewrite -(lattice_additive_zero hV.1 hadd hz).
  by apply: (monotone_daniell_integral_monotone hm hz hag)=> x; exact: normr_ge0.
rewrite (hc _ g ha) pmulr_lge0 // in h0.
rewrite lt_def h0 andbT.
exact: (covariant_character_nonzero hG hA hc hu hmu g).
Qed.

Section Image.
Variables (chi : G -> R) (mu : (X -> R) -> R) (gamma : set X -> \bar R).
Hypothesis hc : is_covariant_on K A chi mu.
Hypothesis hm : is_measure gamma.
Hypothesis hi : is_real_integral_functional gamma K mu.
Hypothesis hr : is_function_lattice_regular K gamma.

(** Source for [covariant_translation_image]: A_g#(gamma) =
    chi(g) gamma whenever chi(g) > 0; the measure form of "A_g#(mu) =
    chi(g) mu" in Federer 2.7.1, p. 122, obtained by the uniqueness of
    K(X) regular representing measures in 2.5.3, p. 94. Supporting
    lemma for 2.7.18, p. 141. *)
Theorem covariant_translation_image g :
  0 < chi g -> measure_pushforward (A g) gamma = measure_scale (chi g) gamma.
Proof.
move=> hg; apply: funext=> S.
have hL := @compactly_supported_continuous_functions_lattice R X.
have hcont := homogeneous_translation_continuous hA g.
have hprop := homogeneous_translation_proper hG hA g.
have hpm := measure_pushforward_is_measure (A g) hm.
have hsm := measure_scale_is_measure hm hg.
have hrep1 : is_real_integral_functional (measure_pushforward (A g) gamma) K
    (fun u => chi g * mu u).
  move=> u hu; have h := @daniell_pushforward_integral R X X (A g) hcont hprop gamma mu hm hi u hu.
  by rewrite /daniell_pushforward (hc g hu) in h.
have hrep2 := measure_scale_represents hm hg hi.
have hreg1 : is_function_lattice_regular K (measure_pushforward (A g) gamma).
  have hK : forall f, K f -> K (f \o A (inv g)).
    by move=> f hf; have := compactly_supported_translate hG hA (inv g) hf.
  exact: (bijection_pushforward_regular (homogeneous_translation_inverse_left hG hA g)
    (homogeneous_translation_inverse_right hG hA g) hK hr).
have hreg2 := measure_scale_regular hm hg hr.
exact: (function_lattice_regular_representation_unique hL hpm hsm hrep1 hrep2 hreg1 hreg2 S).
Qed.

(** Source for [covariant_translation_integral]: int u o A_g dgamma =
    chi(g) int u dgamma whenever u is gamma integrable and chi(g) > 0,
    Federer 2.4.18(1), p. 90, with A_g#(gamma) = chi(g) gamma; used for
    int |v - w|_g dgamma = chi(g) int |v - w| dgamma in 2.7.18,
    p. 141. *)
Theorem covariant_translation_integral g (F : partial_function X (extended_real_line R)) a :
  0 < chi g -> is_measure_integral gamma F a ->
  is_measure_integral gamma (partial_function_precompose (A g) F) ((chi g)%:E * a)%E.
Proof.
move=> hg hF.
have himg := covariant_translation_image hg.
have hI := measure_scale_integral hm hg hF.
rewrite -himg in hI.
have hinj : injective (A g) := can_inj (homogeneous_translation_inverse_left hG hA g).
have hmeas : is_measure_measurable_function gamma (partial_function_precompose (A g) F).
  apply: measurable_function_pushforward_precompose hinj _.
  by rewrite himg; exact (measure_scale_measurable_function hm (chi g) hF.1).
exact: (measure_pushforward_integral_iff hm hmeas _).2 hI.
Qed.

(** Source for [covariant_translation_lone]: v o A_g belongs to
    L_1(gamma), and int |v o A_g| dgamma = chi(g) int |v| dgamma,
    whenever v in L_1(gamma) and chi(g) > 0; Federer 2.7.18, p. 141,
    "|v - w|_g", with 2.4.18(1), p. 90. *)
Theorem covariant_translation_lone g (v : X -> R) :
  0 < chi g -> total_scalar_lp gamma 1 v ->
  total_scalar_lp gamma 1 (v \o A g) /\
  finite_total_scalar_lp_norm gamma 1 (v \o A g) = chi g * finite_total_scalar_lp_norm gamma 1 v.
Proof.
move=> hg hv.
have [a ha] := total_lone_summable_real hm hv.
have hva : is_measure_integral gamma (real_total_integrand (v \o A g)) ((chi g * a)%:E).
  rewrite EFinM; apply: (measure_integral_graph_equivalent _ (covariant_translation_integral hg ha)).
  exact: precompose_total_integrand_graph.
have hvg : total_scalar_lp gamma 1 (v \o A g).
  have hs : summable_real_functions gamma (v \o A g) by exists (chi g * a).
  exact (summable_real_total_lone hm hs).
split=> //.
have hN := total_scalar_lone_absolute_integral hm hv.
have hNg := total_scalar_lone_absolute_integral hm hvg.
have hNt : is_measure_integral gamma (real_total_integrand (fun x => `|(v \o A g) x|))
    ((chi g * finite_total_scalar_lp_norm gamma 1 v)%:E).
  rewrite EFinM; apply: (measure_integral_graph_equivalent _ (covariant_translation_integral hg hN)).
  exact: (precompose_total_integrand_graph (A g) (fun x => `|v x|)).
by have := measure_integral_unique hNg hNt=> -[].
Qed.

End Image.
End CovariantMeasureImage.
