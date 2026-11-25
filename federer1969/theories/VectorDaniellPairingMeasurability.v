(** Federer (1969), 2.5.12, pp. 104–105, fourth paragraph of the proof:
    every member w of Q is phi measurable, because alpha o w belongs to L
    for alpha in E* and E is separable. Federer associates with y in D a
    member mu_y of U* with <y, mu_y> = nu(y), so that nu(z) = sup{<z, mu_y>
    : y in D}; the norming functionals come from the Hahn-Banach theorem of
    1.10.5. The functions x |-> nu(w(x) - p) with p in E are therefore
    countable suprema of measurable functions, and the balls with centres in
    D and rational radii form a countable base of E; hence w is phi
    measurable. The measurability and summability of <eta, k>, in the sixth
    paragraph, are proved in PartialDualPairing.v and
    VectorDaniellLocalBoundPairing.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricScaleContinuity
  NormMetricContinuity PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  PartialAbsolutePartsGraph PartialExtendedOrderLoci FunctionLatticeUP FunctionLatticeLaws MeasureUP
  MeasureSplit MeasureFiniteClosure MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableAlmostModification MeasureCountableClosure MeasureIntegralUP MeasureIntegralComparison
  MeasureIntegralAbsolute MeasureAbsoluteSummability RealIntegralFunctionalUP
  FunctionLatticeRegularityUP CountablyMeasurableUP SummableRealFunctionUP SummableRealNormed
  TotalScalarLpUP TotalScalarMeasurability RealLatticeDensityUP MeasureStepIntegralIdentification
  PartialFunctionSupremumUP MeasurableCountableSupremum MeasurableTotalLimits
  ExtendedRealReciprocalBounds ContinuousRealFunctional VectorDaniellHypotheses
  VectorDaniellRationalSpan VectorDaniellDualExtension VectorDaniellDualDensity
  VectorDaniellWeakMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_total_dominated_integral]: a measurable real
    function dominated by a function with finite integral has a finite
    integral bounded by it, 2.4.4 and 2.4.6, pp. 82–83, used for
    <eta, k> in Federer 2.5.12, p. 105. *)
Lemma real_total_dominated_integral (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (hm : is_measure mu) (F G : X -> R) (b : R) :
  is_measure_measurable_function mu (real_total_integrand F) ->
  is_measure_integral mu (real_total_integrand G) b%:E ->
  (forall x, `|F x| <= G x) ->
  exists c : R, is_measure_integral mu (real_total_integrand F) c%:E /\ `|c| <= b.
Proof.
move=> hF hG hle.
have hdom : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (real_total_integrand F)) (real_total_integrand G)).
  apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm)) => x _.
  exists (`|F x|)%:E, (G x)%:E; split.
    exists (F x)%:E; split; first by apply/real_total_integrand_graph.
    by rewrite abse_EFin.
  by split; [apply/real_total_integrand_graph | rewrite lee_fin].
have [[c hci] _] := measure_dominated_summable hm hF (ex_intro _ b hG) hdom.
have [d [hdi hcd]] := measure_integral_absolute_bound hm hci.
have hdb := measure_integral_monotone hm hdi hG hdom.
exists c; split=> //.
by have hh := le_trans hcd hdb; rewrite abse_EFin lee_fin in hh.
Qed.

(** Source for [real_line_cvg_eps]: the epsilon criterion for the
    convergence of a real sequence in the real line metric, used for the
    pointwise limits of Federer 2.5.12, p. 105. *)
Lemma real_line_cvg_eps (R : realType) (u : nat -> R) (l : R) :
  (forall eps, 0 < eps -> exists M, forall n, (M <= n)%N -> `|u n - l| < eps) ->
  (fun n => (u n : real_line_metric R)) @ \oo --> (l : real_line_metric R).
Proof.
move=> h; apply/cvg_ballP => eps heps.
have [M hM] := h eps heps.
exists M => // n hn; rewrite ballEmdist /= real_line_metric_distanceE distrC; exact: hM.
Qed.

Section PairingMeasurability.
Variable R : realType.
Variable X : choiceType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable L : set (X -> R).
Variable Q : set (X -> E).
Variable T : (X -> E) -> R.
Hypothesis hL : is_function_lattice L.
Hypothesis hQ : is_vector_function_space Q.
Hypothesis hM : is_vector_lattice_module hN L Q.
Hypothesis hT : is_vector_variation_functional N L Q T.

Local Notation Lp := (positive_function_lattice L).
Local Notation lam := (variation_integral N Q T).

Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Hypothesis hrep : is_real_integral_functional phi Lp lam.
Hypothesis hreg : is_function_lattice_regular Lp phi.
Hypothesis hX : measure_countably_measurable phi setT.

Variable D : set E.
Hypothesis hD : is_rational_dense_subspace hN D.
Variable kk : E -> X -> R.
Hypothesis hkk : is_component_density_family N L T phi kk.

Local Notation k := (vector_density N D kk).

(** Source for [lattice_positive_measurable]: every member of L+ is phi
    measurable, Federer 2.5.2, p. 93, used in 2.5.12, p. 104. *)
Lemma lattice_positive_measurable (f : X -> R) : Lp f ->
  is_measure_measurable_function phi (partial_function_total (f : X -> real_line_metric R)).
Proof.
move=> hf; have hi := hrep hf.
exact (total_scalar_real_measurable hphi (real_integrand_measurable_scalar_norm hphi hi.1)).
Qed.

(** Source for [lattice_measurable]: every member of L is phi
    measurable, as the difference of the members f - inf{f, 0} and
    -inf{f, 0} of L+, Federer 2.5.12, p. 104. *)
Lemma lattice_measurable (f : X -> R) : L f ->
  is_measure_measurable_function phi (partial_function_total (f : X -> real_line_metric R)).
Proof.
move=> hf.
have h0 : L (fun _ => 0) := function_lattice_zero hL hf.
have hm : L (fun x => Order.min (f x) 0) := function_lattice_truncation hL (lexx 0) hf.
have hp : Lp (fun x => f x - Order.min (f x) 0).
  split; first by apply: (function_lattice_ordered_difference hL hm hf) => x; rewrite ge_min lexx.
  by move=> x; rewrite subr_ge0 ge_min lexx.
have hn : Lp (fun x => 0 - Order.min (f x) 0).
  split; first by apply: (function_lattice_ordered_difference hL hm h0) => x; rewrite ge_min lexx orbT.
  by move=> x; rewrite subr_ge0 ge_min lexx orbT.
have h1 := real_total_scalar_measurable hphi (lattice_positive_measurable hp).
have h2 := real_total_scalar_measurable hphi (lattice_positive_measurable hn).
have hc : continuous (fun p : (real_line_metric R * real_line_metric R)%type => (p.1 - p.2 : real_line_metric R)).
  change (continuous (fun p : R^o * R^o => p.1 - p.2)).
  by move=> p; apply: cvgB; [exact: cvg_fst|exact: cvg_snd].
have h3 := total_scalar_continuous_binary_operation hphi hc h1 h2.
have -> : f = (fun x => (f x - Order.min (f x) 0) - (0 - Order.min (f x) 0)).
  by apply/funext=> x; ring.
exact (total_scalar_real_measurable hphi h3).
Qed.

(** Source for [norming_family_exists]: with every y in E is associated
    mu_y in U* with <y, mu_y> = nu(y), by the Hahn-Banach theorem,
    Federer 1.10.5, p. 48, as used in 2.5.12, p. 104. *)
Lemma norming_family_exists :
  exists mu : E -> E -> R, forall y, dual_unit_ball hN (mu y) /\ mu y y = N y.
Proof.
have h : forall y : E, exists a : E -> R, dual_unit_ball hN a /\ a y = N y.
  move=> y; have [a [hac [hab hay]]] := continuous_norming_real_functional hN y.
  exists (fun z => a z); split=> //.
  apply/dual_unit_ball_bound; split=> //; split=> //.
  by move=> c u v; rewrite linearD linearZ.
exists (fun y => sval (cid (h y))) => y; exact: svalP (cid (h y)).
Qed.

Variable mu : E -> E -> R.
Hypothesis hmu : forall y, dual_unit_ball hN (mu y) /\ mu y y = N y.

(** Source for [norm_dense_has_sup]: the set {<z, mu_y> : y in D} is
    nonempty and bounded by nu(z), Federer 2.5.12, p. 104. *)
Lemma norm_dense_has_sup (v : E) : has_sup [set mu y v | y in D].
Proof.
split; first by exists (mu 0 v); exists 0 => //; exact: hD.2.2.1.
exists (N v) => _ [y _ <-]; apply: le_trans (ler_norm _) _.
by have /dual_unit_ball_bound [_ hb] := (hmu y).1; exact: hb.
Qed.

(** Source for [norm_dense_sup]: nu(z) = sup{<z, mu_y> : y in D},
    because <z, mu_y> = nu(y) - <y - z, mu_y> >= nu(y) - nu(y - z),
    Federer 2.5.12, p. 104. *)
Lemma norm_dense_sup (v : E) : N v = sup [set mu y v | y in D].
Proof.
have hs := norm_dense_has_sup v.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ge_sup hs.1 _ => _ [y _ <-]; apply: le_trans (ler_norm _) _.
  by have /dual_unit_ball_bound [_ hb] := (hmu y).1; exact: hb.
apply/ler_addgt0Pr => eps heps.
have he2 : 0 < eps / 2 by lra.
have [y [hy hvy]] := dense_approximation hD.2.1 v he2.
have /dual_unit_ball_bound [hyd hyb] := (hmu y).1.
have h1 := sup_upper_bound hs (imageP (fun y0 => mu y0 v) hy).
have h2 := hyb (y - v).
rewrite (dual_space_sub _ _ hyd) (hmu y).2 ler_norml in h2; case/andP: h2 => h2a h2b.
have ht := real_seminorm_triangle hN.1 (v - y) y.
rewrite subrK in ht.
rewrite (real_seminorm_subtract hN.1 y v) in h2b h2a.
simpl in h1; lra.
Qed.

(** Source for [vector_member_norm_measurable]: for w in Q and p in E
    the function x -> nu(w(x) - p) is phi measurable, as the supremum of
    the functions <w - p, mu_y> with y in D, which belong to L up to a
    constant, Federer 2.5.12, p. 104. *)
Lemma vector_member_norm_measurable (w : X -> E) (p : E) : Q w ->
  is_measure_measurable_function phi (real_total_integrand (fun x => N (w x - p))).
Proof.
move=> hw.
apply: (measurable_countable_supremum hphi (D := D)
  (f := fun y => real_total_integrand (fun x => mu y (w x) - mu y p))).
- exact: hD.1.
- move=> y _.
  have hl : L (fun x => mu y (w x)) := vector_lattice_module_pairing hM hw (hmu y).1.1.
  have h1 := real_total_scalar_measurable hphi (lattice_measurable hl).
  have hc : continuous (fun t : real_line_metric R => (t - mu y p : real_line_metric R)).
    change (continuous (fun t : R^o => t - mu y p)).
    by move=> t; apply: cvgB; [exact: cvg_id | exact: cvg_cst].
  have h2 := total_scalar_continuous_operation hphi hc h1.
  exact (measurable_partial_real_embedding hphi (total_scalar_real_measurable hphi h2)).
- constructor.
  + apply/seteqP; split=> x _.
      by move=> y _; exists (mu y (w x) - mu y p)%:E; apply/real_total_integrand_graph.
    by exists (N (w x - p))%:E; apply/real_total_integrand_graph.
  + move=> x t ht z [y [hy hz]].
    move/real_total_integrand_graph: ht => <-; move/real_total_integrand_graph: hz => <-.
    have /dual_unit_ball_bound [hyd hyb] := (hmu y).1.
    rewrite lee_fin -(dual_space_sub _ _ hyd).
    exact: le_trans (ler_norm _) (hyb _).
  + move=> x t ht b hb; move/real_total_integrand_graph: ht => <-.
    have h0 : ((mu 0 (w x) - mu 0 p)%:E <= b)%E.
      by apply: hb; exists 0; split; [exact: hD.2.2.1 | apply/real_total_integrand_graph].
    case: b hb h0 => [r| |] hb h0.
    * rewrite lee_fin (norm_dense_sup (w x - p)).
      apply: ge_sup (norm_dense_has_sup _).1 _ => _ [y hy <-].
      have /dual_unit_ball_bound [hyd _] := (hmu y).1.
      rewrite (dual_space_sub _ _ hyd) -lee_fin; apply: hb; exists y; split=> //.
      by apply/real_total_integrand_graph.
    * exact: leey.
    * by have := lt_le_trans (ltNyr _) h0; rewrite ltxx.
Qed.

Variable e : nat -> E.
Hypothesis he1 : forall n, D (e n).
Hypothesis he2 : forall y, D y -> exists n, e n = y.

(** Source for [vector_member_ball_preimage_measurable]: the inverse
    image under w in Q of a ball is phi measurable, Federer 2.5.12,
    p. 104. *)
Lemma vector_member_ball_preimage_measurable (w : X -> E) (p : E) (r : R) : Q w ->
  measure_measurable phi ((w : X -> real_norm_metric_space hN) @^-1` ball (p : real_norm_metric_space hN) r).
Proof.
move=> hw.
have hm := vector_member_norm_measurable p hw.
have hm' := total_scalar_real_measurable hphi (real_integrand_measurable_scalar_norm hphi hm).
have hU : open [set t : real_line_metric R | t < r] by exact: (@open_lt R r).
have := measurable_function_open_preimage hm' hU.
rewrite partial_function_total_preimage.
have -> : (w : X -> real_norm_metric_space hN) @^-1` ball (p : real_norm_metric_space hN) r
    = (fun x => N (w x - p)) @^-1` [set t | t < r].
  apply/seteqP; split=> x; rewrite /= ballEmdist /= real_norm_metric_distanceE;
    by rewrite (real_seminorm_subtract hN.1).
by [].
Qed.

(** Source for [vector_member_measurable_enumerated]: every member of Q
    is phi measurable, the balls with centres in D and rational radii
    forming a countable base of E, Federer 2.5.12, p. 104. *)
Theorem vector_member_measurable_enumerated (w : X -> E) : Q w ->
  is_measure_measurable_function phi (partial_function_total (w : X -> real_norm_metric_space hN)).
Proof.
move=> hw.
apply: (measurable_relative_countable_base hphi (S := setT)
  (B := fun j : nat * rat => ball (e j.1 : real_norm_metric_space hN) (ratr j.2))).
- by [].
- move=> V hV z _ hVz.
  have hn : nbhs (z : real_norm_metric_space hN) V by rewrite openE in hV; exact: hV _ hVz.
  have [eps heps hball] := proj1 (metricType_numDomainType.nbhs_mdistP (z : real_norm_metric_space hN) _) hn.
  have heps' : (0 : R) < eps := heps.
  have he3 : 0 < eps / 3 by lra.
  have [y [hy hzy]] := dense_approximation hD.2.1 z he3.
  have [n hn'] := he2 hy.
  have h13 : eps / 3 < 2 * eps / 3 by lra.
  have [q hq] := rat_in_itvoo h13.
  have /andP [hq1 hq2] : eps / 3 < ratr q < 2 * eps / 3 := hq.
  exists (n, q); split.
    rewrite /= hn' ballEmdist /= real_norm_metric_distanceE (real_seminorm_subtract hN.1).
    lra.
  move=> v [hv _]; apply: hball.
  move: hv; rewrite /= hn' ballEmdist /= !real_norm_metric_distanceE => hv.
  have ht := real_seminorm_triangle hN.1 (z - y) (y - v).
  rewrite addrA subrK in ht.
  lra.
- move=> [n q] /=; exact: vector_member_ball_preimage_measurable.
Qed.

End PairingMeasurability.
