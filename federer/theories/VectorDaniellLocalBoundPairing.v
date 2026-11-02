(** Federer (1969), 2.5.12, p. 103, last two sentences, and 2.5.14, p. 108:
    "If eta is a phi measurable function mapping X into E, then <eta, k> is
    phi measurable; if also nu o eta is phi summable, then <eta, k> is phi
    summable." Federer's density k satisfies nu*[k(x)] = 1 for phi almost
    all x in 2.5.12, and only for Phi locally almost all x in the Radon
    modification of 2.5.14, where k is only locally Phi almost unique. The
    conclusions are proved here for every weakly measurable k with nu*[k(x)]
    <= 1 for locally almost all x; ordinary almost everywhere bounds are a
    special case. The proof replaces k by zero on the locally null
    exceptional set Z; the modified density takes values in the dual unit
    ball U* everywhere, as on p. 104, so PartialDualPairing.v applies. The
    pairings with k and with the modification differ only on Z.
    Measurability is checked by finite Caratheodory tests (2.1.2, p. 54).
    For summability, the set where eta does not vanish is a countable union
    of the sets {nu o eta > 1/(n+1)}, which have finite measure by the
    estimate of 2.4.12, p. 86, hence it meets Z in a null set. The
    representation formula of k is not needed for these conclusions. The
    local erratum has no entry for pp. 103-108 affecting these sentences. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground
  PartialFunctionUP PartialFunctionBasic PartialNormPower RealPower
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralAlmostEquality
  MeasureGauge MeasureNormPowerMarkov SummableRealFunctionUP
  LocallyNullMeasureUP LocallyNullMeasureLaws LocallyNullMeasureModification
  VectorDaniellHypotheses VectorDaniellDualExtension VectorDaniellRepresentationUP
  PartialDualPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_partial_locally_null_modification]:
    supporting local version of the null-modification remark of
    Federer 2.3.2, p. 73, for partial functions, used for the
    modified density of 2.5.14, p. 108. Only open preimages are
    compared, by the finite-test criterion of 2.1.2, p. 54. *)
Lemma measurable_partial_locally_null_modification (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X Y) (Z : set X) :
  measure_locally_null mu Z ->
  (forall x, ~ Z x -> forall y, partial_function_graph f x y <-> partial_function_graph g x y) ->
  measure_almost_everywhere mu (partial_function_domain g) ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g.
Proof.
move=> hZ he hd hf; constructor=> // U hU.
apply: (@measurable_set_locally_null_modification R X mu hm _ _ Z hZ _
  (measurable_function_open_preimage hf hU))=> x hx.
split=> [[y [hy hu]]|[y [hy hu]]]; exists y; split=> //.
- exact: (proj1 (he x hx y)).
- exact: (proj2 (he x hx y)).
Qed.

Section LocalBound.
Variable R : realType.
Variable X : choiceType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.

(** Source for [zero_weak_dual_exists]: the zero functional is a member
    of E*, Federer 2.5.12(2), p. 102, with nu*(0) <= 1, so that it lies
    in the dual unit ball U* of p. 104. Supporting lemma for the
    modification of k on an exceptional set. *)
Lemma zero_weak_dual_exists : exists z : weak_dual_space hN,
  (forall y, val z y = 0) /\ dual_norm N (val z) <= 1.
Proof.
have h0 : dual_space hN (fun _ : E => (0 : R)).
  split; first by move=> a u v; rewrite mulr0 addr0.
  exact: cst_continuous.
exists (exist _ (fun _ : E => (0 : R)) (mem_set h0)); split=> //.
by apply: dual_norm_le_one=> v; rewrite normr0 (real_seminorm_nonnegative hN.1).
Qed.

(** Source for [partial_dual_pairing_domain]: the pairing <eta, k>
    of Federer 2.5.12, p. 103, is defined exactly where eta is.
    Supporting lemma. *)
Lemma partial_dual_pairing_domain (k : X -> weak_dual_space hN) (f : partial_function X E) x :
  partial_function_domain (partial_dual_pairing k f) x <-> partial_function_domain f x.
Proof.
split=> [[z /partial_dual_pairing_graph [y [hy _]]]|[y hy]]; first by exists y.
by exists (val (k x) y)%:E; apply/partial_dual_pairing_graph; exists y.
Qed.

(** Source for [partial_dual_pairing_local_modification]: changing the
    density k on a locally null set preserves measurability of the
    pairing <eta, k>, supporting Federer 2.5.12, p. 103, as modified in
    2.5.14, p. 108. *)
Lemma partial_dual_pairing_local_modification (k l : X -> weak_dual_space hN)
    (f : partial_function X E) (Z : set X) :
  measure_locally_null phi Z -> (forall x, ~ Z x -> l x = k x) ->
  measure_almost_everywhere phi (partial_function_domain f) ->
  is_measure_measurable_function phi (partial_dual_pairing l f) ->
  is_measure_measurable_function phi (partial_dual_pairing k f).
Proof.
move=> hZ he hd hl.
apply: (@measurable_partial_locally_null_modification R X _ phi hphi _ _ Z hZ _ _ hl).
- move=> x hx z; rewrite !partial_dual_pairing_graph (he x hx); exact: iff_refl.
- apply: (measure_almost_everywhere_mono hphi _ hd)=> x hx.
  exact: (proj2 (partial_dual_pairing_domain k f x)).
Qed.

(** Source for [summable_norm_nonzero_locus_locally_null]: if
    nu o eta is phi summable, then the set where eta does not vanish
    meets every locally null set in a null set. Supporting lemma for
    the summability assertion of Federer 2.5.12, p. 103, in the local
    setting of 2.5.14, p. 108: the sets {nu o eta > 1/(n+1)} have
    finite measure by the estimate of 2.4.12, p. 86. *)
Lemma summable_norm_nonzero_locus_locally_null (f : partial_function X (real_norm_metric_space hN))
    (a : R) (Z : set X) :
  is_measure_measurable_function phi f ->
  is_measure_integral phi (partial_norm_power N 1 f) a%:E ->
  measure_locally_null phi Z ->
  phi (Z `&` [set x | exists y, partial_function_graph f x y /\ y != 0]) = 0%E.
Proof.
move=> hf hi hZ.
pose S n := partial_norm_superlevel N f (n.+1%:R^-1 : R)%:E.
have hlow : measure_lower_integral phi (partial_norm_power N 1 f) = a%:E.
  exact: (measure_lower_integral_unique (measure_lower_integral_specification phi _) hi.2.2).
have hfin n : (phi (S n) < +oo)%E.
  have hr : 0 < n.+1%:R^-1 :> R by rewrite invr_gt0 ltr0n.
  have hb := @measure_norm_power_superlevel_bound R X E N hN phi hphi 1 _ f ltr01 (ltW hr) hf.
  rewrite hlow real_power_one_exponent ?(ltW hr) // in hb.
  rewrite ltNge leye_eq; apply/negP=> /eqP hS; move: hb.
  by rewrite hS mulry gtr0_sg // mul1e leye_eq.
have hnull : phi (\bigcup_(n in setT) (S n `&` Z)) = 0%E.
  apply: (@measure_null_countable_union R X [the choiceType of (nat : Type)] phi hphi setT
    (fun n => S n `&` Z)); first exact: countableP.
  move=> n _; exact: hZ _ (hfin n).
apply: (measure_null_subset hphi _ hnull)=> x [hx [y [hy hy0]]].
have hpos : 0 < N y by rewrite (real_norm_positive hN.1 hN.2).
have [n hn] := ltr_add_invr hpos; rewrite add0r in hn.
exists n=> //; split=> //; exists y; split=> //; rewrite /= lte_fin; exact: hn.
Qed.

(** Source for [local_bound_dual_pairing_consequences]: the last two
    sentences of Federer 2.5.12, p. 103, for every weakly phi
    measurable k with nu*[k(x)] <= 1 for phi locally almost all x, the
    situation of the Radon modification in 2.5.14, p. 108. Partial
    measurable eta is allowed, and summability includes the bound of
    the integral by the integral of nu o eta. Local correction of the
    previously formalised versions, which required nu*[k(x)] <= 1 at
    every x; the representation formula of k is not used. *)
Theorem local_bound_dual_pairing_consequences (hsep : is_separable_normed_space hN)
    (k : X -> weak_dual_space hN) (eta : partial_function X (real_norm_metric_space hN)) :
  is_measure_measurable_function phi (partial_function_total k) ->
  measure_locally_almost_everywhere phi [set x | dual_norm N (val (k x)) <= 1] ->
  is_measure_measurable_function phi eta ->
  is_measure_measurable_function phi (partial_dual_pairing k eta) /\
  (forall a : R, is_measure_integral phi (partial_norm_power N 1 eta) a%:E ->
    exists c : R, is_measure_integral phi (partial_dual_pairing k eta) c%:E /\ `|c| <= a).
Proof.
move=> hk hb heta.
pose Z := ~` [set x | dual_norm N (val (k x)) <= 1].
have hZ : measure_locally_null phi Z := hb.
have [z [hz0 hz1]] := zero_weak_dual_exists.
pose l x := if pselect (dual_norm N (val (k x)) <= 1) then k x else z.
have hlk x : ~ Z x -> l x = k x.
  move=> hx; rewrite /l; case: pselect=> // hn; case: hx=> hy; exact: hn hy.
have hl : is_measure_measurable_function phi (partial_function_total l).
  apply: (@measurable_total_locally_null_modification R X _ phi hphi k l Z hZ _ hk).
  by move=> x hx; rewrite hlk.
have hlb x : dual_norm N (val (l x)) <= 1 by rewrite /l; case: pselect.
have [hlm hls] := @partial_dual_pairing_measurable_summable R X E N hN hsep phi hphi l eta hl hlb heta.
have hd := measurable_function_domain heta.
split.
  exact: (partial_dual_pairing_local_modification hZ hlk hd hlm).
move=> a hi; have [c [hc hca]] := hls a hi.
exists c; split=> //.
apply: (measure_integral_almost_equal hphi hc).
have hnz := summable_norm_nonzero_locus_locally_null heta hi hZ.
have hgood : measure_almost_everywhere phi
    (partial_function_domain eta `&` ~` (Z `&` [set x | exists y, partial_function_graph eta x y /\ y != 0])).
  apply: (measure_almost_everywhere_and hphi hd); by rewrite /measure_almost_everywhere setCK.
apply: (measure_almost_everywhere_mono hphi _ hgood)=> x [[y hy] hx].
exists (val (l x) y)%:E; split; first by apply/partial_dual_pairing_graph; exists y.
apply/partial_dual_pairing_graph; exists y; split=> //.
case: (pselect (Z x))=> hZx; last by rewrite (hlk x hZx).
have hy0 : y = 0.
  apply/eqP; apply: contrapT=> hne; apply: hx; split=> //; exists y; split=> //; exact/negP.
by rewrite hy0 (dual_space_zero (set_valP (k x))) (dual_space_zero (set_valP (l x))).
Qed.

(** Source for [almost_bound_dual_pairing_consequences]: the last two
    sentences of Federer 2.5.12, p. 103, for every weakly measurable
    k with nu*[k(x)] <= 1 for phi almost all x. Corollary of the local
    version, since null sets are locally null. *)
Theorem almost_bound_dual_pairing_consequences (hsep : is_separable_normed_space hN)
    (k : X -> weak_dual_space hN) (eta : partial_function X (real_norm_metric_space hN)) :
  is_measure_measurable_function phi (partial_function_total k) ->
  measure_almost_everywhere phi [set x | dual_norm N (val (k x)) <= 1] ->
  is_measure_measurable_function phi eta ->
  is_measure_measurable_function phi (partial_dual_pairing k eta) /\
  (forall a : R, is_measure_integral phi (partial_norm_power N 1 eta) a%:E ->
    exists c : R, is_measure_integral phi (partial_dual_pairing k eta) c%:E /\ `|c| <= a).
Proof.
move=> hk hb heta.
apply: (local_bound_dual_pairing_consequences hsep hk _ heta).
exact: (measure_null_is_locally_null hphi hb).
Qed.

(** Source for [vector_daniell_almost_unit_pairing_consequences]: the
    last two sentences of Federer 2.5.12, p. 103, for every density k
    as asserted there: k is weakly phi measurable, represents T, and
    nu*[k(x)] = 1 for phi almost all x. Only weak measurability and the
    almost-everywhere norm condition are used; the everywhere unit-ball
    choice made on p. 104 is not required. Direct formalisation. *)
Theorem vector_daniell_almost_unit_pairing_consequences (hsep : is_separable_normed_space hN)
    (Q : set (X -> E)) (T : (X -> E) -> R) (k : X -> weak_dual_space hN)
    (eta : partial_function X (real_norm_metric_space hN)) :
  is_vector_daniell_density phi Q T k ->
  measure_almost_everywhere phi [set x | dual_norm N (val (k x)) = 1] ->
  is_measure_measurable_function phi eta ->
  is_measure_measurable_function phi (partial_dual_pairing k eta) /\
  (forall a : R, is_measure_integral phi (partial_norm_power N 1 eta) a%:E ->
    exists c : R, is_measure_integral phi (partial_dual_pairing k eta) c%:E /\ `|c| <= a).
Proof.
move=> hk hu heta.
apply: (almost_bound_dual_pairing_consequences hsep (vector_daniell_density_measurable hk) _ heta).
by apply: (measure_almost_everywhere_mono hphi _ hu)=> x /= ->.
Qed.

(** Source for [radon_vector_local_unit_pairing_consequences]: the
    conclusions of Federer 2.5.12, p. 103, retained in the Radon
    modification of 2.5.14, p. 108, where the density k is only
    locally determined: k is weakly Phi measurable, represents T, and
    nu*[k(x)] = 1 for Phi locally almost all x. No Radon hypothesis is
    needed for these conclusions, and the representation formula is not
    used. Direct formalisation. *)
Theorem radon_vector_local_unit_pairing_consequences (hsep : is_separable_normed_space hN)
    (Q : set (X -> E)) (T : (X -> E) -> R) (k : X -> weak_dual_space hN)
    (eta : partial_function X (real_norm_metric_space hN)) :
  is_vector_daniell_density phi Q T k ->
  measure_locally_almost_everywhere phi [set x | dual_norm N (val (k x)) = 1] ->
  is_measure_measurable_function phi eta ->
  is_measure_measurable_function phi (partial_dual_pairing k eta) /\
  (forall a : R, is_measure_integral phi (partial_norm_power N 1 eta) a%:E ->
    exists c : R, is_measure_integral phi (partial_dual_pairing k eta) c%:E /\ `|c| <= a).
Proof.
move=> hk hu heta.
apply: (local_bound_dual_pairing_consequences hsep (vector_daniell_density_measurable hk) _ heta).
apply: (measure_locally_null_subset hphi _ hu)=> x hx hn; apply: hx.
by rewrite /= hn.
Qed.

End LocalBound.
