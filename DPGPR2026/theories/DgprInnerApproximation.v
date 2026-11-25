(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    lem:inner (section "The mass bound"): inner approximation by compact
    m rectifiable sets. Suppose M ⊆ R^n is a Borel set which is
    countably (H^m, m) rectifiable, H^m(M) < ∞, θ is H^m ⌞ M summable and
    nonnegative on M, μ = (H^m ⌞ M) ⌞ θ (Federer 2.4.10) and 0 < ε < ∞.
    Then there is a compact m rectifiable set E ⊆ M with μ(R^n ∖ E) < ε.
    The proof follows the blueprint. The closures of the countably many
    m rectifiable sets covering H^m almost all of M are compact and
    m rectifiable (Federer 3.2.14, through the closure of a Lipschitzian
    image of a bounded set); a finite union F of them satisfies
    μ(R^n ∖ F) < ε/2 (2.1.3(5), 2.2.2); a closed set E ⊆ M ∩ F with
    μ((M ∩ F) ∖ E) < ε/2 exists by 2.2.2. The general statement
    [dgpr_inner_approximation_measure] holds for every finite measure μ
    over R^n for which the Borel sets are measurable and which vanishes
    on the sets A with H^m(M ∩ A) = 0. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RectifiableSetUP RectifiableElementary
  RectifiableUnion RectifiableClosure MetricBoundedClosureLaws PartialLipschitzBoundedImage
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP
  TopologicalBorel BorelClosedApproximation ClosedApproximationUP MeasurePrefixComplementLimit
  SetSequenceDisjointification CountableFamilyEnumeration ExtendedRealOrderLimit
  BorelRegularMeasureUP PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci MeasureIntegralUP
  MeasureIntegralUniqueness MeasureDensity MeasureDensityUP MeasureDensityNullSets DensityCharacteristicIntegral
  MeasureRestriction SummableRealFunctionUP ExtendedRealOrderTopology PartialZeroExtension PartialZeroExtensionLaws MeasureSubsetIntegral
  PartialFunctionExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section InnerApproximation.
Variable R : realType.
Variables n m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation H := (@hausdorff_measure R X m).

(** Source for [dgpr_rectifiable_closure_compact]: blueprint lem:inner,
    proof, first two sentences: the closure F of an m rectifiable subset
    of R^n is compact and m rectifiable (Federer 3.2.14; for m ≥ 1 the
    set is the image of a bounded set under a Lipschitzian map, so its
    closure is bounded and closed, and for m = 0 it is finite). *)
Lemma dgpr_rectifiable_closure_compact (F : set X) :
  is_m_rectifiable m F -> compact (closure F) /\ is_m_rectifiable m (closure F).
Proof.
move=> hF; split; last exact: rectifiable_closure.
move: hF; case: m => [|k] hF.
- have hc : closed F := proj1 (@accessible_finite_set_closed X)
    (hausdorff_accessible (@metric_hausdorff R X)) F hF.
  by rewrite -((closure_id F).1 hc); exact: finite_compact.
- have [f [hb [[L hL] hr]]] := hF.
  have hB := partial_lipschitz_bounded_image hL hb.
  rewrite hr in hB.
  exact: euclidean_bounded_closure_compact hB.
Qed.

(** Source for [dgpr_prefix_compact_rectifiable]: blueprint lem:inner,
    proof: the finite union F = F_0 ∪ ... ∪ F_(j-1) of compact
    m rectifiable sets is compact and m rectifiable (Federer 3.2.14). *)
Lemma dgpr_prefix_compact_rectifiable (G : nat -> set X) :
  (forall i, compact (G i) /\ is_m_rectifiable m (G i)) ->
  forall j, compact (set_sequence_prefix G j) /\ is_m_rectifiable m (set_sequence_prefix G j).
Proof.
move=> hG; elim=> [|j [hc hr]].
- rewrite set_sequence_prefix_zero; split; first exact: compact0.
  exact: rectifiable_empty.
- rewrite set_sequence_prefix_succ; have [hcj hrj] := hG j; split.
  + exact: compactU.
  + exact: rectifiable_union.
Qed.

(** Source for [dgpr_prefix_closed]: blueprint lem:inner, proof: a
    finite union of closed sets is closed; supporting lemma. *)
Lemma dgpr_prefix_closed (G : nat -> set X) :
  (forall i, closed (G i)) -> forall j, closed (set_sequence_prefix G j).
Proof.
move=> hG; elim=> [|j hj]; first by rewrite set_sequence_prefix_zero; exact: closed0.
by rewrite set_sequence_prefix_succ; exact: closedU.
Qed.

(** Source for [dgpr_inner_approximation_measure]: blueprint lem:inner,
    proof, for a measure μ over R^n with μ(R^n) < ∞ for which every Borel
    set is μ measurable and μ(A) = 0 whenever H^m(M ∩ A) = 0. The sets
    F_i are the closures of the m rectifiable sets whose union covers
    H^m almost all of M; Federer 2.1.3(5) gives j with μ(R^n ∖ F) < ε/2
    for F = F_0 ∪ ... ∪ F_(j-1), and 2.2.2 a closed set E ⊆ M ∩ F with
    μ((M ∩ F) ∖ E) < ε/2. Since μ(F ∖ M) = 0, μ(R^n ∖ E) < ε. *)
Theorem dgpr_inner_approximation_measure (M : set X) (mu : set X -> \bar R) (eps : R) :
  is_measure mu -> (forall B, borel_set B -> measure_measurable mu B) -> (mu setT < +oo)%E ->
  (forall A, H (M `&` A) = 0%E -> mu A = 0%E) ->
  borel_set M -> is_countably_measure_m_rectifiable H m M -> 0 < eps ->
  exists E, [/\ E `<=` M, compact E, is_m_rectifiable m E & (mu (~` E) < eps%:E)%E].
Proof.
move=> hm hB hfin hac hM [_ [S [[C [hCc [hCr hS]]] hMS]]] heps.
rewrite /measure_almost_included hS in hMS.
have hHm := hausdorff_measure_is_measure X m.
have he2 : 0 < eps / 2 by rewrite divr_gt0.
case: (pselect (exists F, C F)) => [hne|hempty]; last first.
  have hall A : mu A = 0%E.
    apply: hac; apply/eqP; rewrite eq_le measure_nonnegative // andbT -hMS.
    apply: measure_mono => // x [hx _]; split=> // -[F hF _]; apply: hempty; by exists F.
  exists set0; split=> //; [exact: compact0|exact: rectifiable_empty|].
  by rewrite hall lte_fin.
have [G hG] := countable_nonempty_family_enumeration (@closure X) hCc hne.
have hGi i : compact (G i) /\ is_m_rectifiable m (G i).
  have : (closure @` C) (G i) by rewrite -hG; exists i.
  by case=> F hF <-; exact: dgpr_rectifiable_closure_compact (hCr F hF).
have hGclosed i : closed (G i) := compact_closed (@metric_hausdorff R X) (hGi i).1.
have hcover : \bigcup_(F in C) F `<=` \bigcup_i G i.
  move=> x [F hF hx]; have : (closure @` C) (closure F) by exists F.
  rewrite -hG => -[i _ hi]; exists i => //; rewrite hi; exact: subset_closure.
have hnull : mu (setT `\` \bigcup_i G i) = 0%E.
  apply: hac; apply/eqP; rewrite eq_le measure_nonnegative // andbT -hMS.
  apply: measure_mono => // x [hx [_ hxG]]; split=> // hxC; apply: hxG; exact: hcover.
have hGm i : measure_measurable mu (G i) := hB _ (closed_borel_set (hGclosed i)).
have hlim := measure_prefix_complement_limit hm setT hfin hGm.
rewrite hnull in hlim.
have hlt : (0%E < (eps / 2)%:E)%E by rewrite lte_fin.
have [j hj] := hlim.2.2 _ hlt.
pose F := set_sequence_prefix G j.
have [hFc hFr] := dgpr_prefix_compact_rectifiable hGi j.
have hFclosed : closed F := @dgpr_prefix_closed G hGclosed j.
have hFj : (mu (setT `\` F) < (eps / 2)%:E)%E := hj j (leqnn j).
have hMF : borel_set (M `\` ~` F).
  apply: borel_set_difference => //; apply: open_borel_set; by rewrite openC.
have hMFfin : (mu (M `\` ~` F) < +oo)%E.
  apply: le_lt_trans hfin; exact: measure_mono.
have hopen U : open U -> measure_measurable mu U.
  move=> hU; exact: hB _ (open_borel_set hU).
have [E [hEc [hEMF hEerr]]] := metric_borel_closed_approximation hm hopen hMF hMFfin he2.
have hEF : E `<=` F by move=> x hx; have [_ hxF] := hEMF x hx; apply: contrapT.
exists E; split.
- by move=> x hx; have [] := hEMF x hx.
- exact: subclosed_compact hEc hFc hEF.
- exact: rectifiable_subset hEF hFr.
- have hFM : mu (F `\` M) = 0%E.
    apply: hac; rewrite (_ : M `&` (F `\` M) = set0) ?measure_empty //.
    by apply/seteqP; split=> x // [hx [_ hnx]].
  have hsub : ~` E `<=` (setT `\` F) `|` ((M `\` ~` F) `\` E `|` (F `\` M)).
    move=> x hxE; case: (pselect (F x)) => hxF; last by left.
    right; case: (pselect (M x)) => hxM; last by right.
    by left; split=> //; split=> // /(_ hxF).
  have h1 : (mu (~` E) <= mu (setT `\` F) + mu ((M `\` ~` F) `\` E `|` (F `\` M)))%E :=
    measure_binary_cover hm hsub.
  have h2 : (mu ((M `\` ~` F) `\` E `|` (F `\` M)) <= mu ((M `\` ~` F) `\` E) + mu (F `\` M))%E :=
    measure_binary_cover hm (fun x hx => hx).
  rewrite hFM adde0 in h2.
  apply: (le_lt_trans h1).
  apply: (le_lt_trans (leeD2l _ h2)).
  rewrite [eps]splitr EFinD; exact: lteD.
Qed.

(** Source for [dgpr_inner_approximation]: blueprint lem:inner, the
    statement, with μ = (H^m ⌞ M) ⌞ θ written as
    [measure_with_density (measure_restrict H M) (real_total_integrand theta)]
    (Federer 2.4.10). The measure μ is finite because θ is H^m ⌞ M
    summable, every Borel set is μ measurable because H^m is Borel
    regular (2.10.2(1)), and μ(A) = 0 whenever H^m(M ∩ A) = 0; hence
    [dgpr_inner_approximation_measure] applies. The hypothesis
    H^m(M) < ∞ of the blueprint is not used. *)
Theorem dgpr_inner_approximation (M : set X) (theta : X -> R) (eps : R) :
  borel_set M -> is_countably_measure_m_rectifiable H m M -> (H M < +oo)%E ->
  (forall x, M x -> 0 <= theta x) -> summable_real_functions (measure_restrict H M) theta ->
  0 < eps ->
  exists E, [/\ E `<=` M, compact E, is_m_rectifiable m E &
    (measure_with_density (measure_restrict H M) (real_total_integrand theta) (~` E) < eps%:E)%E].
Proof.
move=> hM hrect _ htheta [a ha] heps.
pose HM := measure_restrict H M.
pose h := real_total_integrand theta.
pose mu := measure_with_density HM h.
have hHm := hausdorff_measure_is_measure X m.
have hHMm : is_measure HM := measure_restrict_is_measure hHm M.
have hlaws : is_measure_density HM h mu := measure_with_density_laws HM h.
have hpos : measure_almost_everywhere HM (partial_extended_nonnegative_locus h).
  rewrite /measure_almost_everywhere /HM /measure_restrict.
  rewrite (_ : M `&` ~` _ = set0) ?measure_empty //.
  apply/seteqP; split=> // x [hxM hx]; apply: hx; exists (theta x)%:E; split.
    by exists (theta x).
  by rewrite lee_fin; exact: htheta.
have hmu : is_measure mu := measure_with_density_is_measure hHMm hpos.
have hBH B : borel_set B -> measure_measurable H B.
  move=> hBb; exact: (borel_regular_borel_measurable hHm (hausdorff_measure_borel_regular X m) hBb).
have hB B : borel_set B -> measure_measurable mu B.
  move=> hBb; apply: measure_with_density_measurable => //.
  exact: measure_restrict_measurable (hBH B hBb).
have hfin : (mu setT < +oo)%E.
  have hT : measure_measurable HM setT.
    apply: measure_restrict_measurable; apply: hBH; apply: closed_borel_set; exact: closedT.
  have hs := measurable_density_subset_integral hHMm hlaws hpos ha.1 hT.
  have hext : partial_function_zero_extension (0 : extended_real_line R) setT h = h.
    apply: partial_function_graph_extensionality => x z.
    exact: partial_zero_extension_whole_graph.
  rewrite /is_measure_subset_integral hext in hs.
  by rewrite (measure_integral_unique hs ha) ltry.
apply: (dgpr_inner_approximation_measure hmu hB hfin _ hM hrect heps).
move=> A hA; apply: (measure_density_null_set hHMm hlaws).
by rewrite /HM /measure_restrict.
Qed.

End InnerApproximation.
