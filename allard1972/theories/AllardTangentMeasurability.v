(** Allard (1972), 3.5, p. 431, blueprint al:3.5:lem (first assertion) and
    al:2.8(4)(a)(b): measurability of the approximate tangent plane map
    [x ↦ Tan^k(H^k⌞E, x)] of a locally rectifiable set E ⊆ R^n, as a partial
    map into G(n, k). For an (H^k, k) rectifiable set W the map agrees
    H^k almost everywhere on W with [x ↦ P(ξ(x))], where ξ is the measurable
    orientation of Federer 3.2.25, p. 261, and P(ξ) is the orthogonal
    projection onto the subspace associated with ξ (AllardSimpleProjection.v);
    for E the map is patched from the pieces E ∩ B(0, j) by locality.
    The file also supplies the measure theoretic facts on H^k⌞E used to
    construct v(E): a Borel sandwich of E, the Borel regularity of H^k⌞E and
    a Borel version of the tangent plane map (Federer 2.3.6, p. 77). Here
    M = U = R^n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology normedtype lra cardinality.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerNorm InnerMetric NormMetric HilbertFormCompactness LinearBasis FiniteCoordinates Hom HomInner
  GrassmannSubspaces ExteriorGrading ExteriorNorm InnerExteriorPositivity AssociatedSubspace
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic MeasureRestriction RadonMeasureUP BorelRegularMeasureUP
  TopologicalBorel BorelFunctionUP BorelFunctionBasic HausdorffMeasure HausdorffClosedCoverAgreement
  MetricClosedBalls EuclideanClosedBallCompact MeasurableFunctionUP MeasurablePostcomposition
  MeasurableAlmostModification MeasureApproximateTangentUP RectifiableTangentPlaneUP RectifiableSetUP
  RectifiableOrientationUP RectifiableOrientation MeasureFiniteClosure MeasureCountableClosure
  MeasurableRestrictionTransfer BorelRegularSandwich BorelRegularRestriction MeasureNullModification
  CountablyMeasurableUP LusinBorelVersion.
From Allard Require Import AllardOrthogonalProjectors AllardGrassmann AllardGrassmannSubspaces
  AllardVarifolds AllardRectifiableVarifolds AllardSimpleProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section TangentMeasurability.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation RnM := (inner_metric_space hBn).
Local Notation NX := (inner_norm_real_norm hBn).
Local Notation GA := (projection_grassmann R n k).
Local Notation GB := (grassmann_bundle R n k).
Local Notation HK := (@hausdorff_measure R RnM k).
Local Notation h2 := (euclidean_two_nonzero R).
Local Notation L := (inner_metric_space (@exterior_inner_productP R h2 Rn (@euclidean_inner_product R n) hBn k)).
Local Notation HEn := (inner_metric_space (hom_inner_productP hBn hBn hbn)).
Local Notation tau mu := (@approximate_tangent_plane R n k mu).
Local Notation locrect E := (@is_locally_rectifiable_set R n k E).

(** Source for [restrict_measurable_of_intersection]: Federer 2.1.2, p. 54:
    if S ∩ A is μ measurable, then A is μ⌞S measurable. Supporting lemma. *)
Lemma restrict_measurable_of_intersection (mu : set RnM -> \bar R) (S A : set RnM) :
  is_measure mu -> measure_measurable mu (S `&` A) -> measure_measurable (measure_restrict mu S) A.
Proof.
move=> hm hSA T; rewrite /measure_restrict.
have e1 : S `&` (T `&` A) = (S `&` T) `&` (S `&` A).
  by apply/seteqP; split=> x; [move=> [hs [ht ha]]|move=> [[hs ht] [_ ha]]].
have e2 : S `&` (T `\` A) = (S `&` T) `\` (S `&` A).
  apply/seteqP; split=> x; [move=> [hs [ht hna]]; split=> //; move=> [_ ha]; exact: hna ha|].
  by move=> [[hs ht] hn]; split=> //; split=> //; move=> ha; apply: hn.
by rewrite e1 e2; exact: hSA.
Qed.

(** Source for [orientation_plane_graph]: Allard 3.5, p. 431, with Federer
    3.2.25, p. 261: the graph of [x ↦ P(ξ(x))], the orthogonal projection onto
    the subspace associated with the unit simple k-vector ξ(x) of a
    measurable orientation. Definition. *)
Definition orientation_plane_graph (T : partial_function Rn (exterior_power Rn k)) (x : RnM) (S : GA) : Prop :=
  exists xi, partial_function_graph T x xi /\ (set_val S : Hom Rn Rn) = simple_projection_hom xi.

(** Source for [orientation_plane_functional]: the graph
    [orientation_plane_graph] is single valued. Supporting lemma. *)
Lemma orientation_plane_functional (T : partial_function Rn (exterior_power Rn k)) x (S S' : GA) :
  orientation_plane_graph T x S -> orientation_plane_graph T x S' -> S = S'.
Proof.
move=> [xi [hxi hS]] [xi' [hxi' hS']].
have e := partial_function_single_valued hxi hxi'.
apply: val_inj; have -> : val S = (set_val S : Hom Rn Rn) by [].
have -> : val S' = (set_val S' : Hom Rn Rn) by [].
by rewrite hS hS' e.
Qed.

(** Source for [orientation_plane]: Allard 3.5, p. 431: the partial map
    [x ↦ P(ξ(x))] of R^n into G(n, k) defined by a measurable orientation ξ
    (Federer 3.2.25, p. 261). Definition. *)
Definition orientation_plane (T : partial_function Rn (exterior_power Rn k)) : partial_function RnM GA :=
  @Build_partial_function RnM GA (orientation_plane_graph T) (@orientation_plane_functional T).

(** Source for [orientation_plane_measurable]: Federer 2.3.2(4), p. 73, and
    3.2.25, p. 261: if ξ is a measurable orientation of W, then [x ↦ P(ξ(x))]
    is H^k⌞W measurable as a map into G(n, k); blueprint al:2.8(4)(a)(b).
    Supporting lemma. *)
Lemma orientation_plane_measurable (W : set Rn) (T : partial_function Rn (exterior_power Rn k)) :
  is_rectifiable_measurable_orientation W T ->
  is_measure_measurable_function (measure_restrict HK W) (orientation_plane T).
Proof.
move=> hT.
have hm : is_measure (measure_restrict HK W).
  apply: measure_restrict_is_measure; have h := @hausdorff_measure_is_measure R RnM k; exact h.
have hTm := rectifiable_orientation_measurable hT.
have hdom : partial_function_domain T `<=` partial_function_domain (orientation_plane T).
  move=> x [xi hxi].
  have [hs h1] := rectifiable_orientation_unit_simple hT hxi.
  have hP := simple_projection_hom_projector hs h1.
  by exists (projection_grassmann_of hP); exists xi.
constructor.
- apply: (measure_null_subset hm _ (measurable_function_domain hTm)).
  by move=> x hx hT'; apply: hx; exact: hdom.
- move=> U hU.
  have [O hO hOU] := hU.
  have hP : is_borel_function (fun xi : L => (simple_projection_hom xi : HEn)).
    exact: continuous_borel_function (@simple_projection_hom_continuous R n k).
  have hc := @measurable_function_borel_postcomposition R [the choiceType of RnM] L HEn _ hm T _ hTm hP.
  have := measurable_function_open_preimage hc hO.
  have -> // : partial_function_preimage (partial_function_postcompose T
      (fun xi : L => (simple_projection_hom xi : HEn))) O =
    partial_function_preimage (orientation_plane T) U.
  apply/seteqP; split=> x.
  + move=> [y [[xi [hxi <-]] hOy]].
    have [hs h1] := rectifiable_orientation_unit_simple hT hxi.
    have hP' := simple_projection_hom_projector hs h1.
    exists (projection_grassmann_of hP'); split; first by exists xi.
    by rewrite -hOU.
  + move=> [S [[xi [hxi hS]] hUS]].
    exists (simple_projection_hom xi); split; first by exists xi.
    rewrite -hOU in hUS; by rewrite /= -hS.
Qed.

(** Source for [rectifiable_tangent_plane_measurable]: blueprint
    al:2.8(4)(a)(b), from Federer 3.2.19, p. 256, 3.2.25, p. 261, and 2.3.2,
    p. 73: for an (H^k, k) rectifiable set W, the map [x ↦ Tan^k(H^k⌞W, x)]
    into G(n, k) is H^k⌞W measurable; it agrees H^k almost everywhere on W
    with [x ↦ P(ξ(x))]. Supporting lemma. *)
Lemma rectifiable_tangent_plane_measurable (W : set RnM) :
  is_measure_m_rectifiable HK k W ->
  is_measure_measurable_function (measure_restrict HK W)
    (tau (measure_restrict HK W)).
Proof.
move=> hW.
have hHm : is_measure HK by have h := @hausdorff_measure_is_measure R RnM k; exact h.
have hm : is_measure (measure_restrict HK W) := measure_restrict_is_measure hHm W.
have [T [hT _]] := @federer_3_2_25 R k n W hW.
apply: (@measurable_function_almost_equal R [the choiceType of RnM] GA _ hm (orientation_plane T)).
  exact: orientation_plane_measurable hT.
have ht := rectifiable_orientation_tangent hT.
rewrite /measure_almost_equal /measure_almost_everywhere /measure_restrict.
apply: (measure_null_subset hHm _ ht)=> x [hWx hna]; split=> // [[xi [hxi [hcone _]]]].
apply: hna.
have [hs h1] := rectifiable_orientation_unit_simple hT hxi.
have hP := simple_projection_hom_projector hs h1.
exists (projection_grassmann_of hP); split; first by exists xi.
apply/approximate_tangent_planeE; rewrite hcone.
apply/seteqP; split=> v.
- by move=> hv; apply/(simple_projection_hom_image hs h1).
- by move=> hv; apply/(simple_projection_hom_image hs h1).
Qed.

(** Source for [set_tangent_plane_measurable]: Allard 3.5, p. 431; blueprint
    al:3.5:lem, first assertion: if E is H^k measurable and E ∩ K is (H^k,
    k) rectifiable for compact K, then g_E(x) = Tan^k(H^k⌞E, x) defines an
    H^k⌞E measurable map into G(n, k). The proof uses the locality of Tan^k
    on the open balls U(0, j). Direct formalisation. *)
Lemma set_tangent_plane_measurable (E : set RnM) :
  @is_locally_rectifiable_set R n k E ->
  is_measure_measurable_function (measure_restrict HK E) (tau (measure_restrict HK E)).
Proof.
move=> hE; have [hEm hEr] := hE.
have hHm : is_measure HK by have h := @hausdorff_measure_is_measure R RnM k; exact h.
have hHr : is_borel_regular_measure HK by have h := @hausdorff_measure_borel_regular R RnM k; exact h.
have hm := measure_restrict_is_measure hHm E.
pose B (j : nat) := metric_closed_ball (0 : RnM) j%:R.
pose U (j : nat) := [set x : RnM | mdist (0 : RnM) x < j%:R].
have hBc j : compact (B j) := @euclidean_closed_metric_ball_compact R n (0 : RnM) j%:R.
have hBm j : measure_measurable HK (B j).
  exact: (@borel_regular_borel_measurable R RnM HK hHm hHr (B j)
    (closed_borel_set (@metric_closed_ball_closed R RnM (0 : RnM) j%:R))).
have hUm j : measure_measurable HK (U j).
  exact: (@borel_regular_borel_measurable R RnM HK hHm hHr (U j)
    (open_borel_set (@metric_open_ball_open R RnM (0 : RnM) j%:R))).
have hEBm j : measure_measurable HK (E `&` B j) := measure_measurable_intersection hHm hEm (hBm j).
have hnorm (x : RnM) : mdist (0 : RnM) x = inner_norm hBn x.
  by rewrite inner_metric_distanceE sub0r inner_normN.
have hloc j (x : RnM) S : U j x ->
    (partial_function_graph (tau (measure_restrict HK (E `&` B j))) x S <->
     partial_function_graph (tau (measure_restrict HK E)) x S).
  move=> hx; rewrite /U /= hnorm in hx.
  rewrite !approximate_tangent_planeE.
  by rewrite (@approximate_tangent_cone_closed_ball_local R n k E _ x hx).
constructor.
- have h := @set_approximate_tangent_plane_ae R n k E hE.
  rewrite /measure_almost_everywhere /measure_restrict.
  apply: (measure_null_subset hHm _ h)=> x [hEx hnd]; split=> //.
- move=> O hO.
  apply: restrict_measurable_of_intersection=> //.
  have -> : E `&` partial_function_preimage (tau (measure_restrict HK E)) O =
      \bigcup_j (U j `&` (partial_function_preimage (tau (measure_restrict HK (E `&` B j))) O `&` (E `&` B j))).
    apply/seteqP; split=> x.
    + move=> [hEx [S [hS hOS]]].
      have hx : inner_norm hBn x < (Num.bound (inner_norm hBn x))%:R.
        exact: (archi_boundP (inner_norm_nonnegative hBn x)).
      have hU : U (Num.bound (inner_norm hBn x)) x by rewrite /U /= hnorm.
      exists (Num.bound (inner_norm hBn x)) => //; split=> //; split.
      * by exists S; split=> //; apply/(hloc _ _ _ hU).
      * split=> //; rewrite /B /metric_closed_ball /= hnorm; exact: ltW.
    + move=> [j _ [hU [[S [hS hOS]] [hEx _]]]]; split=> //.
      by exists S; split=> //; apply/(hloc _ _ _ hU).
  apply: measure_measurable_sequence_union=> // j.
  apply: measure_measurable_intersection=> //.
  apply: measurable_restriction_intersection_transfer=> //.
  have hj := rectifiable_tangent_plane_measurable (hEr _ (hBc j)).
  exact: measurable_function_open_preimage hj _ hO.
Qed.

(** Source for [borel_setU]: Federer 2.2.1, p. 59: the union of two Borel
    sets is a Borel set. Supporting lemma. *)
Lemma borel_setU (T : topologicalType) (A B : set T) : borel_set A -> borel_set B -> borel_set (A `|` B).
Proof.
move=> hA hB.
have -> : A `|` B = ~` (~` A `\` B).
  apply/seteqP; split=> x.
  - by move=> [ha|hb] [hna hnb]; [exact: hna|exact: hnb].
  - move=> h; case: (pselect (A x))=> ha; first by left.
    case: (pselect (B x))=> hb; first by right.
    by exfalso; apply: h; split.
exact: borel_set_complement (borel_set_difference (borel_set_complement hA) hB).
Qed.

(** Source for [hausdorff_measure_laws]: Federer 2.10.1, p. 171: H^k is a
    Borel regular measure over R^n. Supporting lemma. *)
Lemma hausdorff_measure_laws : is_measure HK /\ is_borel_regular_measure HK.
Proof.
split; first by have h := @hausdorff_measure_is_measure R RnM k; exact h.
by have h := @hausdorff_measure_borel_regular R RnM k; exact h.
Qed.

Local Notation ball j := (metric_closed_ball (0 : RnM) (j%:R)).

(** Source for [closed_ball_measurable]: Federer 2.10.1, p. 171, and 2.2.3,
    p. 61: the closed balls B(0, j) are H^k measurable. Supporting lemma. *)
Lemma closed_ball_measurable (j : nat) : measure_measurable HK (ball j).
Proof.
have [hHm hHr] := hausdorff_measure_laws.
exact: (@borel_regular_borel_measurable R RnM HK hHm hHr (ball j)
  (closed_borel_set (@metric_closed_ball_closed R RnM (0 : RnM) j%:R))).
Qed.

(** Source for [closed_ball_cover]: R^n is the union of the closed balls
    B(0, j), j = 0, 1, 2, .... Supporting lemma. *)
Lemma closed_ball_cover (x : RnM) : exists j : nat, ball j x.
Proof.
exists (Num.bound (inner_norm hBn x)).
rewrite /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN.
exact: ltW (archi_boundP (inner_norm_nonnegative hBn x)).
Qed.

(** Source for [locally_rectifiable_ball_finite]: Allard 3.5, p. 431, and
    Federer 3.2.14, p. 251: H^k(E ∩ B(0, j)) < ∞ for E as in 3.5, since E ∩
    B(0, j) is (H^k, k) rectifiable. Supporting lemma. *)
Lemma locally_rectifiable_ball_finite E (j : nat) : locrect E -> (HK (E `&` ball j) < +oo)%E.
Proof.
move=> [_ hEr].
exact: (hEr _ (@euclidean_closed_metric_ball_compact R n (0 : RnM) j%:R)).2.
Qed.

(** Source for [locally_rectifiable_borel_sandwich]: Federer 2.2.3, p. 61,
    and 2.1.4, p. 55: for E as in Allard 3.5 there are Borel sets D ⊆ E ⊆ B
    with H^k(B ∖ D) = 0. Supporting lemma. *)
Lemma locally_rectifiable_borel_sandwich E : locrect E ->
  exists D B : set RnM, [/\ borel_set D, borel_set B, D `<=` E, E `<=` B & HK (B `\` D) = 0].
Proof.
move=> hE; have [hEm _] := hE.
have [hHm hHr] := hausdorff_measure_laws.
have hj (j : nat) : exists p : set RnM * set RnM, [/\ borel_set p.1, borel_set p.2,
    p.1 `<=` E `&` ball j, E `&` ball j `<=` p.2 & HK (p.2 `\` p.1) = 0].
  have hm := measure_measurable_intersection hHm hEm (closed_ball_measurable j).
  have [D [B [hD [hB [hDA [hAB h0]]]]]] :=
    @borel_regular_finite_sandwich R RnM HK hHm hHr _ hm (locally_rectifiable_ball_finite j hE).
  by exists (D, B).
have [p hp] := choice hj.
exists (\bigcup_j (p j).1), (\bigcup_j (p j).2); split.
- apply: borel_set_countable_union; first exact: countableP.
  by move=> j _; have [] := hp j.
- apply: borel_set_countable_union; first exact: countableP.
  by move=> j _; have [] := hp j.
- by move=> x [j _ hx]; have [_ _ h _ _] := hp j; have [] := h x hx.
- move=> x hx; have [j hj'] := closed_ball_cover x.
  by exists j => //; have [_ _ _ h _] := hp j; apply: h.
- have h0 : HK (\bigcup_(j in [set: nat]) ((p j).2 `\` (p j).1)) = 0.
    apply: (measure_null_countable_union hHm (countableP [set: nat])).
    by move=> j _; have [_ _ _ _ h] := hp j.
  apply: (measure_null_subset hHm _ h0).
  move=> x [[j _ hx] hn]; exists j; first done.
  split; first exact: hx.
  by move=> hx'; apply: hn; exists j.
Qed.

(** Source for [locally_rectifiable_restrict_borel_regular]: Federer 2.2.3,
    p. 61: H^k⌞E is Borel regular for E as in Allard 3.5, because H^k⌞E =
    H^k⌞B for a Borel set B. Supporting lemma. *)
Lemma locally_rectifiable_restrict_borel_regular E : locrect E ->
  is_borel_regular_measure (measure_restrict HK E).
Proof.
move=> hE; have [hHm hHr] := hausdorff_measure_laws.
have [D [B [hD hB hDE hEB h0]]] := locally_rectifiable_borel_sandwich hE.
have -> : measure_restrict HK E = measure_restrict HK B.
  apply: funext=> Z; rewrite /measure_restrict.
  apply: (measure_null_modification_value hHm h0)=> x hx; split.
  - by move=> [hEx hZ]; split=> //; apply: hEB.
  - move=> [hBx hZ]; split=> //; apply: hDE.
    by case: (pselect (D x))=> // hnD; exfalso; apply: hx; split.
exact: (@borel_regular_restrict_borel R RnM HK hHm hHr B hB).
Qed.

(** Source for [locally_rectifiable_countably_measurable]: Federer 2.3.6, p.
    77, hypothesis: R^n is the union of countably many H^k⌞E measurable sets
    of finite measure, for E as in Allard 3.5. Supporting lemma. *)
Lemma locally_rectifiable_countably_measurable E : locrect E ->
  measure_countably_measurable (measure_restrict HK E) setT.
Proof.
move=> hE; have [hHm _] := hausdorff_measure_laws.
exists ((fun j : nat => ball j) @` setT); split; [|split].
- exact: (card_le_trans (card_image_le _ _) (countableP [set: nat])).
- apply/seteqP; split=> // x _; have [j hj] := closed_ball_cover x.
  by exists (ball j) => //; exists j.
- move=> _ [j _ <-]; split.
  + exact: measure_restrict_measurable (closed_ball_measurable j).
  + exact: locally_rectifiable_ball_finite.
Qed.

(** Source for [set_tangent_borel_version]: Federer 2.3.6, p. 77, first
    corollary: g_E agrees H^k⌞E almost everywhere with a Borel map of R^n
    into G(n, k); blueprint rem:3.5. Supporting lemma. *)
Lemma set_tangent_borel_version E (S0 : GA) : locrect E ->
  exists t : RnM -> GA, is_borel_function t /\
    measure_almost_equal (measure_restrict HK E) (tau (measure_restrict HK E)) (partial_function_total t).
Proof.
move=> hE; have [hHm hHr] := hausdorff_measure_laws.
have [D [hDc hDd]] := @projection_grassmann_separable R n k.
exact: (@lusin_borel_version_metric R RnM GA (measure_restrict HK E) (measure_restrict_is_measure hHm E)
  (locally_rectifiable_restrict_borel_regular hE) D (tau (measure_restrict HK E)) S0 hDc hDd
  (set_tangent_plane_measurable hE) (locally_rectifiable_countably_measurable hE)).
Qed.


End TangentMeasurability.
