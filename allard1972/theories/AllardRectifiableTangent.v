(** Allard (1972), 3.5(1)(b), p. 432, specialised to M = U = R^n; blueprint
    proof of al:3.5(1) and new:density_tangent(b)(c). Suppose c_i > 0 and
    the sets E_i satisfy the hypotheses of Allard 3.5
    ([is_locally_rectifiable_set]). Let μ = Σ_i c_i H^k⌞E_i
    ([rectifiable_sum_measure]), and assume that μ is a Radon measure.
    This file proves that Tan^k(μ, x) = Tan^k(H^k⌞E_i, x) for H^k almost
    all x ∈ E_i ([rectifiable_sum_tangent_equal]), that Tan^k(μ, x) ∈
    G(n, k) for μ almost all x ([rectifiable_sum_tangent_plane_ae]), and
    that [x ↦ Tan^k(μ, x)] is μ measurable
    ([rectifiable_sum_tangent_measurable]). The first assertion is
    obtained from the density strata of Federer 3.3.18, p. 301, applied to
    μ⌞B(0, j). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology normedtype lra cardinality.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric NormMetric
  HilbertFormCompactness LinearBasis FiniteCoordinates Hom GrassmannSubspaces ExtendedRealOrderTopology
  PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureRestriction
  RadonMeasureUP RegularMeasureUP BorelRegularMeasureUP TopologicalBorel HausdorffMeasure
  HausdorffClosedCoverAgreement MetricClosedBalls EuclideanClosedBallCompact MetricDensities
  MetricDensityZeroPowerMass MeasureApproximateTangentUP RectifiableTangentPlaneUP
  RestrictedApproximateTangent NonnegativeSum NonnegativeSumAdd NonnegativeSumSupport
  MeasureFiniteClosure MeasurableFunctionUP MeasurableAlmostModification MeasurableRestrictionTransfer
  RadonBorelRegularity BorelRegularRestriction StructureRectifiableDensityStrata
  StructureDensityStratumTangents FiniteUpperDensityHausdorffBound HausdorffUpperMetricDensity
  HausdorffRestrictedDensity SphericalMetricDensityTheorems FiniteMeasurableTangentRestriction.
From Allard Require Import AllardGrassmann AllardVarifolds AllardRectifiableVarifolds
  AllardTangentMeasurability AllardSetVarifold AllardRectifiableSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableTangent.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation RnM := (inner_metric_space hBn).
Local Notation NX := (inner_norm_real_norm hBn).
Local Notation RNM := (real_norm_metric_space NX).
Local Notation GA := (projection_grassmann R n k).
Local Notation HK := (@hausdorff_measure R RnM k).
Local Notation tau mu := (@approximate_tangent_plane R n k mu).
Local Notation locrect E := (@is_locally_rectifiable_set R n k E).
Local Notation cone mu x := (measure_approximate_tangent_cone NX mu k x).
Local Notation ball j := (metric_closed_ball (0 : RnM) (j%:R)).

Variable c : nat -> R.
Variable E : nat -> set RnM.
Hypothesis hc : forall i, 0 < c i.
Hypothesis hE : forall i, locrect (E i).
Local Notation mu := (@rectifiable_sum_measure R n k c E).
Hypothesis hm : is_measure mu.
Hypothesis hr : is_radon_measure mu.

(** Source for [rectifiable_sum_lower]: Allard 3.5, p. 431: each summand
    of μ = Σ_l c_l H^k⌞E_l is dominated by μ, that is
    c_i H^k(E_i ∩ A) ≤ μ(A) for every A ⊆ R^n. Supporting lemma. *)
Lemma rectifiable_sum_lower i A : ((c i)%:E * HK (E i `&` A) <= mu A)%E.
Proof.
exact: (@nonnegative_sum_term R nat [set: nat] (fun l => ((c l)%:E * HK (E l `&` A))%E) i I).
Qed.

(** Source for [extended_small_multiple_nonpositive]: if 0 ≤ M < ∞ and
    x ≤ s M for every s > 0, then x ≤ 0. This is the limit s → 0+ used
    with Federer 2.10.19(1),(3), p. 181. Supporting lemma. *)
Lemma extended_small_multiple_nonpositive (x M : \bar R) :
  (0 <= M)%E -> (M < +oo)%E -> (forall s : R, 0 < s -> (x <= s%:E * M)%E) -> (x <= 0)%E.
Proof.
case: M => [m| |] hM0 hMf hx //.
rewrite lee_fin in hM0.
case: x hx => [r| |] hx; last by rewrite leNye.
- rewrite lee_fin leNgt; apply/negP=> hr0.
  have hm1 : 0 < m + 1 by lra.
  pose s := r / (m + 1).
  have hs : 0 < s by rewrite /s divr_gt0.
  have := hx s hs; rewrite -EFinM lee_fin => h.
  have e : s * (m + 1) = r by rewrite /s divfK // gt_eqF.
  move: e; rewrite mulrDr mulr1 => e.
  clearbody s; clear hx hMf; lra.
- by have := hx 1 ltr01; rewrite mul1e leye_eq.
Qed.

(** Source for [rectifiable_sum_ball_borel]: Federer 2.10.1, p. 171, and
    2.2.1, p. 60: the closed ball B(0, j) is closed, hence a Borel set.
    Supporting lemma. *)
Lemma rectifiable_sum_ball_borel j : borel_set (ball j).
Proof. exact: (closed_borel_set (@metric_closed_ball_closed R RnM (0 : RnM) j%:R)). Qed.

(** Source for [rectifiable_sum_ball_measure]: Federer 2.1.2, p. 54: the
    restriction μ⌞B(0, j) is a measure. Supporting lemma. *)
Lemma rectifiable_sum_ball_measure j : is_measure (measure_restrict mu (ball j)).
Proof. exact: (measure_restrict_is_measure hm (ball j)). Qed.

(** Source for [rectifiable_sum_ball_borel_regular]: Federer 2.2.5,
    p. 62, and 2.2.3, p. 62: the Radon measure μ is Borel regular, and so
    is its restriction μ⌞B(0, j) to a Borel set. Supporting lemma. *)
Lemma rectifiable_sum_ball_borel_regular j : is_borel_regular_measure (measure_restrict mu (ball j)).
Proof.
exact: (borel_regular_restrict_borel hm (radon_borel_regular hm hr) (rectifiable_sum_ball_borel j)).
Qed.

(** Source for [rectifiable_sum_ball_finite]: Federer 2.2.5, p. 62:
    (μ⌞B(0, j))(R^n) = μ(B(0, j)) < ∞, because B(0, j) is compact and μ
    is a Radon measure. Supporting lemma. *)
Lemma rectifiable_sum_ball_finite j : (measure_restrict mu (ball j) setT < +oo)%E.
Proof.
rewrite /measure_restrict setIT.
exact: (radon_compact_finite hr (@euclidean_closed_metric_ball_compact R n (0 : RnM) j%:R)).
Qed.

(** Source for [rectifiable_sum_ball_infinite_density_null]: Federer
    2.10.19(3), p. 181, in the form of Federer 3.3.15, p. 299: the set of
    points at which Θ^{*k}(μ⌞B(0, j), x) = ∞ is H^k null, since
    H^k(A) ≤ s (μ⌞B(0, j))(A) for every s > 0 on that set A. Supporting
    lemma. *)
Lemma rectifiable_sum_ball_infinite_density_null j :
  HK [set a | (+oo <= upper_metric_density k (measure_restrict mu (ball j)) a)%E] = 0.
Proof.
set B := [set a | _].
have hHm := @hausdorff_measure_is_measure R RnM k.
have hpsi := rectifiable_sum_ball_measure j.
apply/eqP; rewrite eq_le (measure_nonnegative hHm) andbT.
apply: (@extended_small_multiple_nonpositive _ (measure_restrict mu (ball j) B)).
- exact: (measure_nonnegative hpsi).
- exact: (le_lt_trans (measure_mono hpsi (subsetT B)) (rectifiable_sum_ball_finite j)).
- move=> s hs.
  have hb x : B x -> (s^-1%:E < upper_metric_density k (measure_restrict mu (ball j)) x)%E.
    by move=> hx; apply: (lt_le_trans (ltry _) hx).
  have h := @finite_upper_density_hausdorff_bound R RnM k _ B s^-1 hpsi
    (rectifiable_sum_ball_borel_regular j) (rectifiable_sum_ball_finite j)
    (ltac:(by rewrite invr_gt0)) hb.
  by rewrite invrK in h.
Qed.

(** Source for [rectifiable_sum_ball_zero_density_null]: Federer
    2.10.19(1), p. 181: if Z ⊆ E_i ∩ B(0, j) and
    Θ^{*k}(μ⌞B(0, j), x) ≤ 0 for x ∈ Z, then μ(B(0, j) ∩ Z) ≤ 2^k s H^k(Z)
    for every s > 0, hence μ(B(0, j) ∩ Z) = 0; since
    c_i H^k(Z) ≤ μ(B(0, j) ∩ Z) and c_i > 0, the set Z is H^k null.
    Supporting lemma. *)
Lemma rectifiable_sum_ball_zero_density_null i j (Z : set RnM) : Z `<=` E i `&` ball j ->
  (forall a, Z a -> upper_metric_density k (measure_restrict mu (ball j)) a <= 0)%E -> HK Z = 0.
Proof.
move=> hZ hd.
have hHm := @hausdorff_measure_is_measure R RnM k.
have hpsi := rectifiable_sum_ball_measure j.
have hfin : (HK Z < +oo)%E.
  exact: (le_lt_trans (measure_mono hHm hZ) (@locally_rectifiable_ball_finite R n k (E i) j (hE i))).
have hpsiZ : (measure_restrict mu (ball j) Z <= 0)%E.
  apply: (@extended_small_multiple_nonpositive _ (HK Z) (measure_nonnegative hHm Z) hfin).
  move=> s hs.
  have hk : 0 < (2 : R) ^+ k by apply: exprn_gt0.
  have hb a : Z a -> (upper_metric_density k (measure_restrict mu (ball j)) a < (s / 2 ^+ k)%:E)%E.
    move=> ha; apply: (le_lt_trans (hd a ha)); rewrite lte_fin; exact: divr_gt0.
  have h := @federer_2_10_19_1 R RnM k _ Z (s / 2 ^+ k) hpsi
    (borel_regular_is_regular hpsi (rectifiable_sum_ball_borel_regular j)) hb.
  have e : (2 : R) ^+ k * (s / 2 ^+ k) = s by rewrite mulrC divfK // gt_eqF.
  by rewrite e in h.
have hlow := rectifiable_sum_lower i (ball j `&` Z).
have eZ : E i `&` (ball j `&` Z) = Z.
  apply/seteqP; split=> x; first by move=> [_ [_ hx]].
  by move=> hx; have [h1 h2] := hZ x hx.
rewrite eZ in hlow.
have h0 : ((c i)%:E * HK Z <= 0)%E := le_trans hlow hpsiZ.
rewrite pmule_rle0 in h0; last exact: hc.
by apply/eqP; rewrite eq_le h0 (measure_nonnegative hHm).
Qed.

(** Source for [rectifiable_sum_cone_ball_local]: Federer 3.2.16,
    p. 252, and 2.10.19, p. 181: Tan^k is local. If |x| < j, then
    Θ^k(μ⌞(R^n ∖ B(0, j)), x) = 0, because B(x, r) ⊆ B(0, j) for
    0 < r < j - |x|; hence Tan^k(μ, x) = Tan^k(μ⌞B(0, j), x). Supporting
    lemma. *)
Lemma rectifiable_sum_cone_ball_local j x : inner_norm hBn x < j%:R ->
  cone mu x = cone (measure_restrict mu (ball j)) x.
Proof.
move=> hx.
have hWhole : measure_restrict mu setT = mu by apply: funext=> A; rewrite /measure_restrict setTI.
have h := @restricted_approximate_tangent_equal R Rn (inner_norm hBn) NX k mu (ball j) setT x hm (subsetT _).
rewrite hWhole in h; symmetry; apply: h.
apply: (@small_power_mass_metric_zero_density R RNM k mu _ x hm).
move=> e he; exists (j%:R - inner_norm hBn x); split; first by rewrite subr_gt0.
move=> r /andP [hr0 hrj].
have -> : (setT `\` ball j) `&` metric_closed_ball (x : RNM) r = set0.
  apply/seteqP; split=> y // [[_ hn] hy]; apply: hn.
  have ht := metric_triangle (0 : RNM) (x : RNM) (y : RNM).
  move: hy; rewrite /metric_closed_ball /= => hy.
  rewrite !real_norm_metric_distanceE in ht hy.
  rewrite !sub0r !inner_normN in ht.
  rewrite /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN.
  lra.
rewrite (measure_empty hm) lee_fin.
by apply: mulr_ge0; [exact: ltW|apply: exprn_ge0; exact: ltW].
Qed.

(** Source for [stratum_omitted_density_hausdorff_null]: Federer
    2.10.19(4), p. 181, as used in Federer 3.3.18, p. 301: if ψ is a
    finite Borel regular measure, F is a Borel set and S is the density
    stratum F ∩ {a : b^{-1} < Θ^{*k}(ψ, a) < b}, then
    Θ^k(ψ⌞(R^n ∖ S), a) = 0 for H^k almost all a ∈ S. Supporting lemma. *)
Lemma stratum_omitted_density_hausdorff_null (psi : set RnM -> \bar R) (F : set RnM) (b : R) :
  is_measure psi -> is_borel_regular_measure psi -> (psi setT < +oo)%E -> borel_set F ->
  let S := structure_rectifiable_density_stratum k psi F b in
  HK (S `\` [set a | partial_function_graph (metric_density k (measure_restrict psi (~` S))) a 0%E]) = 0.
Proof.
move=> hPsi hRegular hFinite hF S.
have hS : borel_set S := @structure_rectifiable_density_stratum_borel R RnM k psi F b hPsi hF.
have hComplement : measure_measurable psi (~` S) :=
  borel_regular_borel_measurable hPsi hRegular (borel_set_complement hS).
have hComplementFinite : (psi (~` S) < +oo)%E :=
  le_lt_trans (measure_mono hPsi (subsetT (~` S))) hFinite.
have hOff := @federer_2_10_19_4 R RnM k psi (~` S) hPsi hRegular hComplement hComplementFinite.
rewrite setCK in hOff.
exact: (hausdorff_null_of_spherical_null hOff).
Qed.

(** Source for [rectifiable_sum_tangent_equal]: blueprint
    new:density_tangent(c), used in the proof of al:3.5(1); Allard
    3.5(1)(b), p. 432: Tan^k(μ, x) = Tan^k(H^k⌞E_i, x) for H^k almost all
    x ∈ E_i. Choose Borel sets D ⊆ E_i ⊆ B with H^k(B ∖ D) = 0, set
    ψ_j = μ⌞B(0, j) and let S_{j,l} be the density stratum of ψ_j over
    D ∩ B(0, j) with bound l + 1 (Federer 3.3.18, p. 301). On S_{j,l},
    Tan^k(ψ_j⌞S_{j,l}, x) = Tan^k(H^k⌞S_{j,l}, x) everywhere,
    Tan^k(ψ_j⌞S_{j,l}, x) = Tan^k(ψ_j, x) and
    Tan^k(H^k⌞S_{j,l}, x) = Tan^k(H^k⌞(E_i ∩ B(0, j)), x) almost
    everywhere (Federer 2.10.19(4), 3.2.32). The strata cover H^k almost
    all of D ∩ U(0, j), since 0 < Θ^{*k}(ψ_j, x) < ∞ for H^k almost all
    x ∈ E_i ∩ B(0, j) (Federer 2.10.19(1),(3)). *)
Theorem rectifiable_sum_tangent_equal i :
  measure_almost_everywhere_on HK (E i)
    [set x | cone mu x = cone (measure_restrict HK (E i)) x].
Proof.
have hHm := @hausdorff_measure_is_measure R RnM k.
have hHr := @hausdorff_measure_borel_regular R RnM k.
have [D [Bo [hD hBo hDE hEBo hnull]]] := @locally_rectifiable_borel_sandwich R n k (E i) (hE i).
pose psi j := measure_restrict mu (ball j).
pose F j := D `&` ball j.
pose S j l := structure_rectifiable_density_stratum k (psi j) (F j) l.+1%:R.
pose Good j l := [set a | partial_function_graph (metric_density k (measure_restrict (psi j) (~` S j l))) a 0%E].
pose T j l := [set a | cone (measure_restrict HK (S j l)) a = cone (measure_restrict HK (E i `&` ball j)) a].
pose Z0 j := F j `&` [set a | (upper_metric_density k (psi j) a <= 0)%E].
pose Zi j := [set a | (+oo <= upper_metric_density k (psi j) a)%E].
have hF j : borel_set (F j).
  have -> : F j = D `\` ~` ball j by rewrite /F setDE setCK.
  exact: (borel_set_difference hD (borel_set_complement (rectifiable_sum_ball_borel j))).
have hS j l : borel_set (S j l).
  exact: (@structure_rectifiable_density_stratum_borel R RnM k (psi j) (F j) l.+1%:R
    (rectifiable_sum_ball_measure j) (hF j)).
have hSW j l : S j l `<=` E i `&` ball j by move=> a [[hDa hBa] _]; split=> //; exact: hDE.
have hW j : measure_measurable HK (E i `&` ball j).
  exact: (measure_measurable_intersection hHm (hE i).1 (@closed_ball_measurable R n k j)).
have hT j l : HK (S j l `\` T j l) = 0.
  exact: (@finite_measurable_subset_approximate_tangent_equal R k n (E i `&` ball j) (S j l) (hW j)
    (borel_regular_borel_measurable hHm hHr (hS j l)) (hSW j l)
    (@locally_rectifiable_ball_finite R n k (E i) j (hE i))).
have hG j l : HK (S j l `\` Good j l) = 0.
  exact: (@stratum_omitted_density_hausdorff_null (psi j) (F j) l.+1%:R (rectifiable_sum_ball_measure j)
    (rectifiable_sum_ball_borel_regular j) (rectifiable_sum_ball_finite j) (hF j)).
have hZ0 j : HK (Z0 j) = 0.
  apply: (@rectifiable_sum_ball_zero_density_null i j).
  - by move=> a [[hDa hBa] _]; split=> //; exact: hDE.
  - by move=> a [_ h].
have hZi j : HK (Zi j) = 0 := rectifiable_sum_ball_infinite_density_null j.
have hN0 : HK (E i `\` D) = 0.
  by apply: (measure_null_subset hHm _ hnull)=> x [hx hn]; split=> //; exact: hEBo.
have h1 : HK (\bigcup_(j in [set: nat]) (Z0 j `|` Zi j)) = 0.
  exact: (measure_null_countable_union hHm (countableP [set: nat])
    (fun j _ => measure_null_union hHm (hZ0 j) (hZi j))).
have h2 j : HK (\bigcup_(l in [set: nat]) ((S j l `\` Good j l) `|` (S j l `\` T j l))) = 0.
  exact: (measure_null_countable_union hHm (countableP [set: nat])
    (fun l _ => measure_null_union hHm (hG j l) (hT j l))).
have h3 : HK (\bigcup_(j in [set: nat]) \bigcup_(l in [set: nat])
    ((S j l `\` Good j l) `|` (S j l `\` T j l))) = 0.
  exact: (measure_null_countable_union hHm (countableP [set: nat]) (fun j _ => h2 j)).
apply: (measure_null_subset hHm _ (measure_null_union hHm (measure_null_union hHm hN0 h1) h3)).
move=> x [hEx hnP].
apply: contrapT=> hNx; apply: hnP.
have hDx : D x by apply: contrapT=> hn; apply: hNx; left; left; split.
pose j := Num.bound (inner_norm hBn x).
have hxj : inner_norm hBn x < j%:R := archi_boundP (inner_norm_nonnegative hBn x).
have hBx : ball j x.
  by rewrite /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN; exact: ltW.
have hFx : F j x by split.
have hpos : ~ (upper_metric_density k (psi j) x <= 0)%E.
  by move=> h; apply: hNx; left; right; exists j=> //; left; split.
have hfin : ~ (+oo <= upper_metric_density k (psi j) x)%E.
  by move=> h; apply: hNx; left; right; exists j=> //; right.
have [y [ey hy]] : exists y : R, upper_metric_density k (psi j) x = y%:E /\ 0 < y.
  move: hpos hfin; case: (upper_metric_density k (psi j) x) => [y| |] hpos hfin.
  - exists y; split=> //; rewrite ltNge; apply/negP=> h; apply: hpos; rewrite lee_fin.
    exact: h.
  - by exfalso; apply: hfin.
  - by exfalso; apply: hpos; exact: leNye.
pose l := maxn (Num.bound y) (Num.bound y^-1).
have hb1 : y < l.+1%:R.
  apply: (lt_le_trans (archi_boundP (ltW hy))); rewrite ler_nat.
  exact: (leq_trans (leq_maxl _ _) (leqnSn _)).
have hb2 : y^-1 < l.+1%:R.
  have hy' : 0 <= y^-1 by rewrite invr_ge0; exact: ltW.
  apply: (lt_le_trans (archi_boundP hy')); rewrite ler_nat.
  exact: (leq_trans (leq_maxr _ _) (leqnSn _)).
have hSx : S j l x.
  split=> //; rewrite ey; apply/andP; split; rewrite lte_fin //.
  by rewrite invf_plt ?posrE ?ltr0Sn.
have hGx : Good j l x.
  by apply: contrapT=> hn; apply: hNx; right; exists j=> //; exists l=> //; left; split.
have hTx : T j l x.
  by apply: contrapT=> hn; apply: hNx; right; exists j=> //; exists l=> //; right; split.
change (cone mu x = cone (measure_restrict HK (E i)) x).
rewrite (rectifiable_sum_cone_ball_local hxj).
have hWhole : measure_restrict (psi j) setT = psi j.
  by apply: funext=> A; rewrite /measure_restrict setTI.
have hLocal := @restricted_approximate_tangent_equal R Rn (inner_norm hBn) NX k (psi j) (S j l) setT x
  (rectifiable_sum_ball_measure j) (subsetT _).
rewrite setTD hWhole in hLocal.
rewrite -(hLocal hGx).
rewrite (@structure_density_stratum_tangent_agreement R n k (psi j) (F j) l.+1%:R x
  (rectifiable_sum_ball_measure j) (rectifiable_sum_ball_borel_regular j)
  (rectifiable_sum_ball_finite j) (ltr0Sn _ _)).
rewrite hTx.
exact: (@approximate_tangent_cone_closed_ball_local R n k (E i) j%:R x hxj).
Qed.

(** Source for [rectifiable_sum_tangent_agree]: blueprint
    new:density_tangent(c) and al:3.5:lem; Allard 3.5(1)(b), p. 432: for
    H^k almost all x ∈ E_i, both Tan^k(μ, x) and Tan^k(H^k⌞E_i, x) belong
    to G(n, k) and they are equal. *)
Theorem rectifiable_sum_tangent_agree i :
  measure_almost_everywhere_on HK (E i)
    (partial_function_agreement (tau mu) (tau (measure_restrict HK (E i)))).
Proof.
have hHm := @hausdorff_measure_is_measure R RnM k.
have h1 := rectifiable_sum_tangent_equal i.
have h2 := @set_approximate_tangent_plane_ae R n k (E i) (hE i).
apply: (measure_null_subset hHm _ (measure_null_union hHm h1 h2)).
move=> x [hEx hn].
apply: contrapT=> hNx; apply: hn.
have hc1 : cone mu x = cone (measure_restrict HK (E i)) x.
  by apply: contrapT=> h; apply: hNx; left; split.
have [S hS] : exists S, partial_function_graph (tau (measure_restrict HK (E i))) x S.
  by apply: contrapT=> h; apply: hNx; right; split.
exists S; split=> //.
by apply/approximate_tangent_planeE; rewrite hc1; exact: hS.
Qed.

(** Source for [rectifiable_sum_tangent_plane_ae]: blueprint
    new:density_tangent(b), used in the proof of al:3.5(1); Allard
    3.5(1)(a), p. 432: Tan^k(μ, x) ∈ G(n, k) for μ almost all x. A set N
    is μ null if H^k(E_l ∩ N) = 0 for every l. *)
Theorem rectifiable_sum_tangent_plane_ae :
  measure_almost_everywhere mu [set x | exists S, partial_function_graph (tau mu) x S].
Proof.
have hHm := @hausdorff_measure_is_measure R RnM k.
rewrite /measure_almost_everywhere /rectifiable_sum_measure.
set P := [set x | _].
have hge l : [set: nat] l -> (0 <= (c l)%:E * HK (E l `&` ~` P))%E.
  by move=> _; apply: mule_ge0; [rewrite lee_fin; exact: ltW|exact: measure_nonnegative].
apply/(nonnegative_sum_zero_iff hge)=> l _.
have h0 : HK (E l `&` ~` P) = 0.
  apply: (measure_null_subset hHm _ (rectifiable_sum_tangent_agree l)).
  by move=> x [hx hn]; split=> //; move=> [S [hS _]]; apply: hn; exists S.
by rewrite h0 mule0.
Qed.

(** Source for [rectifiable_sum_measurable]: Federer 2.1.2, p. 54, and
    Allard 3.5, p. 431: a set A is μ measurable if E_l ∩ A is H^k
    measurable for every l, because
    μ(T) = Σ_l c_l (H^k(E_l ∩ T ∩ A) + H^k(E_l ∩ T ∖ A)) for T ⊆ R^n.
    Supporting lemma. *)
Lemma rectifiable_sum_measurable A :
  (forall l, measure_measurable HK (E l `&` A)) -> measure_measurable mu A.
Proof.
have hHm := @hausdorff_measure_is_measure R RnM k.
move=> hA T; rewrite /rectifiable_sum_measure.
have hge (B : set RnM) l : [set: nat] l -> (0 <= (c l)%:E * HK (E l `&` B))%E.
  by move=> _; apply: mule_ge0; [rewrite lee_fin; exact: ltW|exact: measure_nonnegative].
rewrite -nonnegative_sum_add; [|exact: hge|exact: hge].
apply: nonnegative_sum_ext=> l _.
have e1 := hA l (E l `&` T).
have e2 : (E l `&` T) `&` (E l `&` A) = E l `&` (T `&` A).
  by apply/seteqP; split=> x; [move=> [[h1 h2] [_ h3]]|move=> [h1 [h2 h3]]].
have e3 : (E l `&` T) `\` (E l `&` A) = E l `&` (T `\` A).
  apply/seteqP; split=> x; first by move=> [[h1 h2] h3]; split=> //; split=> // h4; apply: h3.
  by move=> [h1 [h2 h3]]; split=> //; move=> [_ h4]; apply: h3.
rewrite e1 e2 e3 ge0_muleDr //; exact: measure_nonnegative.
Qed.

(** Source for [rectifiable_sum_tangent_measurable]: blueprint
    new:density_tangent(b), used in the proof of al:3.5(1); Allard
    3.5(1)(b), p. 432, and Federer 2.3.2, p. 73: [x ↦ Tan^k(μ, x)] is μ
    measurable. For open U ⊆ G(n, k), the set of x ∈ E_l with
    Tan^k(μ, x) ∈ U differs by an H^k null set from the H^k measurable set
    of x ∈ E_l with Tan^k(H^k⌞E_l, x) ∈ U. *)
Theorem rectifiable_sum_tangent_measurable : is_measure_measurable_function mu (tau mu).
Proof.
have hHm := @hausdorff_measure_is_measure R RnM k.
split; first exact: rectifiable_sum_tangent_plane_ae.
move=> U hU; apply: rectifiable_sum_measurable=> l.
have hM := @set_tangent_plane_measurable R n k (E l) (hE l).
have hP := measurable_function_open_preimage hM hU.
have hPl := measurable_restriction_intersection_transfer hHm (hE l).1 hP.
have hN : HK (E l `\` partial_function_agreement (tau mu) (tau (measure_restrict HK (E l)))) = 0.
  exact: (rectifiable_sum_tangent_agree l).
apply: (measurable_set_null_modification hHm hN _ hPl)=> x hNx.
have hag : E l x -> partial_function_agreement (tau mu) (tau (measure_restrict HK (E l))) x.
  by move=> hx; apply: contrapT=> h; apply: hNx; split.
split.
- move=> [[S [hS hUS]] hx]; have [S' [h1 h2]] := hag hx.
  have e := partial_function_single_valued hS h2.
  by split=> //; exists S'; split=> //; rewrite -e.
- move=> [hx [S [hS hUS]]]; have [S' [h1 h2]] := hag hx.
  have e := partial_function_single_valued hS h1.
  by split=> //; exists S'; split=> //; rewrite -e.
Qed.

End RectifiableTangent.
