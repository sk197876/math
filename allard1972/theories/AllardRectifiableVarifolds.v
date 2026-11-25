(** Allard (1972), 3.5, printed pp. 431–432, specialised to M = U = R^n;
    blueprint al:3.5, al:3.5:lem and al:2.8(4)(a). Suppose E ⊆ R^n is
    H^k measurable and E ∩ K is (H^k, k) rectifiable (Federer 3.2.14) for
    every compact K ([is_locally_rectifiable_set]). Allard sets
    g_E(x) = (x, Tan^k(H^k⌞E, x)) and defines the varifold

        v(E)(A) = H^k(g_E^{-1}[A])   for A ⊆ G_k(R^n),

    where Tan^k(H^k⌞E, x) is the approximate tangent cone of Federer
    3.2.16, regarded as a member of G(n, k) when it is a k dimensional
    subspace ([approximate_tangent_plane]). This file proves that
    Tan^k(H^k⌞E, x) ∈ G(n, k) for H^k almost all x ∈ E
    ([set_approximate_tangent_plane_ae]; Federer 3.2.19), characterises
    v(E) by its values on Borel sets ([is_set_varifold]), proves that v(E)
    is determined by them ([set_varifold_unique]) and that
    ‖v(E)‖(B) = H^k(E ∩ B) for Borel B ([set_varifold_weight_borel]), and
    defines the rectifiable varifolds RV_k(R^n)
    ([is_rectifiable_varifold]). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology normedtype lra cardinality.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric NormMetric
  HilbertFormCompactness LinearBasis FiniteCoordinates Hom GrassmannSubspaces ExtendedRealOrderTopology PartialFunctionUP
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureRestriction RadonMeasureUP
  BorelRegularMeasureUP TopologicalBorel HausdorffMeasure HausdorffClosedCoverAgreement
  MetricClosedBalls EuclideanClosedBallCompact MetricDensities MetricDensityZeroPowerMass
  MeasureApproximateTangentUP RectifiableTangentPlaneUP RectifiableSetUP RectifiableDensityTangent
  RestrictedApproximateTangent NonnegativeSum MeasureFiniteClosure MeasureSplit BorelFunctionUP
  BorelFunctionBasic.
From Allard Require Import AllardGrassmann AllardGrassmannSubspaces AllardVarifolds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableVarifolds.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation RnM := (inner_metric_space hBn).
Local Notation NX := (inner_norm_real_norm hBn).
Local Notation RNM := (real_norm_metric_space NX).
Local Notation GA := (projection_grassmann R n k).
Local Notation GB := (grassmann_bundle R n k).
Local Notation HK := (@hausdorff_measure R RnM k).

(** Source for [approximate_tangent_plane_graph]: Allard 3.5, p. 431,
    and Federer 3.2.16, p. 252: S ∈ G(n, k) represents Tan^k(μ, x) if the
    approximate tangent cone of μ at x equals im S. Definition. *)
Definition approximate_tangent_plane_graph (mu : set Rn -> \bar R) (x : RnM) (S : GA) : Prop :=
  measure_approximate_tangent_cone NX mu k x = [set v | exists w, (set_val S : Hom Rn Rn) w = v].

(** Source for [approximate_tangent_plane_functional]: Allard 2.3,
    p. 421: an orthogonal projection is determined by its image, so at
    most one S ∈ G(n, k) represents Tan^k(μ, x). Supporting lemma. *)
Lemma approximate_tangent_plane_functional (mu : set Rn -> \bar R) (x : RnM) (S T : GA) :
  approximate_tangent_plane_graph mu x S -> approximate_tangent_plane_graph mu x T -> S = T.
Proof.
move=> hS hT.
have e : [set v | exists w, (set_val S : Hom Rn Rn) w = v] =
    [set v | exists w, (set_val T : Hom Rn Rn) w = v] := etrans (esym hS) hT.
have hP : projector_subspace R n k S = projector_subspace R n k T.
  apply: grassmann_ext=> y; rewrite !projector_subspaceE; split=> h.
  - have h' : [set v | exists w, (set_val T : Hom Rn Rn) w = v] y by rewrite -e.
    exact: h'.
  - have h' : [set v | exists w, (set_val S : Hom Rn Rn) w = v] y by rewrite e.
    exact: h'.
by rewrite -(subspace_projectorK S) -(subspace_projectorK T) hP.
Qed.

(** Source for [approximate_tangent_plane]: Allard 3.5, p. 431: the
    partial map x ↦ Tan^k(μ, x) ∈ G(n, k), defined where the approximate
    tangent cone of Federer 3.2.16 is a k dimensional subspace.
    Definition. *)
Definition approximate_tangent_plane (mu : set Rn -> \bar R) : partial_function RnM GA.
Proof.
refine (@Build_partial_function RnM GA (approximate_tangent_plane_graph mu) _).
move=> x S T hS hT; exact: approximate_tangent_plane_functional hS hT.
Defined.

(** Source for [approximate_tangent_planeE]: the graph of
    [approximate_tangent_plane]. Supporting lemma. *)
Lemma approximate_tangent_planeE (mu : set Rn -> \bar R) (x : RnM) (S : GA) :
  partial_function_graph (approximate_tangent_plane mu) x S <->
  measure_approximate_tangent_cone NX mu k x = [set v | exists w, (set_val S : Hom Rn Rn) w = v].
Proof. by []. Qed.

(** Source for [approximate_tangent_plane_exists]: Federer 3.2.19,
    p. 256, and Allard 2.3, p. 421: if Tan^k(μ, x) is a k dimensional
    subspace in the sense of Federer, then it is represented by a member
    of G(n, k). Supporting lemma. *)
Lemma approximate_tangent_plane_exists (mu : set Rn -> \bar R) (x : RnM) :
  is_m_dimensional_approximate_tangent k mu x ->
  exists S, partial_function_graph (approximate_tangent_plane mu) x S.
Proof.
move=> [P hP]; exists (subspace_projector R n k P); rewrite approximate_tangent_planeE hP.
have e : projector_subspace R n k (subspace_projector R n k P) = P := projector_subspaceK P.
apply/seteqP; split=> v /= hv.
- apply: (proj1 (projector_subspaceE (subspace_projector R n k P) v)); by rewrite e.
- have h := proj2 (projector_subspaceE (subspace_projector R n k P) v) hv.
  by rewrite e in h.
Qed.

(** Source for [closed_ball_complement_zero_density]: Federer 2.10.19,
    p. 181: if |x| < j, then Θ^k(H^k⌞(E ∖ B(0, j)), x) = 0, because
    B(x, r) ⊆ B(0, j) for small r. Supporting lemma. *)
Lemma closed_ball_complement_zero_density (E : set Rn) (j : R) (x : Rn) :
  inner_norm hBn x < j ->
  partial_function_graph (@metric_density R RNM k
    (measure_restrict HK (E `\` (E `&` metric_closed_ball (0 : RNM) j)))) x 0%E.
Proof.
move=> hx.
apply: (@small_power_mass_metric_zero_density R RNM k HK _ x (@hausdorff_measure_is_measure R RnM k)).
move=> e he; exists (j - inner_norm hBn x); split; first by rewrite subr_gt0.
move=> r /andP [hr hrj].
have -> : (E `\` (E `&` metric_closed_ball (0 : RNM) j)) `&` metric_closed_ball (x : RNM) r = set0.
  apply/seteqP; split=> y // [[hEy hn] hy]; apply: hn; split=> //.
  have ht := metric_triangle (0 : RNM) (x : RNM) (y : RNM).
  move: hy; rewrite /metric_closed_ball /= => hy.
  rewrite !real_norm_metric_distanceE in ht hy.
  rewrite !sub0r !inner_normN in ht.
  rewrite /= real_norm_metric_distanceE sub0r inner_normN.
  lra.
rewrite (measure_empty (@hausdorff_measure_is_measure R RnM k)) lee_fin.
by apply: mulr_ge0; [exact: ltW|apply: exprn_ge0; exact: ltW].
Qed.

(** Source for [closed_ball_norm_metricE]: the closed ball B(0, j) of
    R^n is the same set for the Euclidean metric and for the metric of the
    Euclidean norm. Supporting lemma. *)
Lemma closed_ball_norm_metricE (j : R) :
  metric_closed_ball (0 : RNM) j = metric_closed_ball (0 : RnM) j.
Proof.
apply/seteqP; split=> y; rewrite /metric_closed_ball /=.
- by rewrite real_norm_metric_distanceE inner_metric_distanceE.
- by rewrite real_norm_metric_distanceE inner_metric_distanceE.
Qed.

(** Source for [approximate_tangent_cone_closed_ball_local]: blueprint
    al:3.5:lem, “since Tan^k is local”: if |x| < j, then
    Tan^k(H^k⌞(E ∩ B(0, j)), x) = Tan^k(H^k⌞E, x) (Federer 3.2.16).
    Supporting lemma. *)
Lemma approximate_tangent_cone_closed_ball_local (E : set RnM) (j : R) (x : RnM) :
  inner_norm hBn x < j ->
  measure_approximate_tangent_cone NX (measure_restrict HK (E `&` metric_closed_ball (0 : RnM) j)) k x =
  measure_approximate_tangent_cone NX (measure_restrict HK E) k x.
Proof.
move=> hx; rewrite -closed_ball_norm_metricE.
apply: restricted_approximate_tangent_equal.
- have h := @hausdorff_measure_is_measure R RnM k; exact h.
- exact: subIsetl.
- exact: (closed_ball_complement_zero_density E hx).
Qed.

(** Source for [is_locally_rectifiable_set]: Allard 3.5, p. 431: E is
    H^k measurable and E ∩ K is (H^k, k) rectifiable for every compact K,
    in the sense of Federer 3.2.14 (blueprint new:rectifiable_equiv).
    Definition. *)
Definition is_locally_rectifiable_set (E : set RnM) : Prop :=
  measure_measurable HK E /\
  forall K : set RnM, compact K -> is_measure_m_rectifiable HK k (E `&` K).

(** Source for [set_approximate_tangent_plane_ae]: blueprint
    al:3.5:lem and al:2.8(4)(a)(b): g_E is defined at H^k almost all
    points of E, that is Tan^k(H^k⌞E, x) ∈ G(n, k) for H^k almost all
    x ∈ E. The proof applies Federer 3.2.19, p. 256, to E ∩ B(0, j) and
    uses that Tan^k is local. Direct formalisation. *)
Theorem set_approximate_tangent_plane_ae (E : set RnM) :
  is_locally_rectifiable_set E ->
  measure_almost_everywhere_on HK E
    [set x | exists S, partial_function_graph (approximate_tangent_plane (measure_restrict HK E)) x S].
Proof.
move=> [hEm hEr].
have hm := @hausdorff_measure_is_measure R RnM k.
have hr := @hausdorff_measure_borel_regular R RnM k.
pose B (j : nat) := metric_closed_ball (0 : RnM) j%:R.
pose T (j : nat) := [set x | is_m_dimensional_approximate_tangent k (measure_restrict HK (E `&` B j)) x].
have hBc j : compact (B j) := @euclidean_closed_metric_ball_compact R n (0 : RnM) j%:R.
have hBm j : measure_measurable HK (B j).
  exact: (@borel_regular_borel_measurable R RnM HK hm hr (B j)
    (closed_borel_set (@metric_closed_ball_closed R RnM (0 : RnM) j%:R))).
have hEBm j : measure_measurable HK (E `&` B j) := measure_measurable_intersection hm hEm (hBm j).
have hj j : HK ((E `&` B j) `\` T j) = 0.
  have h319 := federer_3_2_19 (hEr _ (hBc j)) (hEBm j).
  have [h _] := h319.
  apply: (measure_null_subset hm _ h)=> x [hx hnT]; split=> //; move=> [_ hT]; exact: hnT hT.
apply: (measure_null_subset hm _ (measure_null_countable_union hm (countableP [set: nat])
  (fun j _ => hj j))).
move=> x [hEx hnP].
have hxj : inner_norm hBn x < (Num.bound (inner_norm hBn x))%:R.
  exact: (archi_boundP (inner_norm_nonnegative hBn x)).
exists (Num.bound (inner_norm hBn x)) => //; split.
- split=> //; rewrite /B /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN; exact: ltW.
- move=> hT; apply: hnP.
  have [S hS] := approximate_tangent_plane_exists hT.
  exists S; rewrite approximate_tangent_planeE -(approximate_tangent_cone_closed_ball_local E hxj).
  exact: hS.
Qed.

(** Source for [set_varifold_preimage]: Allard 3.5, p. 431: the set
    g_E^{-1}[B] = {x ∈ E : (x, Tan^k(H^k⌞E, x)) ∈ B}. Definition. *)
Definition set_varifold_preimage (E : set RnM) (B : set GB) : set RnM :=
  [set x | E x /\ exists S, partial_function_graph (approximate_tangent_plane (measure_restrict HK E)) x S /\
    B (x, S)].

(** Source for [is_set_varifold]: Allard 3.5, p. 431, and blueprint
    al:3.5: W is v(E), that is W ∈ V_k(R^n) and W(B) = H^k(g_E^{-1}[B])
    for every Borel subset B of G_k(R^n). Definition. *)
Record is_set_varifold (E : set RnM) (W : set GB -> \bar R) : Prop := {
  (** Source for [set_varifold_varifold]: v(E) ∈ V_k(R^n), Allard 3.5,
      p. 431. *)
  set_varifold_varifold : is_varifold W;
  (** Source for [set_varifold_borel]: v(E)(B) = H^k(g_E^{-1}[B]) for
      Borel B, Allard 3.5, p. 431. *)
  set_varifold_borel : forall B : set GB, borel_set B -> W B = HK (set_varifold_preimage E B)
}.

(** Source for [set_varifold_unique]: blueprint al:3.5: v(E) is
    determined by its values on Borel sets, both measures being Radon
    measures (Federer 2.2.5). Direct formalisation. *)
Theorem set_varifold_unique (E : set RnM) (W1 W2 : set GB -> \bar R) :
  is_set_varifold E W1 -> is_set_varifold E W2 -> W1 = W2.
Proof.
move=> [[hm1 hr1] h1] [[hm2 hr2] h2].
have hU (U : set GB) : open U -> W1 U = W2 U.
  by move=> hUo; rewrite (h1 _ (open_borel_set hUo)) (h2 _ (open_borel_set hUo)).
apply: funext=> A; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (radon_outer_greatest hr2)=> U hUo hAU; rewrite -(hU _ hUo).
  exact: (measure_mono hm1 hAU).
- apply: (radon_outer_greatest hr1)=> U hUo hAU; rewrite (hU _ hUo).
  exact: (measure_mono hm2 hAU).
Qed.

(** Source for [set_varifold_weight_borel]: blueprint al:3.5:lem:
    ‖v(E)‖(B) = H^k(E ∩ B) for every Borel subset B of R^n, since
    π ∘ g_E is the identity on the domain of g_E and g_E is defined at
    H^k almost all points of E. Direct formalisation. *)
Theorem set_varifold_weight_borel (E : set RnM) (W : set GB -> \bar R) (B : set RnM) :
  is_locally_rectifiable_set E -> is_set_varifold E W -> borel_set B ->
  varifold_weight W B = HK (E `&` B).
Proof.
move=> hE hW hB.
have hm := @hausdorff_measure_is_measure R RnM k.
have hpre : borel_set ((@grassmann_bundle_point R n k) @^-1` B).
  exact: (borel_function_preimage (continuous_borel_function (@grassmann_bundle_point_continuous R n k)) hB).
rewrite varifold_weightE.
have -> : [set z : GB | B z.1] = (@grassmann_bundle_point R n k) @^-1` B by [].
rewrite (set_varifold_borel hW hpre).
have hnull := set_approximate_tangent_plane_ae hE.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: measure_mono=> //; move=> x [hEx [S [_ hBx]]]; by split.
- have hc := @measure_binary_cover R RnM HK hm (E `&` B)
    (set_varifold_preimage E ((@grassmann_bundle_point R n k) @^-1` B))
    (E `\` [set x | exists S, partial_function_graph (approximate_tangent_plane (measure_restrict HK E)) x S]).
  have hsub : E `&` B `<=` set_varifold_preimage E ((@grassmann_bundle_point R n k) @^-1` B) `|`
      (E `\` [set x | exists S, partial_function_graph (approximate_tangent_plane (measure_restrict HK E)) x S]).
    move=> x [hEx hBx]; case: (pselect (exists S, partial_function_graph
      (approximate_tangent_plane (measure_restrict HK E)) x S))=> [[S hS]|hn].
    + by left; split=> //; exists S.
    + by right.
  have := hc hsub; by rewrite hnull adde0.
Qed.

(** Source for [is_rectifiable_varifold]: Allard 3.5, p. 431: V ∈
    RV_k(R^n) if V ∈ V_k(R^n) and there are positive numbers c_1, c_2, …
    and sets E_1, E_2, … as in [is_locally_rectifiable_set] with
    V(A) = Σ_i c_i v(E_i)(A) for A ⊆ G_k(R^n). Definition. *)
Definition is_rectifiable_varifold (V : set GB -> \bar R) : Prop :=
  is_varifold V /\
  exists (c : nat -> R) (E : nat -> set RnM) (W : nat -> set GB -> \bar R),
    [/\ forall i, 0 < c i, forall i, is_locally_rectifiable_set (E i),
      forall i, is_set_varifold (E i) (W i) &
      forall A, V A = nonnegative_sum [set: nat] (fun i => ((c i)%:E * W i A)%E)].
End RectifiableVarifolds.
