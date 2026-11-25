(** Federer (1969), 2.7.16, pp. 134–135: "We verify next that, for every
    linear endomorphism f of R^n, L^n[f(S)] = |det f| . L^n(S) whenever S is
    a subset of R^n. In case det f = 0, im f is a proper subspace of R^n,
    hence has L^n measure 0. In case det f <> 0, the assertion to be proved
    is equivalent to the equation f_#(L^n) = |det f|^{-1} . L^n." The proof
    follows Federer: f_#(L^n) is a Haar measure of R^n
    (TranslationInvariantHaar.v), hence f_#(L^n) = chi(f) L^n with chi(f) >
    0; chi(f) = 1 for orthogonal f, because f maps the open unit ball onto
    itself; chi(f) = (c_1 ... c_n)^{-1} for f(x) = (c_1 x_1, ..., c_n x_n)
    with c_i > 0, because f maps {x : 0 < x_i < 1} onto {x : 0 < x_i < c_i};
    and by 1.7.3, p. 30, every f with det f <> 0 satisfies f o g = h o d
    with g, h orthogonal and d of the second type, which is how "all maps of
    these two special types generate GL(n, R)" is used. For det f = 0 the
    image of f lies in a hyperplane {y : y . w = 0}, w a unit vector with
    f*(w) = 0 (1.7.4, p. 30, and 1.7.6, p. 33), and the hyperplane is the
    image of a coordinate hyperplane under an orthogonal map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module tvs.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground FiniteCoordinates GrassmannAbbreviations
  EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  EuclideanCoordinateMetric EuclideanCoordinateTopology LinearBasis OrthogonalMaps OrthonormalFamilies
  OrthogonalFinite OrthogonalImageBasis InnerFiniteSynthesis AdjointUP Adjoint AdjointDeterminant
  TensorUP HomeomorphismUP EquivariantPushforward TopologicalBorel MeasureUP MeasureBasic
  MeasurePushforward MeasureSplit BorelRegularMeasureUP MeasureCoordinateTransport ProperMapUP
  CompactSupportFunctionUP RealIntegralFunctionalUP DaniellSpacePushforward
  LebesgueScalarMeasure EuclideanLebesgue EuclideanLebesgueDimensions EuclideanAdditiveGroup
  EuclideanLebesgueTranslation EuclideanLebesgueBoxes TranslationInvariantHaar EuclideanLebesgueHaar
  EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LinearImage.
Variable R : realType.
Variable n : nat.
Local Notation V := (R_n R n).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation hb := (@coordinate_basisP R n).
Local Notation eps := (@coordinate_basis R n).
Local Notation K := (@compactly_supported_continuous_functions R E).

(** Source for [euclidean_linear_homeomorphism]: a linear automorphism
    of R^n with inverse g is a homeomorphism, Federer 1.7.1, p. 28;
    supporting 2.7.16, p. 135. *)
Lemma euclidean_linear_homeomorphism (f g : {linear V -> V}) : cancel f g -> cancel g f ->
  is_homeomorphism_with_inverse (f : E -> E) (g : E -> E).
Proof.
move=> hfg hgf; constructor=> //; exact: euclidean_linear_continuous.
Qed.

(** Source for [euclidean_linear_image_invariant]: Federer 2.7.16,
    p. 135, "If z in R^n and T a subset of R^n, then
    f_#(L^n)[z + T] = L^n[f^{-1}(z) + f^{-1}(T)] = f_#(L^n)[T]": the image
    measure f_#(L^n) of a linear automorphism f is an invariant Borel
    measure. Direct formalisation of the displayed computation. *)
Lemma euclidean_linear_image_invariant (f g : {linear V -> V}) : cancel f g -> cancel g f ->
  is_invariant_borel_measure (fun x y : E => x + y) (measure_pushforward (f : E -> E) Leb).
Proof.
move=> hfg hgf; have hh := euclidean_linear_homeomorphism hfg hgf.
constructor.
- exact: measure_pushforward_is_measure (euclidean_lebesgue_is_measure R n).
- exact: (@homeomorphic_pushforward_borel_regular R E E Leb (euclidean_lebesgue_is_measure R n)
    (f : E -> E) (g : E -> E) hfg hgf (@euclidean_linear_continuous R n f) (@euclidean_linear_continuous R n g)
    (euclidean_lebesgue_borel_regular R n)).
- move=> C hC; rewrite /measure_pushforward.
  exact: euclidean_compact_finite (homeomorphism_with_inverse_proper hh hC).
- move=> z; apply: funext=> T; rewrite /measure_pushforward.
  have he : (f : E -> E) @^-1` ((fun y : E => z + y) @^-1` T) =
      euclidean_translation (g z) @^-1` ((f : E -> E) @^-1` T).
    by apply/seteqP; split=> x /=; rewrite /euclidean_translation linearD hgf.
  rewrite he.
  have := congr1 (fun mu => mu ((f : E -> E) @^-1` T)) (euclidean_lebesgue_translation_pushforward (g z)).
  exact.
Qed.

(** Source for [euclidean_linear_image_positive]: supporting lemma for
    Federer 2.7.16, p. 135: f_#(L^n) is positive on the compact set
    f(Q), Q the closed unit cube. *)
Lemma euclidean_linear_image_positive (f g : {linear V -> V}) : cancel f g -> cancel g f ->
  compact ((f : E -> E) @` [set x : E | forall i, 0 <= x i <= 1]) /\
  (0 < measure_pushforward (f : E -> E) Leb ((f : E -> E) @` [set x : E | forall i, (0 <= x i <= 1)%R]))%E.
Proof.
move=> hfg hgf; have [hC hv] := @euclidean_unit_closed_cube R n.
split.
- apply: continuous_compact=> //; apply: continuous_subspaceT; exact: euclidean_linear_continuous.
- rewrite /measure_pushforward.
  have he : (f : E -> E) @^-1` ((f : E -> E) @` [set x : E | forall i, 0 <= x i <= 1]) =
      [set x : E | forall i, 0 <= x i <= 1].
    apply/seteqP; split=> x /=; last by move=> hx; exists x.
    by move=> [y hy hyx]; have := congr1 g hyx; rewrite !hfg=> <-.
  by rewrite he hv lte01.
Qed.

(** Source for [euclidean_linear_pushforward_scale]: Federer 2.7.16,
    p. 135, "thus f_#(L^n) is a Haar measure of R^n, hence
    f_#(L^n) = chi(f) . L^n with chi(f) > 0", together with
    int u o f dL^n = chi(f) int u dL^n for u in K(R^n). Direct
    formalisation. *)
Theorem euclidean_linear_pushforward_scale (f g : {linear V -> V}) : cancel f g -> cancel g f ->
  exists c : R, [/\ 0 < c,
    forall u, K u -> (@euclidean_lebesgue_integral R n) (u \o (f : E -> E)) =
      c * (@euclidean_lebesgue_integral R n) u &
    forall S, Leb ((f : E -> E) @^-1` S) = (c%:E * Leb S)%E].
Proof.
move=> hfg hgf.
have hpsi := euclidean_linear_image_invariant hfg hgf.
have [hD hposD] := euclidean_linear_image_positive hfg hgf.
have [U hU] := @euclidean_countable_open_base R n.
have [hWo hWc hWT] := @euclidean_ball_cover R n.
have [hC hv] := @euclidean_unit_closed_cube R n.
have hpos : (0 < Leb [set x : E | forall i, (0 <= x i <= 1)%R])%E by rewrite hv lte01.
have [c [hc hJ hS]] := invariant_borel_integral_multiple (euclidean_additive_lch_group R n) hU hWo hWc hWT
  (@euclidean_lebesgue_invariant_borel R n) hpsi hC hpos hD hposD.
exists c; split=> // u hu.
have [hfc hfp] : continuous (f : E -> E) /\ is_proper_map (f : E -> E).
  split; first exact: euclidean_linear_continuous.
  exact: homeomorphism_with_inverse_proper (euclidean_linear_homeomorphism hfg hgf).
have hp := daniell_pushforward_integral hfc hfp (euclidean_lebesgue_is_measure R n)
  (@euclidean_lebesgue_integral_represents R n).
rewrite -hJ //.
exact: real_integral_functional_unique_on_lattice hp (invariant_borel_integral_represents hpsi) u hu.
Qed.

(** Source for [euclidean_unit_ball_bounds]: supporting lemma for
    Federer 2.7.16, p. 135: the open unit ball {x : |x| < 1} has finite
    positive L^n measure; it contains the box
    {x : |x_i| < 1/(n+1) for every i}. *)
Lemma euclidean_unit_ball_bounds :
  (0 < Leb [set x : E | (`|x| < 1)%R])%E /\ (Leb [set x : E | (`|x| < 1)%R] < +oo)%E.
Proof.
split.
- pose r : R := (n.+1%:R)^-1.
  have hr : 0 < r by rewrite invr_gt0 ltr0n.
  have hsub : [set x : E | forall i, - r < x i < r] `<=` [set x : E | (`|x| < 1)%R].
    move=> x hx; rewrite /=; apply: le_lt_trans (euclidean_norm_coordinate_sum x) _.
    apply: (@le_lt_trans _ _ (\sum_(i < n) r)).
      by apply: ler_sum=> i _; rewrite ler_norml; have := hx i; move=> /andP[h1 h2]; rewrite !ltW.
    rewrite sumr_const card_ord -mulr_natr /r mulrC.
    by rewrite ltr_pdivrMr ?ltr0n // mul1r ltr_nat.
  apply: lt_le_trans (@measure_mono R E Leb (euclidean_lebesgue_is_measure R n) _ _ hsub).
  rewrite (@euclidean_open_box R n (fun _ => - r) (fun _ => r)); last by move=> i; lra.
  rewrite lte_fin; apply: prodr_gt0=> i _; lra.
- apply: le_lt_trans (@measure_mono R E Leb (euclidean_lebesgue_is_measure R n) _
    [set x : E | `|x - 0| <= 1] _) _.
    by move=> x /= hx; rewrite subr0 ltW.
  exact: euclidean_compact_finite (@euclidean_closed_ball_compact R n 0 1).
Qed.

(** Source for [euclidean_orthogonal_pushforward]: Federer 2.7.16,
    p. 135, "In case f is orthogonal, then f maps every open ball with
    center 0 onto itself, hence chi(f) = 1": L^n[f^{-1}(S)] = L^n(S) for
    every orthogonal endomorphism f of R^n. Direct formalisation. *)
Theorem euclidean_orthogonal_pushforward (f : {linear V -> V}) :
  is_orthogonal_map B B f -> forall S, Leb ((f : E -> E) @^-1` S) = Leb S.
Proof.
move=> hf; have [g [hfg [hgf _]]] := orthogonal_endomorphism_inverse_exists hB hb hf.
have [c [hc _ hS]] := euclidean_linear_pushforward_scale hfg hgf.
have hball : (f : E -> E) @^-1` [set x : E | (`|x| < 1)%R] = [set x : E | (`|x| < 1)%R].
  apply/seteqP; split=> x /=; rewrite !inner_norm_topologyE (orthogonal_map_norm hB hB hf) //.
have [hpos hfin] := euclidean_unit_ball_bounds.
have h1 := hS [set x : E | (`|x| < 1)%R]; rewrite hball in h1.
have hc1 : c = 1.
  move: hpos hfin h1; case: (Leb [set x : E | (`|x| < 1)%R])=> [a| |] //.
  rewrite lte_fin=> ha _ /eqP; rewrite -EFinM eqe -subr_eq0 -{1}(mul1r a) -mulrBl mulf_eq0.
  by rewrite (gt_eqF ha) orbF subr_eq0=> /eqP <-.
by move=> S; rewrite hS hc1 mul1e.
Qed.

(** Source for [euclidean_diagonal_pushforward]: Federer 2.7.16, p. 135,
    "In case there exist positive numbers c_1, ..., c_n such that
    f(x) = (c_1 x_1, ..., c_n x_n) whenever x in R^n, then
    f{x : 0 < x_i < 1} = {x : 0 < x_i < c_i}, hence
    chi(f) = (c_1 . c_2 ... c_n)^{-1}". Direct formalisation. *)
Theorem euclidean_diagonal_pushforward (c : 'I_n -> R) : (forall i, 0 < c i) ->
  forall S, Leb ((euclidean_diagonal_map c : E -> E) @^-1` S) = ((\prod_(i < n) c i)^-1%:E * Leb S)%E.
Proof.
move=> hc.
have hfg : cancel (euclidean_diagonal_map c) (euclidean_diagonal_map (fun i => (c i)^-1)).
  move=> x; apply/ffunP=> i; rewrite /= /euclidean_diagonal !ffunE mulrA mulVf ?mul1r //.
  exact: lt0r_neq0.
have hgf : cancel (euclidean_diagonal_map (fun i => (c i)^-1)) (euclidean_diagonal_map c).
  move=> x; apply/ffunP=> i; rewrite /= /euclidean_diagonal !ffunE mulrA mulfV ?mul1r //.
  exact: lt0r_neq0.
have [k [hk _ hS]] := euclidean_linear_pushforward_scale hfg hgf.
have hpre : (euclidean_diagonal_map c : E -> E) @^-1` [set x : E | forall i, 0 < x i < c i] =
    [set x : E | forall i, 0 < x i < 1].
  apply/seteqP; split=> x /= h i; have := h i; rewrite /euclidean_diagonal ffunE.
  - by rewrite pmulr_rgt0 // -{2}(mulr1 (c i)) ltr_pM2l.
  - by move=> /andP[h1 h2]; rewrite pmulr_rgt0 // h1 /= -{2}(mulr1 (c i)) ltr_pM2l.
have h1 := hS [set x : E | forall i, 0 < x i < c i].
rewrite hpre euclidean_unit_cube euclidean_open_box in h1; last by move=> i; exact: ltW (hc i).
have hp : 0 < \prod_(i < n) c i by apply: prodr_gt0=> i _.
have hbox : (\prod_(i < n) (c i - 0)) = \prod_(i < n) c i by apply: eq_bigr=> i _; rewrite subr0.
rewrite hbox -EFinM in h1; move: h1=> /eqP; rewrite eqe eq_sym=> /eqP hk1.
have hk2 : k = (\prod_(i < n) c i)^-1.
  by apply: (mulIf (lt0r_neq0 hp)); rewrite hk1 mulVf //; exact: lt0r_neq0.
by move=> S; rewrite hS hk2.
Qed.

End LinearImage.
