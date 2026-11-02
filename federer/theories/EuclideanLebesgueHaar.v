(** Federer (1969), 2.7.16, example (1), p. 134: "L^1 is the unique (left
    and right) Haar measure of the additive group of R such that L^1{t : 0 <
    t < 1} = 1. More generally, since the additive group of R^n is the
    direct sum of n factors equal to R, L^n is the unique (left and right)
    Haar measure over R^n such that L^n{x : 0 < x_i < 1 for i = 1, ..., n} =
    1." The book prints "L" in place of "L^n" in the second sentence;
    Federer's erratum, page 3, corrects book p. 134 line 26 to "L^n", and
    the statement below follows the correction. The proof applies
    TranslationInvariantHaar.v to L^1 and L^n: both are Borel regular
    (2.5.17, p. 111, and 2.6.5, p. 120), finite on compact sets, invariant
    under translations (EuclideanLebesgueTranslation.v), and positive on the
    closed unit cube. Uniqueness is 2.7.7, p. 125. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module tvs.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground FiniteCoordinates GrassmannAbbreviations
  EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  EuclideanCoordinateMetric EuclideanCoordinateTopology TopologicalGroupUP TopologicalBorel
  CountableOpenBaseUP MeasureUP MeasureBasic BorelRegularMeasureUP CompactSupportFunctionUP
  FunctionLatticeRegularityUP RealIntegralFunctionalUP MonotoneDaniellIntegralUP HaarIntegralUP
  LebesgueScalarMeasure StieltjesBorelRegularity
  EuclideanLebesgue EuclideanLebesgueRegularity EuclideanLebesgueDimensions IntervalBumpFunctions
  MeasureBijectionUP EuclideanAdditiveGroup EuclideanLebesgueTranslation EuclideanLebesgueBoxes
  TranslationInvariantHaar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section EuclideanHaar.
Variable R : realType.
Variable n : nat.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation K := (@compactly_supported_continuous_functions R E).

(** Source for [euclidean_countable_open_base]: R^n has a countable
    base, as needed for 2.5.14, p. 107, in Federer 2.7.16, p. 134; for
    n >= 1 it is supplied by 2.6.5, p. 120, and the one-point space
    R^0 has the base {empty set, R^0}. Supporting lemma. *)
Lemma euclidean_countable_open_base : exists U : nat -> set E, is_countable_open_base U.
Proof.
case: n=> [|k]; last exact: (positive_euclidean_lebesgue_regularity R k).2.2.
exists (fun j => if j is 0%N then set0 else setT); constructor.
- by move=> [|j]; [exact: open0|exact: openT].
- by [].
- move=> V hV x hx; exists 1%N; split=> // y _.
  by rewrite (coordinate_zero y) -(coordinate_zero x).
Qed.

(** Source for [euclidean_norm_coordinate_sum]: |x| <= sum_i |x_i| for
    x in R^n, by the expansion in the standard orthonormal base, Federer
    1.7.1, p. 28; supporting the compactness of coordinate boxes used in
    2.7.16, p. 134. *)
Lemma euclidean_norm_coordinate_sum (x : E) : `|x| <= \sum_i `|x i|.
Proof.
have hx : x = \sum_i x i *: (@coordinate_basis R n i : E).
  exact: esym (euclidean_coordinate_expansion x).
rewrite [in X in X <= _]hx; apply: le_trans (ler_norm_sum _ _ _) _.
apply: ler_sum=> i _; rewrite normrZ.
have h1 : `|(@coordinate_basis R n i : E)| = 1.
  by rewrite inner_norm_topologyE; exact: euclidean_coordinate_unit_norm.
by rewrite h1 mulr1.
Qed.

(** Source for [euclidean_closed_box_compact]: the closed coordinate
    box {x : a_i <= x_i <= b_i} is compact, Federer 1.7.1, p. 28;
    supporting 2.7.16, p. 134. *)
Lemma euclidean_closed_box_compact (a b : 'I_n -> R) :
  compact [set x : E | forall i, a i <= x i <= b i].
Proof.
pose r := \sum_i (`|a i| + `|b i|).
apply: (subclosed_compact _ (@euclidean_closed_ball_compact R n (0 : E) r)).
- have he : [set x : E | forall i, a i <= x i <= b i] =
      \bigcap_i ([set x : E | a i <= x i] `&` [set x : E | x i <= b i]).
    by apply/seteqP; split=> x /= h i; [move=> _; have /andP[] := h i|have [] := h i I=> -> ->].
  rewrite he; apply: closed_bigI=> i _; apply: closedI.
  + have -> : [set x : E | a i <= x i] = (fun x : E => (x i : R^o)) @^-1` [set t : R^o | a i <= t] by [].
    apply: preimage_closed; last exact: closed_ge.
    by move=> x _; exact: euclidean_coordinate_continuous.
  + have -> : [set x : E | x i <= b i] = (fun x : E => (x i : R^o)) @^-1` [set t : R^o | t <= b i] by [].
    apply: preimage_closed; last exact: closed_le.
    by move=> x _; exact: euclidean_coordinate_continuous.
- move=> x /= hx; rewrite subr0; apply: le_trans (euclidean_norm_coordinate_sum x) _.
  apply: ler_sum=> i _; have /andP[h1 h2] := hx i.
  have ha := ler_norm (- a i); rewrite normrN in ha.
  have hb := ler_norm (b i).
  have hna := normr_ge0 (a i); have hnb := normr_ge0 (b i).
  rewrite ler_norml; apply/andP; split; lra.
Qed.

(** Source for [euclidean_lebesgue_invariant_borel]: Federer 2.7.16,
    pp. 134–135: L^n is Borel regular, finite on compact sets, and
    invariant under translations. Supporting lemma. *)
Lemma euclidean_lebesgue_invariant_borel : is_invariant_borel_measure (fun x y : E => x + y) Leb.
Proof.
constructor.
- exact: euclidean_lebesgue_is_measure.
- exact: euclidean_lebesgue_borel_regular.
- move=> C hC; exact: euclidean_compact_finite hC.
- move=> z; exact: euclidean_lebesgue_translation_pushforward z.
Qed.

(** Source for [euclidean_lebesgue_integral]: the integral
    u |-> int u dL^n on K(R^n), Federer 2.5.1, p. 92, and 2.5.13, p. 106,
    the left Haar integral corresponding to L^n in 2.7.16, p. 134.
    Definition through the sealed integral map of 2.5.1. *)
Definition euclidean_lebesgue_integral : (E -> R) -> R :=
  invariant_borel_integral euclidean_lebesgue_invariant_borel.

(** Source for [euclidean_lebesgue_integral_represents]: L^n represents
    its integral on K(R^n), Federer 2.5.1, p. 92. Supporting lemma. *)
Lemma euclidean_lebesgue_integral_represents : is_real_integral_functional Leb K euclidean_lebesgue_integral.
Proof. exact: invariant_borel_integral_represents. Qed.

(** Source for [euclidean_lebesgue_integral_monotone]: the integral of
    L^n is a monotone Daniell integral on K(R^n), Federer 2.5.1, p. 92.
    Supporting lemma. *)
Lemma euclidean_lebesgue_integral_monotone : is_monotone_daniell_integral K euclidean_lebesgue_integral.
Proof. exact: invariant_borel_integral_monotone. Qed.

(** Source for [euclidean_open_ball_sequence]: the open balls
    {x : |x| < k} of R^n, k = 0, 1, 2, ..., supporting Federer 2.7.16,
    p. 134. Definition. *)
Definition euclidean_open_ball_sequence (k : nat) : set E := [set x : E | `|x| < k%:R].

(** Source for [euclidean_ball_cover]: R^n is covered by the open balls
    {x : |x| < k}, each contained in a compact closed ball, Federer
    1.7.1, p. 28; supporting 2.7.16, p. 134. *)
Lemma euclidean_ball_cover :
  [/\ forall k, open (euclidean_open_ball_sequence k),
    forall k, exists2 C, compact C & euclidean_open_ball_sequence k `<=` C &
    forall x : E, exists k, euclidean_open_ball_sequence k x].
Proof.
split.
- move=> k; have he : euclidean_open_ball_sequence k = ball (0 : E) k%:R.
    by apply/seteqP; split=> x; rewrite -ball_normE /= sub0r normrN.
  rewrite he; exact: ball_open.
- move=> k; exists [set x : E | `|x - 0| <= k%:R]; first exact: (@euclidean_closed_ball_compact R n 0 k%:R).
  by move=> x /= hx; rewrite subr0 ltW.
- move=> x; exists (Num.truncn `|x|).+1; rewrite /euclidean_open_ball_sequence /=.
  by have /andP[_ h] := truncn_itv (normr_ge0 x).
Qed.

(** Source for [euclidean_unit_closed_cube]: supporting lemma for
    Federer 2.7.16, p. 134: the closed unit cube is compact and has
    L^n measure one. *)
Lemma euclidean_unit_closed_cube :
  compact [set x : E | forall i, 0 <= x i <= 1] /\ Leb [set x : E | forall i, 0 <= x i <= 1] = 1%:E.
Proof.
split; first exact: (@euclidean_closed_box_compact (fun _ => 0) (fun _ => 1)).
rewrite (@euclidean_closed_box R n (fun _ => 0) (fun _ => 1)); last by move=> i; exact: ler01.
by congr (_%:E); rewrite big1 // => i _; rewrite subr0.
Qed.

(** Source for [euclidean_lebesgue_function_lattice_regular]: L^n is
    K(R^n) regular, as presupposed by "L^n is ... Haar measure" in
    Federer 2.7.16, p. 134 (2.7.2, p. 122). Supporting theorem. *)
Theorem euclidean_lebesgue_function_lattice_regular : is_function_lattice_regular K Leb.
Proof.
have [U hU] := euclidean_countable_open_base.
have [hWo hWc hWT] := euclidean_ball_cover.
exact: (invariant_borel_function_lattice_regular (euclidean_additive_lch_group R n) hU hWo hWc hWT
  euclidean_lebesgue_invariant_borel).
Qed.

(** Source for [euclidean_lebesgue_left_haar]: Federer 2.7.16, p. 134,
    "L^n is the ... (left ...) Haar measure over R^n". Direct
    formalisation of the existence part. *)
Theorem euclidean_lebesgue_left_haar : is_left_haar_measure (fun x y : E => x + y) Leb.
Proof.
have [U hU] := euclidean_countable_open_base.
have [hWo hWc hWT] := euclidean_ball_cover.
have [hC hv] := euclidean_unit_closed_cube.
apply: (invariant_borel_left_haar (euclidean_additive_lch_group R n) hU hWo hWc hWT
  euclidean_lebesgue_invariant_borel hC).
by rewrite hv lte01.
Qed.

(** Source for [euclidean_lebesgue_right_haar]: Federer 2.7.16, p. 134,
    "L^n is the ... (... right) Haar measure over R^n". Direct
    formalisation of the existence part. *)
Theorem euclidean_lebesgue_right_haar :
  is_right_haar_measure (fun x y : E => x + y) (fun x => - x) Leb.
Proof.
have [U hU] := euclidean_countable_open_base.
have [hWo hWc hWT] := euclidean_ball_cover.
have [hC hv] := euclidean_unit_closed_cube.
apply: (invariant_borel_right_haar (euclidean_additive_lch_group R n) (fun x y : E => addrC x y) hU hWo hWc hWT
  euclidean_lebesgue_invariant_borel hC).
by rewrite hv lte01.
Qed.

(** Source for [euclidean_haar_measure_multiple]: Federer 2.7.16,
    p. 134, the uniqueness in "the unique (left and right) Haar measure
    over R^n", before normalisation: every left or right Haar measure of
    R^n is c L^n with 0 < c < oo, by 2.7.7, p. 125. Direct
    formalisation. *)
Theorem euclidean_haar_measure_multiple (phi : set E -> \bar R) :
  is_left_haar_measure (fun x y : E => x + y) phi \/
    is_right_haar_measure (fun x y : E => x + y) (fun x => - x) phi ->
  exists2 c : R, 0 < c & forall S, phi S = (c%:E * Leb S)%E.
Proof.
have [U hU] := euclidean_countable_open_base.
have [hWo hWc hWT] := euclidean_ball_cover.
have [hC hv] := euclidean_unit_closed_cube.
have hpos : (0 < Leb [set x : E | forall i, (0 <= x i <= 1)%R])%E by rewrite hv lte01.
case=> h.
- exact: (left_haar_measure_multiple (euclidean_additive_lch_group R n) hU hWo hWc hWT
    euclidean_lebesgue_invariant_borel hC hpos h).
- exact: (right_haar_measure_multiple (euclidean_additive_lch_group R n) (fun x y : E => addrC x y) hU hWo hWc hWT
    euclidean_lebesgue_invariant_borel hC hpos h).
Qed.

(** Source for [euclidean_lebesgue_haar_unique]: Federer 2.7.16, p. 134,
    as corrected by the erratum, page 3, book p. 134 line 26: "L^n is the
    unique (left and right) Haar measure over R^n such that
    L^n{x : 0 < x_i < 1 for i = 1, ..., n} = 1". Direct formalisation of
    the uniqueness; existence is [euclidean_lebesgue_left_haar],
    [euclidean_lebesgue_right_haar] and [euclidean_unit_cube]. *)
Theorem euclidean_lebesgue_haar_unique (phi : set E -> \bar R) :
  is_left_haar_measure (fun x y : E => x + y) phi \/
    is_right_haar_measure (fun x y : E => x + y) (fun x => - x) phi ->
  phi [set x | forall i, 0 < x i < 1] = 1%:E -> phi = Leb.
Proof.
move=> hphi h1; have [c hc he] := euclidean_haar_measure_multiple hphi.
rewrite he euclidean_unit_cube mule1 in h1.
have hc1 : c = 1 by move: h1=> /eqP; rewrite eqe=> /eqP.
by apply: funext=> S; rewrite he hc1 mul1e.
Qed.

End EuclideanHaar.

Section LineHaar.
Variable R : realType.
Local Notation L1 := (@lebesgue_scalar_measure R).

(** Source for [real_additive_lch_group]: the additive group of R is a
    locally compact Hausdorff topological group, Federer 2.7.16, p. 134,
    with 2.7.1, p. 121. Supporting lemma. *)
Lemma real_additive_lch_group :
  is_locally_compact_hausdorff_group (fun x y : R => x + y) (fun x => - x) 0.
Proof.
split; last first.
- exact: locally_compactR.
- exact: (@metric_hausdorff R [the metricType R of real_line_metric R]).
split.
- by split; [exact: addrA|exact: add0r|exact: addNr].
- exact: (@add_continuous R^o).
- exact: (@opp_continuous R^o).
Qed.

(** Source for [real_interval_sequence]: the open intervals
    {t : -k < t < k} of R, supporting Federer 2.7.16, p. 134.
    Definition. *)
Definition real_interval_sequence (k : nat) : set R := `](- k%:R : R), k%:R[.

(** Source for [real_interval_cover]: R is covered by the open intervals
    {t : -k < t < k}, each contained in a compact segment; supporting
    Federer 2.7.16, p. 134. *)
Lemma real_interval_cover :
  [/\ forall k, open (real_interval_sequence k),
    forall k, exists2 C, compact C & real_interval_sequence k `<=` C &
    forall x : R, exists k, real_interval_sequence k x].
Proof.
split.
- move=> k; exact: interval_open.
- move=> k; exists `[(- k%:R : R), k%:R]; first exact: segment_compact.
  by move=> t; rewrite /real_interval_sequence /= !in_itv /= => /andP[h1 h2]; rewrite !ltW.
- move=> x; exists (Num.truncn `|x|).+1.
  have /andP[_ h] := truncn_itv (normr_ge0 x).
  by rewrite /real_interval_sequence /= in_itv /= -ltr_norml.
Qed.

(** Source for [lebesgue_scalar_compact_finite]: compact subsets of R
    have finite L^1 measure, supporting Federer 2.7.16, p. 134. *)
Lemma lebesgue_scalar_compact_finite (C : set R) : compact C -> (L1 C < +oo)%E.
Proof.
move=> hC; have [M [_ hM]] := @compact_bounded R R^o C hC.
have hlt : M < `|M| + 1 by apply: le_lt_trans (ler_norm M) _; rewrite ltrDl ltr01.
have hsub : C `<=` `[(- (`|M| + 1)), `|M| + 1].
  by move=> t ht; rewrite /= in_itv /= -ler_norml; exact: hM _ hlt t ht.
apply: le_lt_trans (@measure_mono R R L1 (lebesgue_scalar_is_measure R) _ _ hsub) _.
rewrite lebesgue_scalar_segment; first exact: ltry.
by have := normr_ge0 M; lra.
Qed.

(** Source for [lebesgue_scalar_invariant_borel]: L^1 is Borel regular,
    finite on compact sets and invariant under translations, Federer
    2.5.17, p. 111, and 2.7.16, p. 134. Supporting lemma. *)
Lemma lebesgue_scalar_invariant_borel : is_invariant_borel_measure (fun x y : R => x + y) L1.
Proof.
constructor.
- exact: lebesgue_scalar_is_measure.
- exact: lebesgue_scalar_borel_regular.
- exact: lebesgue_scalar_compact_finite.
- by move=> z; exact: measure_bijection_pushforward (lebesgue_scalar_translation z).
Qed.

(** Source for [lebesgue_scalar_left_haar]: Federer 2.7.16, p. 134,
    "L^1 is the ... (left ...) Haar measure of the additive group of R".
    Direct formalisation of the existence part. *)
Theorem lebesgue_scalar_left_haar : is_left_haar_measure (fun x y : R => x + y) L1.
Proof.
have [U hU] := @real_line_countable_open_base_exists R.
have [hWo hWc hWT] := real_interval_cover.
apply: (invariant_borel_left_haar real_additive_lch_group hU hWo hWc hWT
  lebesgue_scalar_invariant_borel (@segment_compact R 0 1)).
by rewrite lebesgue_scalar_segment ?ler01 // subr0 lte01.
Qed.

(** Source for [lebesgue_scalar_right_haar]: Federer 2.7.16, p. 134,
    "L^1 is the ... (... right) Haar measure of the additive group of
    R". Direct formalisation of the existence part. *)
Theorem lebesgue_scalar_right_haar :
  is_right_haar_measure (fun x y : R => x + y) (fun x => - x) L1.
Proof.
have [U hU] := @real_line_countable_open_base_exists R.
have [hWo hWc hWT] := real_interval_cover.
apply: (invariant_borel_right_haar real_additive_lch_group (fun x y : R => addrC x y) hU hWo hWc hWT
  lebesgue_scalar_invariant_borel (@segment_compact R 0 1)).
by rewrite lebesgue_scalar_segment ?ler01 // subr0 lte01.
Qed.

(** Source for [lebesgue_scalar_haar_unique]: Federer 2.7.16, p. 134,
    "L^1 is the unique (left and right) Haar measure of the additive group
    of R such that L^1{t : 0 < t < 1} = 1". Direct formalisation of the
    uniqueness; the normalisation of L^1 is [lebesgue_scalar_open_interval]. *)
Theorem lebesgue_scalar_haar_unique (phi : set R -> \bar R) :
  is_left_haar_measure (fun x y : R => x + y) phi \/
    is_right_haar_measure (fun x y : R => x + y) (fun x => - x) phi ->
  phi `]0, 1[ = 1%:E -> phi = L1.
Proof.
move=> hphi h1.
have [U hU] := @real_line_countable_open_base_exists R.
have [hWo hWc hWT] := real_interval_cover.
have hpos : (0 < L1 `[0%R, 1%R])%E by rewrite lebesgue_scalar_segment ?ler01 // subr0 lte01.
have [c hc he] : exists2 c : R, 0 < c & forall S, phi S = (c%:E * L1 S)%E.
  case: hphi=> h.
  - exact: (left_haar_measure_multiple real_additive_lch_group hU hWo hWc hWT
      lebesgue_scalar_invariant_borel (@segment_compact R 0 1) hpos h).
  - exact: (right_haar_measure_multiple real_additive_lch_group (fun x y : R => addrC x y) hU hWo hWc hWT
      lebesgue_scalar_invariant_borel (@segment_compact R 0 1) hpos h).
rewrite he lebesgue_scalar_open_interval ?ler01 // subr0 mule1 in h1.
have hc1 : c = 1 by move: h1=> /eqP; rewrite eqe=> /eqP.
by apply: funext=> S; rewrite he hc1 mul1e.
Qed.

End LineHaar.
