(** Federer (1969), 2.7.16, p. 136: "If S is the convex hull of n + 1 points
    v_0, ..., v_n of R^n, then L^n(S) = |(v_1 - v_0) wedge ... wedge (v_n -
    v_0)|/n!. Since the effect of a linear endomorphism f of R^n is to
    multiply both sides of this equation by |det f|, and both sides are
    invariant under translations, it suffices to verify the equation in case
    v_0 = 0 and v_1, ..., v_n form the standard orthonormal base of R^n; but
    then S = R^n cap {x : x_j >= 0 for j in {1, ..., n}, sum_j x_j <= 1} and
    using 2.6.2, 2.9.20 one inductively computes L^n(S) = int_0^1 L^{n-1}{y
    : y_j >= 0, sum_j y_j <= 1 - t} dL^1 t = int_0^1 (1-t)^{n-1}/(n-1)! dL^1
    t = 1/n!". The convex hull is specified by its defining property (the
    smallest convex set containing the points, 1.7.13, p. 37) and identified
    with the set of convex combinations. The module proves L^n of the
    standard simplex by induction with Fubini's theorem 2.6.2(3), p. 115,
    the determinant formula of 2.7.16, p. 134, for {y : y_j >= 0, sum_j y_j
    <= s} = s . S_{n-1}, and the evaluation of PowerSegmentIntegral.v in
    place of 2.9.20. Coordinates are split as R^(m+1) = R^m x R with the
    first coordinate as t, the reverse of the printed order; this is a
    relabelling. The norm of the n-vector is that of 1.7.5, p. 32, and |w_1
    wedge ... wedge w_n| = |det f| for f(e_i) = w_i (1.3.4, p. 16). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module tvs.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology FiniteCoordinates
  GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerMetric InnerNormedTopology
  CoordinateProjection EuclideanCoordinateTopology LinearBasis OrthonormalFamilies InnerConvex
  ExteriorGrading ExteriorMaps FiniteExteriorPowers ExteriorDeterminant ExteriorNorm
  ExteriorOperatorEstimate TopologicalBorel MeasureUP MeasureBasic MeasurePushforward
  PushforwardMeasurableSets MeasureSplit CountablyMeasurableUP CountablyMeasurableSubsets
  CountablyMeasurableProduct PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  SummableRealFunctionUP
  SummableRealArithmetic ProductMeasure ProductSections ProductSetFubini PointMassMeasure
  LebesgueScalarMeasure EuclideanCoordinateSplit EuclideanLebesgue EuclideanLebesgueDimensions
  EuclideanAdditiveGroup EuclideanLebesgueTranslation EuclideanLebesgueBoxes EuclideanLinearMaps
  EuclideanLebesgueDeterminant PowerSegmentIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_convex_hull]: "the convex hull of n + 1 points",
    Federer 2.7.16, p. 136: the smallest convex set (1.7.13, p. 37)
    containing A. Definition by this property. *)
Definition is_convex_hull (R : realFieldType) (V : lmodType R) (A S : set V) : Prop :=
  [/\ is_inner_convex S, A `<=` S & forall C, is_inner_convex C -> A `<=` C -> S `<=` C].

(** Source for [convex_hull_unique]: the convex hull is unique,
    supporting Federer 2.7.16, p. 136. *)
Lemma convex_hull_unique (R : realFieldType) (V : lmodType R) (A S T : set V) :
  is_convex_hull A S -> is_convex_hull A T -> S = T.
Proof.
move=> [hS hAS hSm] [hT hAT hTm]; apply/seteqP; split; [exact: hSm|exact: hTm].
Qed.

(** Source for [convex_combinations]: the points sum_i l_i v_i with
    l_i >= 0 and sum_i l_i = 1, supporting Federer 2.7.16, p. 136.
    Definition. *)
Definition convex_combinations (R : realFieldType) (V : lmodType R) m (v : 'I_m -> V) : set V :=
  [set x | exists l : 'I_m -> R, [/\ forall i, 0 <= l i, \sum_i l i = 1 & x = \sum_i l i *: v i]].

(** Source for [convex_combinations_hull]: the convex combinations of
    v_1, ..., v_m form the convex hull of these points, supporting the
    reduction in Federer 2.7.16, p. 136. Supporting lemma. *)
Lemma convex_combinations_hull (R : realFieldType) (V : lmodType R) m (v : 'I_m -> V) :
  is_convex_hull [set v i | i in setT] (convex_combinations v).
Proof.
split.
- move=> x y [l [hl hs ->]] [l' [hl' hs' ->]] t ht0 ht1.
  exists (fun i => (1 - t) * l i + t * l' i); split.
  + by move=> i; rewrite addr_ge0 ?mulr_ge0 ?subr_ge0.
  + by rewrite big_split /= -!mulr_sumr hs hs' !mulr1 subrK.
  + rewrite !scaler_sumr -big_split /=; apply: eq_bigr=> i _.
    by rewrite !scalerA scalerDl.
- move=> x [i _ <-]; exists (fun j => if j == i then 1 else 0); split.
  + by move=> j; case: (j == i).
  + by rewrite -big_mkcond /= big_pred1_eq.
  + rewrite (eq_bigr (fun j => if j == i then v i else 0)); last first.
      by move=> j _; case: (eqVneq j i)=> [->|_]; rewrite ?scale1r ?scale0r.
    by rewrite -big_mkcond /= big_pred1_eq.
- move=> C hC; elim: m v=> [|m ih] v hv x [l [hl hs ->]].
    by move: hs; rewrite big_ord0=> /eqP; rewrite eq_sym oner_eq0.
  rewrite big_ord_recl; rewrite big_ord_recl in hs.
  pose s := \sum_(i < m) l (lift ord0 i).
  have hs0 : 0 <= s by apply: sumr_ge0=> i _; exact: hl.
  have hl0 : l ord0 = 1 - s by rewrite -hs addrK.
  case: (eqVneq s 0)=> [h0|hs1].
  + have hz i : l (lift ord0 i) = 0.
      by apply/eqP; move: h0=> /eqP; rewrite psumr_eq0 ?(fun i _ => hl (lift ord0 i)) // =>
        /allP /(_ i (mem_index_enum _)) /implyP; apply.
    rewrite big1 ?addr0; last by move=> i _; rewrite hz scale0r.
    by rewrite hl0 h0 subr0 scale1r; apply: hv; exists ord0.
  + have hpos : 0 < s by rewrite lt_def hs1 hs0.
    pose y := \sum_(i < m) (l (lift ord0 i) / s) *: v (lift ord0 i).
    have hy : C y.
      apply: (ih (fun i => v (lift ord0 i))); first by move=> z [i _ <-]; apply: hv; exists (lift ord0 i).
      exists (fun i => l (lift ord0 i) / s); split.
      * by move=> i; rewrite divr_ge0.
      * by rewrite -mulr_suml mulfV.
      * by [].
    have hv0 : C (v ord0) by apply: hv; exists ord0.
    have hs1' : s <= 1 by have := hl ord0; rewrite hl0; lra.
    have h := hC _ _ hv0 hy s hs0 hs1'.
    have he : (1 - s) *: v ord0 + s *: y = l ord0 *: v ord0 + \sum_(i < m) l (lift ord0 i) *: v (lift ord0 i).
      rewrite hl0 /y scaler_sumr; congr (_ + _); apply: eq_bigr=> i _.
      by rewrite scalerA mulrCA mulfV ?mulr1 // gt_eqF.
    by rewrite -he.
Qed.

Section Simplex.
Variable R : realType.
Local Notation V n := (R_n R n).
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Leb n := (@euclidean_lebesgue_measure R n).
Local Notation L1 := (@lebesgue_scalar_measure R).

(** Source for [euclidean_standard_simplex]: Federer 2.7.16, p. 136,
    S = R^n cap {x : x_j >= 0 for j in {1, ..., n}, sum_j x_j <= 1}.
    Direct definition. *)
Definition euclidean_standard_simplex n : set (E n) :=
  [set x | (forall j, 0 <= x j) /\ \sum_j x j <= 1].

(** Source for [euclidean_coordinate_sum_continuous]: x |-> sum_j x_j is
    continuous on R^n, supporting Federer 2.7.16, p. 136. *)
Lemma euclidean_coordinate_sum_continuous n : continuous (fun x : E n => (\sum_j x j : R^o)).
Proof.
apply: continuous_big; first exact: add_continuous.
move=> j _; exact: euclidean_coordinate_continuous.
Qed.

(** Source for [euclidean_standard_simplex_closed]: the standard
    simplex is closed, hence L^n measurable; supporting Federer 2.7.16,
    p. 136. *)
Lemma euclidean_standard_simplex_closed n : closed (@euclidean_standard_simplex n).
Proof.
have he : @euclidean_standard_simplex n =
    (\bigcap_j [set x : E n | 0 <= x j]) `&` [set x : E n | \sum_j x j <= 1].
  apply/seteqP; split=> x /=; first by move=> [h1 h2]; split=> // j _; exact: h1.
  by move=> [h1 h2]; split=> // j; exact: h1 j I.
rewrite he; apply: closedI.
- apply: closed_bigI=> j _.
  have -> : [set x : E n | 0 <= x j] = (fun x : E n => (x j : R^o)) @^-1` [set t : R^o | 0 <= t] by [].
  apply: preimage_closed; last exact: closed_ge.
  by move=> x _; exact: euclidean_coordinate_continuous.
- have -> : [set x : E n | \sum_j x j <= 1] =
      (fun x : E n => (\sum_j x j : R^o)) @^-1` [set t : R^o | t <= 1] by [].
  apply: preimage_closed; last exact: closed_le.
  by move=> x _; exact: euclidean_coordinate_sum_continuous.
Qed.

(** Source for [euclidean_simplex_dilation]: Federer 2.7.16, p. 136,
    {y : y_j >= 0, sum_j y_j <= s} is the image of the standard simplex
    under multiplication by s >= 0. Supporting lemma. *)
Lemma euclidean_simplex_dilation n (s : R) : 0 <= s ->
  (euclidean_diagonal_map (fun _ : 'I_n => s) : E n -> E n) @` @euclidean_standard_simplex n =
    [set y : E n | (forall j, 0 <= y j) /\ \sum_j y j <= s].
Proof.
move=> hs; apply/seteqP; split=> y /=.
- move=> [z [hz1 hz2] <-]; rewrite /euclidean_diagonal; split.
  + by move=> j; rewrite ffunE mulr_ge0.
  + under eq_bigr do rewrite ffunE; rewrite -mulr_sumr.
    by rewrite -[X in _ <= X]mulr1 ler_wpM2l.
- move=> [hy1 hy2]; case: (eqVneq s 0)=> [h0|hs0].
  + exists 0; first by split=> [j|]; rewrite ?ffunE ?big1 ?ler01 // => j _; rewrite ffunE.
    have hz : forall j, y j = 0.
      move=> j; apply/eqP; move: hy2; rewrite h0=> hle.
      have hsum : \sum_j y j = 0 by apply/eqP; rewrite eq_le hle sumr_ge0 // => i _; exact: hy1.
      move: hsum=> /eqP; rewrite psumr_eq0; last by move=> i _; exact: hy1.
      by move=> /allP /(_ j (mem_index_enum _)) h; exact: h.
    by apply/ffunP=> j; rewrite /euclidean_diagonal !ffunE hz h0 mul0r.
  + have hp : 0 < s by rewrite lt_def hs0 hs.
    exists [ffun j => s^-1 * y j].
    * split; first by move=> j; rewrite ffunE mulr_ge0 ?invr_ge0.
      under eq_bigr do rewrite ffunE; rewrite -mulr_sumr.
      by rewrite ler_pdivrMl // mulr1.
    * by apply/ffunP=> j; rewrite /euclidean_diagonal !ffunE mulrA mulfV ?mul1r.
Qed.

(** Source for [euclidean_simplex_dilation_measure]: Federer 2.7.16,
    p. 136, L^n{y : y_j >= 0, sum_j y_j <= s} = s^n L^n(S) for s >= 0,
    since multiplication by s has determinant s^n. Supporting lemma. *)
Lemma euclidean_simplex_dilation_measure n (s : R) : 0 <= s ->
  Leb n [set y : E n | (forall j, 0 <= y j) /\ \sum_j y j <= s] =
    ((s ^+ n)%:E * Leb n (@euclidean_standard_simplex n))%E.
Proof.
move=> hs; rewrite -(euclidean_simplex_dilation n hs) euclidean_lebesgue_linear_image.
by rewrite euclidean_diagonal_det prodr_const card_ord ger0_norm ?exprn_ge0.
Qed.

(** Source for [euclidean_simplex_section]: Federer 2.7.16, p. 136, the
    section of the standard simplex of R^(m+1) at the first coordinate t
    is {y : y_j >= 0, sum_j y_j <= 1 - t} for 0 <= t, and empty
    otherwise. Supporting lemma. *)
Lemma euclidean_simplex_section m (t : R) :
  product_horizontal_section ((@euclidean_join R m) @^-1` @euclidean_standard_simplex m.+1) t =
    [set y : E m | 0 <= t /\ ((forall j, 0 <= y j) /\ \sum_j y j <= 1 - t)].
Proof.
apply/seteqP; split=> y; rewrite /product_horizontal_section /euclidean_standard_simplex /=.
- move=> [h1 h2]; rewrite big_ord_recl euclidean_join_head in h2.
  have ht := h1 ord0; rewrite euclidean_join_head in ht.
  split=> //; split.
  + by move=> j; have := h1 (lift ord0 j); rewrite euclidean_join_tail.
  + have h3 : \sum_(i < m) (@euclidean_join R m (y, t) : E m.+1) (lift ord0 i) = \sum_i y i.
      by apply: eq_bigr=> i _; rewrite euclidean_join_tail.
    rewrite h3 /= in h2; lra.
- move=> [ht [h1 h2]]; split.
  + move=> i; case: (unliftP ord0 i)=> [j ->|->].
    * by rewrite euclidean_join_tail.
    * by rewrite euclidean_join_head.
  + rewrite big_ord_recl euclidean_join_head.
    rewrite (eq_bigr (fun j => y j)) /=; last by move=> j _; rewrite euclidean_join_tail.
    lra.
Qed.

(** Source for [euclidean_standard_simplex_measure]: Federer 2.7.16,
    p. 136, "using 2.6.2, 2.9.20 one inductively computes
    L^n(S) = int_0^1 L^{n-1}{y : y_j >= 0, sum_j y_j <= 1 - t} dL^1 t
    = int_0^1 (1-t)^{n-1}/(n-1)! dL^1 t = 1/n!". Direct formalisation,
    including the cases n = 0 and n = 1. *)
Theorem euclidean_standard_simplex_measure n :
  Leb n (@euclidean_standard_simplex n) = (n`!%:R^-1)%:E.
Proof.
elim: n=> [|n ih].
  rewrite /= point_mass_in /= ?invr1 // ; split=> [j|]; [by case: j | by rewrite big_ord0 ler01].
case: n ih=> [|k] ih.
  have he : @euclidean_standard_simplex 1 = [set x : E 1 | forall i, 0 <= x i <= 1].
    apply/seteqP; split=> x /=.
    - by move=> [h1 h2] i; rewrite (ord1 i) h1 /=; rewrite big_ord1 in h2.
    - move=> h; split; first by move=> j; have /andP[] := h j.
      by rewrite big_ord1; have /andP[] := h ord0.
  rewrite he (@euclidean_closed_box R 1 (fun _ => 0) (fun _ => 1)); last by move=> i; exact: ler01.
  by rewrite big_ord1 subr0 /= invr1.
pose T := @euclidean_standard_simplex k.+2.
pose S := (@euclidean_join R k.+1) @^-1` T.
pose hm := positive_euclidean_lebesgue_is_measure R k.
pose hb := lebesgue_scalar_is_measure R.
have hSv : product_measure hm hb S = Leb k.+2 T.
  by rewrite /= positive_euclidean_lebesgue_successor /measure_pushforward.
have hTm : measure_measurable (Leb k.+2) T.
  apply: euclidean_borel_measurable; apply: closed_borel_set.
  exact: euclidean_standard_simplex_closed.
have hSm : measure_measurable (product_measure hm hb) S.
  have hp := positive_euclidean_lebesgue_split_product R k.
  rewrite -hp; apply: pushforward_measurable_from_preimage.
  have he : (@euclidean_split R k.+1) @^-1` S = T.
    by apply/seteqP; split=> x; rewrite /S /= euclidean_splitK.
  by rewrite he; exact: hTm.
have hSc : measure_countably_measurable (product_measure hm hb) S.
  apply: (measurable_subset_countably_measurable (product_measure_is_measure hm hb) hSm (subsetT S)).
  apply: product_whole_countably_measurable.
  - exact: (euclidean_lebesgue_countably_measurable R k.+1).
  - exact: lebesgue_scalar_countably_measurable.
have [_ [_ [_ hint]]] := product_set_fubini hSc.
rewrite hSv in hint.
pose c : R := (k.+1)`!%:R^-1.
pose g t : R := if 0 <= t <= 1 then c * (1 - t) ^+ k.+1 else 0.
have hfun : (fun y : R => positive_euclidean_lebesgue_measure k (product_horizontal_section S y)) =
    (fun t => (g t)%:E).
  apply: funext=> t; rewrite /S /T euclidean_simplex_section /g.
  case: ifP=> /andP ht.
  - have [ht0 ht1] := ht.
    have he : [set y : E k.+1 | 0 <= t /\ ((forall j, 0 <= y j) /\ \sum_j y j <= 1 - t)] =
        [set y : E k.+1 | (forall j, 0 <= y j) /\ \sum_j y j <= 1 - t].
      by apply/seteqP; split=> y /=; [move=> [_ h]|move=> h; split].
    change (Leb k.+1 [set y : E k.+1 | 0 <= t /\ ((forall j, 0 <= y j) /\ \sum_j y j <= 1 - t)] =
      (c * (1 - t) ^+ k.+1)%:E).
    rewrite he euclidean_simplex_dilation_measure ?subr_ge0 // ih -EFinM.
    by rewrite mulrC.
  - have he : [set y : E k.+1 | 0 <= t /\ ((forall j, 0 <= y j) /\ \sum_j y j <= 1 - t)] = set0.
      apply/seteqP; split=> y //= [h0 [h1 h2]]; apply: ht; split=> //.
      have : 0 <= \sum_j y j by apply: sumr_ge0=> j _; exact: h1.
      lra.
    change (Leb k.+1 [set y : E k.+1 | 0 <= t /\ ((forall j, 0 <= y j) /\ \sum_j y j <= 1 - t)] = 0%:E).
    by rewrite he measure_empty //; exact: euclidean_lebesgue_is_measure.
rewrite hfun in hint.
have hpi := complement_power_segment_integral R k.+1.
have hpt : is_measure_integral L1 (real_total_integrand (fun t => if 0 <= t <= 1 then (1 - t) ^+ k.+1 else 0))
    (k.+2%:R^-1)%:E.
  apply: (measure_integral_graph_equivalent _ hpi)=> t z.
  rewrite partial_function_zero_extension_graph real_total_integrand_graph /= in_itv /=.
  rewrite ?real_total_integrand_graph.
  case: ifP=> h; split.
  - by move=> [[_ <-]|[hn _]]; [exists ((1 - t) ^+ k.+1)|].
  - by move=> [y [<- <-]]; left.
  - by move=> [[hn _]|[_ ->]]; [|exists 0].
  - by move=> [y [<- <-]]; right.
have hps := real_total_integral_scale (lebesgue_scalar_is_measure R) c hpt.
have hg : is_measure_integral L1 (partial_function_total (fun t => (g t)%:E))
    ((c * k.+2%:R^-1)%R)%:E.
  apply: (measure_integral_graph_equivalent _ hps)=> t z.
  rewrite real_total_integrand_graph /g /=; case: ifP=> _; last by rewrite mulr0.
  by [].
have hv := measure_integral_unique hint hg.
rewrite hv /c; congr (_%:E).
by rewrite [in RHS]factS natrM invfM mulrC.
Qed.

(** Source for [euclidean_wedge_frame_norm]: |w_1 wedge ... wedge w_n|
    = |det f| for the linear map f with f(e_i) = w_i, Federer 1.3.4,
    p. 16, and 1.7.5, p. 32; supporting 2.7.16, p. 136. *)
Lemma euclidean_wedge_frame_norm n (w : 'I_n -> V n) :
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) (e_lambda w (ord_tuple n)) =
    `|euclidean_det (euclidean_frame_map w)|.
Proof.
pose F := euclidean_frame_map w.
have hw : w = (fun i => F (@coordinate_basis R n i)).
  by apply: funext=> i; rewrite /F /= euclidean_frame_basis.
have ho : orthonormal_family (@euclidean_inner_product R n) (@coordinate_basis R n).
  by move=> i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
rewrite {1}hw -exterior_map_indexed_product.
rewrite (detE (euclidean_two_nonzero R) (@coordinate_basisP R n)) exterior_norm_scale.
rewrite (orthonormal_product_unit_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) ho) mulr1.
by [].
Qed.

(** Source for [euclidean_simplex_measure]: Federer 2.7.16, p. 136,
    "If S is the convex hull of n + 1 points v_0, ..., v_n of R^n, then
    L^n(S) = |(v_1 - v_0) wedge ... wedge (v_n - v_0)|/n!". Direct
    formalisation, with the points indexed by 'I_(n+1) and v_0 the
    point of index 0. *)
Theorem euclidean_simplex_measure n (v : 'I_n.+1 -> V n) (S : set (E n)) :
  is_convex_hull [set v i | i in setT] S ->
  Leb n S = (exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (e_lambda (fun i => v (lift ord0 i) - v ord0) (ord_tuple n)) / n`!%:R)%:E.
Proof.
move=> hS.
have -> : S = convex_combinations v by exact: convex_hull_unique hS (convex_combinations_hull v).
pose w i := v (lift ord0 i) - v ord0.
pose F := euclidean_frame_map w.
have hFz (z : E n) : (F : E n -> E n) z =
    \sum_(j < n) z j *: v (lift ord0 j) - (\sum_(j < n) z j) *: v ord0.
  rewrite /F /= /euclidean_frame scaler_suml -sumrB; apply: eq_bigr=> j _.
  by rewrite /w scalerBr.
have hset : convex_combinations v =
    [set v ord0 + y | y in (F : E n -> E n) @` @euclidean_standard_simplex n].
  apply/seteqP; split=> x /=.
  - move=> [l [hl hs ->]].
    have hs' : l ord0 = 1 - \sum_(j < n) l (lift ord0 j) by rewrite -hs big_ord_recl addrK.
    pose Z : E n := [ffun j => l (lift ord0 j)].
    have hZ : \sum_(j < n) Z j = \sum_(j < n) l (lift ord0 j) by apply: eq_bigr=> j _; rewrite ffunE.
    exists (F Z); last first.
      rewrite hFz hZ big_ord_recl hs' scalerBl scale1r.
      rewrite (eq_bigr (fun j => l (lift ord0 j) *: v (lift ord0 j))); last by move=> j _; rewrite ffunE.
      by rewrite [RHS]addrC addrCA.
    exists Z=> //; split.
    + by move=> j; rewrite ffunE.
    + by rewrite hZ; have := hl ord0; rewrite hs'; lra.
  - move=> [y [z [hz1 hz2] <-] <-].
    exists (fun i => if unlift ord0 i is Some j then z j else 1 - \sum_j z j); split.
    + move=> i; case: (unliftP ord0 i)=> [j _|_] //; lra.
    + rewrite big_ord_recl unlift_none [X in _ + X](eq_bigr (fun j => z j)); last first.
        by move=> j _; rewrite liftK.
      exact: subrK.
    + rewrite big_ord_recl unlift_none [X in _ = _ + X](eq_bigr (fun j => z j *: v (lift ord0 j))); last first.
        by move=> j _; rewrite liftK.
      by rewrite hFz scalerBl scale1r [RHS]addrC addrCA.
rewrite hset euclidean_lebesgue_translation euclidean_lebesgue_linear_image.
rewrite euclidean_standard_simplex_measure -EFinM euclidean_wedge_frame_norm.
by [].
Qed.

End Simplex.
