(** Federer (1969), 2.7.16, p. 135: "We define alpha(n) = L^n{x : |x| < 1}
    and observe that, whenever a in R^n and r > 0, alpha(n) r^n = L^n{x : |x
    - a| < r} because L^n is invariant under translation by a, and
    multiplication by r has determinant r^n. Moreover alpha(1) = 2, and for
    n >= 2 Fubini's Theorem yields the recursion formula alpha(n) =
    int_{-1}^{1} L^{n-1}{y : |y| < (1 - t^2)^{1/2}} dL^1 t = alpha(n-1)
    int_{-1}^{1} (1 - t^2)^{(n-1)/2} dL^1 t. We also define alpha(0) = 1."
    The book prints the exponent (n-2)/2; Federer's erratum, page 3,
    corrects book p. 135 line 35 to (1 - t^2)^{(n-1)/2}, which is the
    formula proved below. The power (1 - t^2)^{(n-1)/2} is written ((1 -
    t^2)^{1/2})^{n-1} with the real square root. With the convention of
    2.6.5 that L^0 is the unit mass at the sole point of R^0, the value
    alpha(0) = 1 is a consequence of the definition. The recursion uses
    2.6.2(3), p. 115, for L^n = L^{n-1} x L^1 (2.6.5, p. 119), and the
    sections {y : |y|^2 + t^2 < 1}. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology FiniteCoordinates
  GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  TopologicalBorel MeasureUP MeasureBasic MeasurePushforward PushforwardMeasurableSets MeasureSplit
  CountablyMeasurableUP CountablyMeasurableSubsets CountablyMeasurableProduct PartialFunctionBasic
  MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP SummableRealArithmetic
  ProductMeasure ProductSections ProductSetFubini PointMassMeasure LebesgueScalarMeasure
  EuclideanCoordinateSplit EuclideanLebesgue EuclideanLebesgueDimensions EuclideanAdditiveGroup
  EuclideanLebesgueTranslation EuclideanLebesgueBoxes EuclideanLinearMaps EuclideanLebesgueLinear
  EuclideanLebesgueDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section BallVolume.
Variable R : realType.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Leb n := (@euclidean_lebesgue_measure R n).
Local Notation L1 := (@lebesgue_scalar_measure R).

(** Source for [euclidean_unit_ball_volume]: Federer 2.7.16, p. 135,
    "We define alpha(n) = L^n{x : |x| < 1}". Direct definition of the
    real number alpha(n); [euclidean_unit_ball_volumeE] shows that the
    measure is finite and equals alpha(n). *)
Definition euclidean_unit_ball_volume (n : nat) : R := fine (Leb n [set x : E n | `|x| < 1]).

(** Source for [euclidean_unit_ball_volumeE]: Federer 2.7.16, p. 135,
    alpha(n) = L^n{x : |x| < 1}, with 0 < alpha(n) < oo. Supporting
    lemma. *)
Lemma euclidean_unit_ball_volumeE n :
  Leb n [set x : E n | `|x| < 1] = (euclidean_unit_ball_volume n)%:E /\ 0 < euclidean_unit_ball_volume n.
Proof.
have [hpos hfin] := @euclidean_unit_ball_bounds R n.
have hf : Leb n [set x : E n | `|x| < 1] \is a fin_num.
  by rewrite ge0_fin_numE // ltW.
split; first by rewrite /euclidean_unit_ball_volume fineK.
by rewrite /euclidean_unit_ball_volume -lte_fin fineK.
Qed.

(** Source for [euclidean_ball_measure]: Federer 2.7.16, p. 135,
    "whenever a in R^n and r > 0, alpha(n) r^n = L^n{x : |x - a| < r}
    because L^n is invariant under translation by a, and multiplication
    by r has determinant r^n". Direct formalisation. *)
Theorem euclidean_ball_measure n (a : E n) (r : R) : 0 < r ->
  Leb n [set x : E n | `|x - a| < r] = (euclidean_unit_ball_volume n * r ^+ n)%:E.
Proof.
move=> hr.
pose m := euclidean_diagonal_map (fun _ : 'I_n => r).
have hm (x : E n) : (m : E n -> E n) x = r *: x.
  by apply/ffunP=> i; rewrite /m /= /euclidean_diagonal !ffunE.
have hdet : euclidean_det m = r ^+ n.
  by rewrite /m euclidean_diagonal_det prodr_const card_ord.
have himg : (m : E n -> E n) @` [set x : E n | `|x| < 1] = [set y : E n | `|y| < r].
  apply/seteqP; split=> y /=.
  - by move=> [x hx <-]; rewrite hm normrZ gtr0_norm // -{2}(mulr1 r) ltr_pM2l.
  - move=> hy; exists (r^-1 *: y); last by rewrite hm scalerA mulfV ?scale1r //; exact: lt0r_neq0.
    rewrite /= normrZ gtr0_norm ?invr_gt0 // mulrC ltr_pdivrMr // mul1r; exact: hy.
have htr : [set x : E n | `|x - a| < r] = [set a + y | y in [set y : E n | `|y| < r]].
  apply/seteqP; split=> x /=.
  - by move=> hx; exists (x - a)=> //; rewrite addrC subrK.
  - by move=> [y hy <-]; rewrite addrC addKr.
rewrite htr euclidean_lebesgue_translation -himg euclidean_lebesgue_linear_image hdet.
rewrite (euclidean_unit_ball_volumeE n).1 -EFinM ger0_norm ?exprn_ge0 ?ltW //.
by rewrite mulrC.
Qed.

(** Source for [euclidean_unit_ball_volume0]: Federer 2.7.16, p. 135,
    "We also define alpha(0) = 1": with L^0 the unit mass of 2.6.5, the
    definition alpha(0) = L^0{x : |x| < 1} already gives 1. Direct
    formalisation. *)
Theorem euclidean_unit_ball_volume0 : euclidean_unit_ball_volume 0 = 1.
Proof.
rewrite /euclidean_unit_ball_volume /euclidean_lebesgue_measure point_mass_in //=.
by rewrite normr0 ltr01.
Qed.

(** Source for [euclidean_norm_one]: on R^1 the Euclidean norm is the
    absolute value of the coordinate, Federer 1.7.1, p. 28; supporting
    alpha(1) = 2 in 2.7.16, p. 135. *)
Lemma euclidean_norm_one (x : E 1) : `|x| = `|x ord0|.
Proof.
rewrite inner_norm_topologyE; apply: inner_norm_value; first exact: normr_ge0.
by rewrite real_normK ?num_real // /euclidean_inner_product big_ord1 expr2.
Qed.

(** Source for [euclidean_unit_ball_volume1]: Federer 2.7.16, p. 135,
    "Moreover alpha(1) = 2". Direct formalisation. *)
Theorem euclidean_unit_ball_volume1 : euclidean_unit_ball_volume 1 = 2.
Proof.
have he : [set x : E 1 | `|x| < 1] = [set x : E 1 | forall i, -1 < x i < 1].
  apply/seteqP; split=> x /=.
  - by move=> hx i; rewrite (ord1 i) -ltr_norml -euclidean_norm_one.
  - by move=> hx; rewrite euclidean_norm_one ltr_norml; exact: hx ord0.
have h := (euclidean_unit_ball_volumeE 1).1.
rewrite he (@euclidean_open_box R 1 (fun _ => -1) (fun _ => 1)) in h; last by move=> i; lra.
rewrite big_ord1 in h; move: h=> /eqP; rewrite eqe eq_sym=> /eqP ->; lra.
Qed.

(** Source for [euclidean_join_norm]: |(y, t)|^2 = |y|^2 + t^2 for the
    splitting R^(m+1) = R^m x R of 2.6.5, p. 119; supporting the sections
    in the recursion of Federer 2.7.16, p. 135. *)
Lemma euclidean_join_norm m (y : E m) (t : R) :
  `|(@euclidean_join R m (y, t) : E m.+1)| ^+ 2 = `|y| ^+ 2 + t ^+ 2.
Proof.
rewrite !inner_norm_topologyE !inner_norm_sqr /euclidean_inner_product big_ord_recl.
rewrite euclidean_join_head addrC expr2; congr (_ + _).
by apply: eq_bigr=> i _; rewrite euclidean_join_tail.
Qed.

(** Source for [euclidean_ball_section]: Federer 2.7.16, p. 135, the
    section of the unit ball of R^(m+1) at height t is
    {y : |y| < (1 - t^2)^{1/2}}. Supporting lemma. *)
Lemma euclidean_ball_section m (t : R) :
  product_horizontal_section ((@euclidean_join R m) @^-1` [set x : E m.+1 | `|x| < 1]) t =
    [set y : E m | `|y| < Num.sqrt (1 - t ^+ 2)].
Proof.
apply/seteqP; split=> y; rewrite /product_horizontal_section /=.
- move=> h.
  have h2 : `|(@euclidean_join R m (y, t) : E m.+1)| ^+ 2 < 1.
    by rewrite -(expr1n _ 2) ltr_sqr ?nnegrE ?normr_ge0 ?ler01.
  rewrite euclidean_join_norm in h2.
  have hs : 0 < 1 - t ^+ 2 by have := sqr_ge0 (`|y|); lra.
  by rewrite -ltr_sqr ?nnegrE ?normr_ge0 ?sqrtr_ge0 // sqr_sqrtr ?ltW //; lra.
- move=> h.
  have hs : 0 < Num.sqrt (1 - t ^+ 2) := le_lt_trans (normr_ge0 y) h.
  rewrite sqrtr_gt0 in hs.
  have h2 : `|y| ^+ 2 < 1 - t ^+ 2.
    by rewrite -[X in _ < X](sqr_sqrtr (ltW hs)) ltr_sqr ?nnegrE ?normr_ge0 ?sqrtr_ge0.
  rewrite -ltr_sqr ?nnegrE ?normr_ge0 ?ler01 // expr1n euclidean_join_norm; lra.
Qed.

(** Source for [euclidean_ball_section_measure]: Federer 2.7.16, p. 135,
    L^m{y : |y| < (1 - t^2)^{1/2}} = alpha(m) ((1 - t^2)^{1/2})^m for
    |t| < 1, and 0 otherwise. Supporting lemma. *)
Lemma euclidean_ball_section_measure m (t : R) :
  Leb m [set y : E m | `|y| < Num.sqrt (1 - t ^+ 2)] =
    (if `|t| < 1 then euclidean_unit_ball_volume m * Num.sqrt (1 - t ^+ 2) ^+ m else 0)%:E.
Proof.
case: ifP=> ht.
- have hs : 0 < Num.sqrt (1 - t ^+ 2).
    rewrite sqrtr_gt0 subr_gt0 -(expr1n _ 2) -real_normK ?num_real //.
    by rewrite ltr_sqr ?nnegrE ?normr_ge0 ?ler01.
  have he : [set y : E m | `|y| < Num.sqrt (1 - t ^+ 2)] = [set y : E m | `|y - 0| < Num.sqrt (1 - t ^+ 2)].
    by apply/seteqP; split=> y; rewrite /= subr0.
  by rewrite he euclidean_ball_measure.
- have he : [set y : E m | `|y| < Num.sqrt (1 - t ^+ 2)] = set0.
    apply/seteqP; split=> y //= hy.
    have hs : 0 < Num.sqrt (1 - t ^+ 2) := le_lt_trans (normr_ge0 y) hy.
    move: hs; rewrite sqrtr_gt0 subr_gt0 -(expr1n _ 2) -real_normK ?num_real //.
    by rewrite ltr_sqr ?nnegrE ?normr_ge0 ?ler01 // ht.
  by rewrite he measure_empty //; exact: euclidean_lebesgue_is_measure.
Qed.

(** Source for [euclidean_ball_recursion_sections]: Federer 2.7.16,
    p. 135, first line of the recursion: for n = m + 1 >= 2,
    alpha(n) = int L^{n-1}{y : |y| < (1 - t^2)^{1/2}} dL^1 t, by Fubini's
    Theorem 2.6.2(3), p. 115. The integrand vanishes for |t| >= 1, so
    the integral over R is Federer's int_{-1}^{1}. Direct formalisation. *)
Theorem euclidean_ball_recursion_sections m : (1 <= m)%N ->
  is_measure_integral L1
    (partial_function_total (fun t : R =>
      (Leb m [set y : E m | `|y| < Num.sqrt (1 - t ^+ 2)] : extended_real_line R)))
    (euclidean_unit_ball_volume m.+1)%:E.
Proof.
case: m=> [//|k] _.
pose B := [set x : E k.+2 | `|x| < 1].
pose S := (@euclidean_join R k.+1) @^-1` B.
pose hm := positive_euclidean_lebesgue_is_measure R k.
pose hb := lebesgue_scalar_is_measure R.
have hSv : product_measure hm hb S = Leb k.+2 B.
  rewrite /= positive_euclidean_lebesgue_successor /measure_pushforward.
  by congr (product_measure _ _ _).
have hBm : measure_measurable (Leb k.+2) B.
  apply: euclidean_borel_measurable; apply: open_borel_set.
  have he : B = ball (0 : E k.+2) 1.
    by apply/seteqP; split=> x; rewrite /B -ball_normE /= sub0r normrN.
  rewrite he; exact: ball_open.
have hSm : measure_measurable (product_measure hm hb) S.
  have hp := positive_euclidean_lebesgue_split_product R k.
  rewrite -hp; apply: pushforward_measurable_from_preimage.
  have he : (@euclidean_split R k.+1) @^-1` S = B.
    by apply/seteqP; split=> x; rewrite /S /= euclidean_splitK.
  by rewrite he; exact: hBm.
have hSc : measure_countably_measurable (product_measure hm hb) S.
  apply: (measurable_subset_countably_measurable (product_measure_is_measure hm hb) hSm (subsetT S)).
  apply: product_whole_countably_measurable.
  - exact: (euclidean_lebesgue_countably_measurable R k.+1).
  - exact: lebesgue_scalar_countably_measurable.
have [_ [_ [_ hint]]] := product_set_fubini hSc.
rewrite hSv (euclidean_unit_ball_volumeE k.+2).1 in hint.
apply: (measure_integral_graph_equivalent _ hint)=> t z.
have he : (fun y : R => positive_euclidean_lebesgue_measure k (product_horizontal_section S y)) =
    (fun t0 : R => Leb k.+1 [set y : E k.+1 | `|y| < Num.sqrt (1 - t0 ^+ 2)]).
  by apply: funext=> y; rewrite /S /B euclidean_ball_section.
by rewrite he.
Qed.

(** Source for [euclidean_ball_recursion]: Federer 2.7.16, p. 135, as
    corrected by the erratum, page 3, book p. 135 line 35: for n >= 2,
    alpha(n) = alpha(n-1) int_{-1}^{1} (1 - t^2)^{(n-1)/2} dL^1 t. Direct
    formalisation; the integrand is ((1 - t^2)^{1/2})^{n-1} on
    {t : |t| < 1} and 0 elsewhere. *)
Theorem euclidean_ball_recursion n : (2 <= n)%N ->
  exists c : R,
    is_measure_integral L1
      (real_total_integrand (fun t : R => if `|t| < 1 then Num.sqrt (1 - t ^+ 2) ^+ n.-1 else 0)) c%:E /\
    euclidean_unit_ball_volume n = euclidean_unit_ball_volume n.-1 * c.
Proof.
case: n=> [//|m] hm; rewrite /= in hm *.
have h := euclidean_ball_recursion_sections hm.
have [_ hpos] := euclidean_unit_ball_volumeE m.
pose g t := if `|t| < 1 then euclidean_unit_ball_volume m * Num.sqrt (1 - t ^+ 2) ^+ m else 0.
have hfun : (fun t : R => Leb m [set y : E m | `|y| < Num.sqrt (1 - t ^+ 2)]) = (fun t => (g t)%:E).
  by apply: funext=> t; rewrite euclidean_ball_section_measure.
rewrite hfun in h.
have hg : is_measure_integral L1 (real_total_integrand g) (euclidean_unit_ball_volume m.+1)%:E.
  apply: (measure_integral_graph_equivalent _ h)=> t z.
  by rewrite real_total_integrand_graph; split=> hz; exact: hz.
exists ((euclidean_unit_ball_volume m)^-1 * euclidean_unit_ball_volume m.+1); split.
- have hs := real_total_integral_scale (lebesgue_scalar_is_measure R) ((euclidean_unit_ball_volume m)^-1) hg.
  have hfun2 : (fun t => (euclidean_unit_ball_volume m)^-1 * g t) =
      (fun t => if `|t| < 1 then Num.sqrt (1 - t ^+ 2) ^+ m else 0).
    apply: funext=> t; rewrite /g; case: ifP=> _; last by rewrite mulr0.
    by rewrite mulrA mulVf ?mul1r //; exact: lt0r_neq0.
  by rewrite hfun2 in hs.
- by rewrite mulrA mulfV ?mul1r //; exact: lt0r_neq0.
Qed.

End BallVolume.
