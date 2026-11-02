(** Federer (1969), 2.7.16, pp. 134–136: the values of L^n on coordinate
    boxes, used for the normalisation "L^n{x : 0 < x_i < 1 for i = 1, ...,
    n} = 1" on p. 134 and for "f{x : 0 < x_i < 1} = {x : 0 < x_i < c_i}" on
    p. 135. By 2.6.2(2), p. 115, and the product laws of 2.6.5, pp. 119–120,
    the set {x : x_i in A_i for every i} has L^n measure prod_i L^1(A_i)
    whenever each A_i is L^1 measurable. The module also proves that compact
    subsets of R^n have finite L^n measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground FiniteCoordinates GrassmannAbbreviations
  EuclideanInnerProduct InnerMetric InnerNormedTopology MeasureUP MeasureBasic MeasureAlmostBasic MeasureSplit
  MeasurePushforward PushforwardMeasurableSets TopologicalBorel BorelRegularMeasureUP ProductMeasure
  ProductRectangleValue LebesgueScalarMeasure EuclideanOneCoordinate EuclideanCoordinateSplit
  EuclideanLebesgue EuclideanLebesgueDimensions PointMassMeasure StieltjesContinuityPoints
  IntervalBumpFunctions EuclideanAdditiveGroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Boxes.
Variable R : realType.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation L1 := (@lebesgue_scalar_measure R).
Local Notation Leb n := (@euclidean_lebesgue_measure R n).

(** Source for [euclidean_coordinate_box]: supporting definition for
    Federer 2.7.16, pp. 134–135: the set {x : x_i in A_i for every i}
    of R^n. *)
Definition euclidean_coordinate_box n (A : 'I_n -> set R) : set (E n) :=
  [set x | forall i, A i (x i)].

(** Source for [positive_coordinate_box_measure]: supporting lemma for
    Federer 2.7.16, p. 134: on R^(k+1) the set {x : x_i in A_i} is L^(k+1)
    measurable with measure prod_i L^1(A_i), by 2.6.2(2), p. 115, and the
    inductive product laws of 2.6.5, pp. 119–120. *)
Lemma positive_coordinate_box_measure k (A : 'I_k.+1 -> set R) :
  (forall i, measure_measurable L1 (A i)) ->
  measure_measurable (@positive_euclidean_lebesgue_measure R k) (euclidean_coordinate_box A) /\
  @positive_euclidean_lebesgue_measure R k (euclidean_coordinate_box A) = (\prod_(i < k.+1) L1 (A i))%E.
Proof.
elim: k A=> [|k ih] A hA.
- have hpre : (@euclidean_one_embed R) @^-1` euclidean_coordinate_box A = A ord0.
    apply/seteqP; split=> t /=.
    + by move=> h; have := h ord0; rewrite /euclidean_one_embed ffunE.
    + by move=> h i; rewrite /euclidean_one_embed ffunE (ord1 i).
  rewrite positive_euclidean_lebesgue_first big_ord1; split.
  + by apply: pushforward_measurable_from_preimage; rewrite hpre; exact: hA.
  + by rewrite /measure_pushforward hpre.
- pose A' i := A (lift ord0 i).
  have [hm' hv'] := ih A' (fun i => hA (lift ord0 i)).
  have [hr hrv] := @product_measure_measurable_rectangle R _ _ _ _
    (positive_euclidean_lebesgue_is_measure R k) (lebesgue_scalar_is_measure R)
    (euclidean_coordinate_box A') (A ord0) hm' (hA ord0).
  have hpre : (@euclidean_join R k.+1) @^-1` euclidean_coordinate_box A =
      euclidean_coordinate_box A' `*` A ord0.
    apply/seteqP; split=> -[u t] /=.
    + move=> h; split; last by have := h ord0; rewrite euclidean_join_head.
      by move=> i; have := h (lift ord0 i); rewrite euclidean_join_tail.
    + move=> [hu ht] i; case: (unliftP ord0 i)=> [j ->|->].
      * by rewrite euclidean_join_tail; exact: hu.
      * by rewrite euclidean_join_head.
  rewrite positive_euclidean_lebesgue_successor; split.
  + by apply: pushforward_measurable_from_preimage; rewrite hpre.
  + by rewrite /measure_pushforward hpre hrv hv' muleC [RHS]big_ord_recl.
Qed.

(** Source for [euclidean_coordinate_box_measure]: Federer 2.7.16,
    p. 134, "since the additive group of R^n is the direct sum of n
    factors equal to R": in every dimension the set {x : x_i in A_i} is
    L^n measurable with L^n measure prod_i L^1(A_i), whenever the A_i are
    L^1 measurable. For n = 0 both sides equal one. Supporting lemma. *)
Theorem euclidean_coordinate_box_measure n (A : 'I_n -> set R) :
  (forall i, measure_measurable L1 (A i)) ->
  measure_measurable (Leb n) (euclidean_coordinate_box A) /\
  Leb n (euclidean_coordinate_box A) = (\prod_(i < n) L1 (A i))%E.
Proof.
case: n A=> [|k] A hA; last exact: positive_coordinate_box_measure hA.
have hT : euclidean_coordinate_box A = setT.
  by apply/seteqP; split=> x // _ [].
rewrite hT big_ord0; split.
- exact: measure_measurable_whole (euclidean_lebesgue_is_measure R 0).
- exact: point_mass_in.
Qed.

(** Source for [lebesgue_scalar_open_interval]: L^1{t : a < t < b} =
    b - a whenever a <= b, Federer 2.5.17, p. 111, used in 2.7.16,
    p. 134. The segment and the open interval differ by two points of
    measure zero. Supporting lemma. *)
Lemma lebesgue_scalar_open_interval (a b : R) : a <= b -> L1 `]a, b[ = (b - a)%:E.
Proof.
move=> hab; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite -lebesgue_scalar_segment //; apply: (@measure_mono R R L1 (lebesgue_scalar_is_measure R)).
  by move=> t; rewrite /= !in_itv /= => /andP[h1 h2]; rewrite !ltW.
- rewrite -lebesgue_scalar_segment //.
  have hs : `[a, b] `<=` `]a, b[ `|` ([set a] `|` [set b]).
    move=> t; rewrite /= !in_itv /= => /andP[h1 h2].
    have [hat|hat] := eqVneq a t; first by right; left.
    have [htb|htb] := eqVneq t b; first by right; right.
    by left; rewrite !lt_neqAle hat h1 htb h2.
  apply: le_trans (@measure_mono R R L1 (lebesgue_scalar_is_measure R) _ _ hs) _.
  apply: le_trans (measure_union_le _ _ (lebesgue_scalar_is_measure R)) _.
  rewrite (measure_null_union (lebesgue_scalar_is_measure R)) ?lebesgue_scalar_singleton //.
  by rewrite adde0.
Qed.

(** Source for [lebesgue_scalar_borel_measurable]: Borel subsets of R
    are L^1 measurable, Federer 2.5.17, p. 111, and 2.2.3, p. 61.
    Supporting lemma. *)
Lemma lebesgue_scalar_borel_measurable (A : set R) : borel_set A -> measure_measurable L1 A.
Proof.
exact: borel_regular_borel_measurable (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R) A.
Qed.

(** Source for [lebesgue_scalar_open_interval_measurable]: open
    intervals are L^1 measurable, Federer 2.5.17, p. 111. Supporting
    lemma. *)
Lemma lebesgue_scalar_open_interval_measurable (a b : R) : measure_measurable L1 `]a, b[.
Proof. apply: lebesgue_scalar_borel_measurable; apply: open_borel_set; exact: interval_open. Qed.

(** Source for [lebesgue_scalar_segment_measurable]: segments are L^1
    measurable, Federer 2.5.17, p. 111. Supporting lemma. *)
Lemma lebesgue_scalar_segment_measurable (a b : R) : measure_measurable L1 `[a, b].
Proof. apply: lebesgue_scalar_borel_measurable; apply: closed_borel_set; exact: segment_closed_real. Qed.

(** Source for [euclidean_open_box]: Federer 2.7.16, pp. 134–135, L^n{x :
    a_i < x_i < b_i for i = 1, ..., n} = prod_i (b_i - a_i) whenever a_i <=
    b_i. Direct formalisation of the box values used in the text *)
Theorem euclidean_open_box n (a b : 'I_n -> R) : (forall i, a i <= b i) ->
  Leb n [set x | forall i, a i < x i < b i] = (\prod_(i < n) (b i - a i))%:E.
Proof.
move=> hab.
have [_ hv] := @euclidean_coordinate_box_measure n (fun i => `]a i, b i[)
  (fun i => lebesgue_scalar_open_interval_measurable (a i) (b i)).
transitivity (Leb n (euclidean_coordinate_box (fun i => `]a i, b i[))).
  by congr (Leb n _); apply/seteqP; split=> x /= h i; have := h i; rewrite /= in_itv.
rewrite hv -prodEFin; apply: eq_bigr=> i _; exact: lebesgue_scalar_open_interval.
Qed.

(** Source for [euclidean_closed_box]: Federer 2.7.16, p. 136, the
    rectangular box {x : 0 <= (x - a) . e_i <= c_i} in the standard
    base: L^n{x : a_i <= x_i <= b_i for i = 1, ..., n} = prod_i (b_i - a_i)
    whenever a_i <= b_i. Supporting lemma. *)
Theorem euclidean_closed_box n (a b : 'I_n -> R) : (forall i, a i <= b i) ->
  Leb n [set x | forall i, a i <= x i <= b i] = (\prod_(i < n) (b i - a i))%:E.
Proof.
move=> hab.
have [_ hv] := @euclidean_coordinate_box_measure n (fun i => `[a i, b i])
  (fun i => lebesgue_scalar_segment_measurable (a i) (b i)).
transitivity (Leb n (euclidean_coordinate_box (fun i => `[a i, b i]))).
  by congr (Leb n _); apply/seteqP; split=> x /= h i; have := h i; rewrite /= in_itv.
rewrite hv -prodEFin; apply: eq_bigr=> i _; exact: lebesgue_scalar_segment.
Qed.

(** Source for [euclidean_unit_cube]: Federer 2.7.16, p. 134,
    "L^n{x : 0 < x_i < 1 for i = 1, ..., n} = 1". Direct
    formalisation; for n = 0 the set is the whole one-point space. *)
Theorem euclidean_unit_cube n : Leb n [set x | forall i, 0 < x i < 1] = 1%:E.
Proof.
rewrite (@euclidean_open_box n (fun _ => 0) (fun _ => 1)); last by move=> i; exact: ler01.
by congr (_%:E); rewrite big1 // => i _; rewrite subr0.
Qed.

(** Source for [euclidean_borel_measurable]: Borel subsets of R^n are
    L^n measurable, Federer 2.6.5, p. 120, and 2.2.3, p. 61; used
    throughout 2.7.16, pp. 134–136. Supporting lemma. *)
Lemma euclidean_borel_measurable n (A : set (E n)) : borel_set A -> measure_measurable (Leb n) A.
Proof.
exact: borel_regular_borel_measurable (euclidean_lebesgue_is_measure R n)
  (euclidean_lebesgue_borel_regular R n) A.
Qed.

(** Source for [euclidean_compact_finite]: compact subsets of R^n have
    finite L^n measure, as required of the Haar measures in Federer
    2.7.16, p. 134 (2.7.2, p. 122, with 2.5.13, p. 106). A compact set
    lies in a closed coordinate box, whose measure is finite. Supporting
    lemma. *)
Lemma euclidean_compact_finite n (K : set (E n)) : compact K -> (Leb n K < +oo)%E.
Proof.
move=> hK; have [r [hr hb]] := euclidean_compact_coordinate_bound hK.
have hsub : K `<=` [set x | forall i, - r <= x i <= r].
  by move=> x hx i; rewrite -ler_norml; exact: hb x hx i.
apply: le_lt_trans (measure_mono (euclidean_lebesgue_is_measure R n) hsub) _.
rewrite euclidean_closed_box; first exact: ltry.
by move=> i; lra.
Qed.

End Boxes.
