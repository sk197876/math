(** Federer (1969), 2.7.16, pp. 134–135: L^1 and L^n are invariant under the
    translations tau_z(v) = z + v; "since the additive group of R^n is the
    direct sum of n factors equal to R", and L^n is the n-fold product of
    L^1 by 2.6.5, pp. 119–120. Translation invariance of L^1 follows from
    the characterisation of 2.5.17, p. 111: the image of L^1 under t |-> c +
    t is Borel regular and gives every segment its length. A map acting
    coordinatewise by measure bijections of L^1 is then a measure bijection
    of L^n, by induction over the product laws of 2.6.5 and the bijection
    invariance of products (2.6.1, p. 115). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric InnerNormedTopology MeasureUP MeasurePushforward BorelRegularMeasureUP
  MeasureCoordinateTransport ProductMeasure ProductMeasureBijections MeasureBijectionUP
  MeasureBijectionLaws LebesgueLineUP LebesgueScalarMeasure EuclideanOneCoordinate
  EuclideanCoordinateSplit EuclideanLebesgue EuclideanLebesgueBijections
  EuclideanLebesgueDimensions PointMassMeasure EuclideanAdditiveGroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Translation.
Variable R : realType.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation L1 := (@lebesgue_scalar_measure R).

(** Source for [measure_bijection_ext]: supporting lemma for Federer
    2.7.16, p. 135: the measure bijection laws of 2.6.5, pp. 119–120,
    depend only on the values of the two maps. *)
Lemma measure_bijection_ext (X Y : choiceType) (mu : set X -> \bar R) (nu : set Y -> \bar R)
    (f f' : X -> Y) (g g' : Y -> X) :
  is_measure_bijection mu nu f g -> f =1 f' -> g =1 g' -> is_measure_bijection mu nu f' g'.
Proof.
move=> [hf hg he] hff hgg; constructor.
- by move=> x; rewrite -hff -hgg hf.
- by move=> y; rewrite -hff -hgg hg.
- rewrite -he; apply: funext=> B; rewrite /measure_pushforward.
  by congr (mu _); apply/seteqP; split=> x /=; rewrite hff.
Qed.

(** Source for [scalar_translation_continuous]: continuity of
    t |-> c + t on R, supporting the translation invariance of L^1 in
    Federer 2.7.16, p. 134. *)
Lemma scalar_translation_continuous (c : R) : continuous (fun t : R => c + t).
Proof.
move=> t; apply: (@continuousD R R^o R^o (fun _ => c) (fun s => s) t).
- exact: cst_continuous.
- exact: cvg_id.
Qed.

(** Source for [lebesgue_scalar_translation]: Federer 2.7.16, p. 134,
    "L^1 is the ... Haar measure of the additive group of R": L^1 is
    invariant under t |-> c + t. Proved from the characterisation of
    L^1 in 2.5.17, p. 111, as a measure bijection with inverse
    t |-> -c + t. Supporting lemma. *)
Lemma lebesgue_scalar_translation (c : R) :
  is_measure_bijection L1 L1 (fun t => c + t) (fun t => - c + t).
Proof.
constructor; [by move=> t; rewrite addKr | by move=> t; rewrite addNKr |].
apply: lebesgue_line_unique (lebesgue_scalar_specification R).
constructor.
- exact: measure_pushforward_is_measure (lebesgue_scalar_is_measure R).
- apply: (@homeomorphic_pushforward_borel_regular R R R L1 (lebesgue_scalar_is_measure R)
    (fun t => c + t) (fun t => - c + t)).
  + by move=> t; rewrite addKr.
  + by move=> t; rewrite addNKr.
  + exact: scalar_translation_continuous.
  + exact: scalar_translation_continuous.
  + exact: lebesgue_scalar_borel_regular.
- move=> a b hab; rewrite /measure_pushforward.
  have he : (fun t => c + t) @^-1` `[a, b] = `[a - c, b - c].
    apply/seteqP; split=> t; rewrite /= !in_itv /=.
    + by move=> /andP[h1 h2]; rewrite lerBlDl h1 lerBrDl h2.
    + by move=> /andP[h1 h2]; rewrite -lerBlDl h1 -lerBrDl h2.
  rewrite he lebesgue_scalar_segment; last by rewrite lerD2r.
  by congr (_%:E); rewrite opprB addrA subrK.
Qed.

(** Source for [euclidean_coordinatewise_map]: supporting definition
    for Federer 2.7.16, p. 134, "the additive group of R^n is the direct
    sum of n factors equal to R": the map x |-> (f_1(x_1), ..., f_n(x_n))
    of R^n. *)
Definition euclidean_coordinatewise_map n (f : 'I_n -> R -> R) (x : E n) : E n :=
  [ffun i => f i (x i)].

(** Source for [positive_coordinatewise_bijection]: supporting lemma
    for Federer 2.7.16, p. 134: on R^(k+1), a map acting on each
    coordinate by a measure bijection of L^1 is a measure bijection of
    the product L^(k+1), by induction over the laws of 2.6.5,
    pp. 119–120. *)
Lemma positive_coordinatewise_bijection k (f g : 'I_k.+1 -> R -> R) :
  (forall i, is_measure_bijection L1 L1 (f i) (g i)) ->
  is_measure_bijection (@positive_euclidean_lebesgue_measure R k)
    (@positive_euclidean_lebesgue_measure R k)
    (euclidean_coordinatewise_map f) (euclidean_coordinatewise_map g).
Proof.
elim: k f g=> [|k ih] f g hfg.
- have h1 := positive_euclidean_line_bijection R.
  have h2 := measure_bijection_compose (measure_bijection_compose h1 (hfg ord0))
    (measure_bijection_inverse h1).
  apply: (measure_bijection_ext h2)=> x; apply/ffunP=> i;
    rewrite /euclidean_coordinatewise_map /euclidean_one_embed /euclidean_one_project !ffunE;
    by rewrite (ord1 i).
- have hs := positive_euclidean_split_bijection R k.
  pose f' i := f (lift ord0 i); pose g' i := g (lift ord0 i).
  have hp := @measure_bijection_product R _ _ _ _ _ _ _ _
    (positive_euclidean_lebesgue_is_measure R k) (lebesgue_scalar_is_measure R)
    (positive_euclidean_lebesgue_is_measure R k) (lebesgue_scalar_is_measure R)
    _ _ _ _ (ih f' g' (fun i => hfg (lift ord0 i))) (hfg ord0).
  have h2 := measure_bijection_compose (measure_bijection_compose hs hp) (measure_bijection_inverse hs).
  apply: (measure_bijection_ext h2)=> x; apply/ffunP=> i;
    case: (unliftP ord0 i)=> [j ->|->];
    rewrite ?euclidean_join_tail ?euclidean_join_head /cartesian_map /= /euclidean_coordinatewise_map
      !ffunE //.
Qed.

(** Source for [euclidean_coordinatewise_bijection]: supporting lemma
    for Federer 2.7.16, p. 134, in every dimension: a coordinatewise
    measure bijection of the factors L^1 is a measure bijection of L^n.
    For n = 0 the map is the identity of the one-point space. *)
Lemma euclidean_coordinatewise_bijection n (f g : 'I_n -> R -> R) :
  (forall i, is_measure_bijection L1 L1 (f i) (g i)) ->
  is_measure_bijection (@euclidean_lebesgue_measure R n) (@euclidean_lebesgue_measure R n)
    (euclidean_coordinatewise_map f) (euclidean_coordinatewise_map g).
Proof.
case: n f g=> [|k] f g hfg; last exact: positive_coordinatewise_bijection hfg.
have hid (x : E 0) (h : 'I_0 -> R -> R) : euclidean_coordinatewise_map h x = x.
  by rewrite (coordinate_zero x) (coordinate_zero (euclidean_coordinatewise_map h 0)).
apply: (measure_bijection_ext (measure_bijection_identity (@euclidean_lebesgue_measure R 0)));
  by move=> x; rewrite hid.
Qed.

(** Source for [euclidean_lebesgue_translation_bijection]: Federer
    2.7.16, pp. 134–135, the translation invariance of L^n under
    tau_z(v) = z + v, stated as a measure bijection with inverse
    tau_(-z). Supporting lemma. *)
Lemma euclidean_lebesgue_translation_bijection n (z : E n) :
  is_measure_bijection (@euclidean_lebesgue_measure R n) (@euclidean_lebesgue_measure R n)
    (euclidean_translation z) (euclidean_translation (- z)).
Proof.
have h := @euclidean_coordinatewise_bijection n (fun i t => z i + t) (fun i t => - z i + t)
  (fun i => lebesgue_scalar_translation (z i)).
apply: (measure_bijection_ext h)=> x; apply/ffunP=> i;
  by rewrite /euclidean_coordinatewise_map /euclidean_translation !ffunE.
Qed.

(** Source for [euclidean_lebesgue_translation_pushforward]: Federer
    2.7.16, p. 135, "L^n is invariant under translation by a": the image
    of L^n under tau_z is L^n. Direct formalisation. *)
Theorem euclidean_lebesgue_translation_pushforward n (z : E n) :
  measure_pushforward (euclidean_translation z) (@euclidean_lebesgue_measure R n) =
    @euclidean_lebesgue_measure R n.
Proof. exact: measure_bijection_pushforward (euclidean_lebesgue_translation_bijection z). Qed.

(** Source for [euclidean_lebesgue_translation]: Federer 2.7.16, p. 135,
    L^n[z + T] = L^n(T) whenever z in R^n and T is a subset of R^n.
    Direct formalisation. *)
Theorem euclidean_lebesgue_translation n (z : E n) (T : set (E n)) :
  @euclidean_lebesgue_measure R n [set z + x | x in T] = @euclidean_lebesgue_measure R n T.
Proof.
have h := congr1 (fun mu => mu T) (euclidean_lebesgue_translation_pushforward (- z)).
rewrite /= /measure_pushforward in h; rewrite -h.
congr (euclidean_lebesgue_measure _ _); apply/seteqP; split=> y.
- by move=> [x hx <-]; rewrite /euclidean_translation /= addKr.
- by move=> hy; exists (- z + y)=> //; rewrite addNKr.
Qed.

(** Source for [lebesgue_scalar_translation_set]: Federer 2.7.16,
    p. 134, the translation invariance of L^1: L^1[c + T] = L^1(T).
    Direct formalisation. *)
Theorem lebesgue_scalar_translation_set (c : R) (T : set R) :
  L1 [set c + t | t in T] = L1 T.
Proof.
have h := congr1 (fun mu => mu T) (measure_bijection_pushforward (lebesgue_scalar_translation (- c))).
rewrite /= /measure_pushforward in h; rewrite -h.
congr (L1 _); apply/seteqP; split=> y.
- by move=> [x hx <-] /=; rewrite addKr.
- by move=> hy; exists (- c + y)=> //; rewrite addNKr.
Qed.

End Translation.
