(** Federer (1969), 2.7.16, pp. 134–135: "for every linear endomorphism f of
    R^n, L^n[f(S)] = |det f| . L^n(S) whenever S is a subset of R^n", and in
    case det f <> 0, "f_#(L^n) = |det f|^{-1} . L^n". For det f <> 0, 1.7.3,
    p. 30, gives an orthonormal base e_1, ..., e_n of R^n with f(e_i) .
    f(e_j) = 0 for i <> j. With c_i = |f(e_i)| > 0 and e'_i = f(e_i)/c_i, f
    o g = h o d where g(x) = sum_i x_i e_i and h(x) = sum_i x_i e'_i are
    orthogonal and d(x) = (c_1 x_1, ..., c_n x_n); this is the generation of
    GL(n, R) by the two special types of maps used by Federer. Hence chi(f)
    = chi(d) = (c_1 ... c_n)^{-1} and |det f| = c_1 ... c_n. For det f = 0
    the adjoint f* has det f* = det f = 0 (1.7.6, p. 33); 1.7.3 applied to
    f* gives an orthonormal base containing a vector w with f*(w) = 0, so im
    f lies in the hyperplane {y : y . w = 0}, which is the image of the
    coordinate hyperplane {x : x_j = 0} under an orthogonal map and has
    measure 0. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground FiniteCoordinates GrassmannAbbreviations
  EuclideanInnerProduct InnerProductUP InnerProductLaws InnerNorm InnerMetric InnerNormedTopology
  LinearBasis Bilinear OrthogonalMaps OrthonormalFamilies OrthogonalFinite OrthogonalImageBasis
  InnerFiniteSynthesis AdjointUP Adjoint AdjointDeterminant TensorUP ExteriorDeterminant
  TopologicalBorel MeasureUP MeasureBasic MeasureSplit LebesgueScalarMeasure
  EuclideanLebesgue EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanLinearMaps
  EuclideanLebesgueLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Determinant.
Variable R : realType.
Variable n : nat.
Local Notation V := (R_n R n).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation hb := (@coordinate_basisP R n).
Local Notation eps := (@coordinate_basis R n).
Local Notation hl := (inner_bilinear (@euclidean_inner_productP R n)).

(** Source for [orthonormal_nonzero]: a member of an orthonormal family
    is not zero, Federer 1.7.1, p. 28. Supporting lemma. *)
Lemma orthonormal_nonzero (e : 'I_n -> V) : orthonormal_family B e -> forall i, e i != 0.
Proof.
move=> he i; apply/negP=> /eqP h; have := he i i; rewrite eqxx h (bil0l hl)=> /eqP.
by rewrite eq_sym oner_eq0.
Qed.

(** Source for [inner_coordinate_sum]: (sum_i a_i v_i) . w =
    sum_i a_i (v_i . w), Federer 1.7.1, p. 28. Supporting lemma. *)
Lemma inner_coordinate_sum (a : 'I_n -> R) (v : 'I_n -> V) (w : V) :
  B (\sum_i a i *: v i) w = \sum_i a i * B (v i) w.
Proof.
rewrite -(inner_coordinateE hB) linear_sum; apply: eq_bigr=> i _.
by rewrite linearZ inner_coordinateE.
Qed.

(** Source for [euclidean_orthogonal_images_injective]: if e is an
    orthonormal base of R^n and the f(e_i) are nonzero and pairwise
    orthogonal, then f is univalent, Federer 1.7.3, p. 30; supporting
    the singular case of 2.7.16, p. 134. *)
Lemma euclidean_orthogonal_images_injective (a : {linear V -> V}) (e : 'I_n -> V) :
  is_basis e -> orthonormal_family B e ->
  (forall i j, i != j -> B (a (e i)) (a (e j)) = 0) -> (forall i, a (e i) != 0) -> injective a.
Proof.
move=> he ho horth hnz x y hxy.
pose z : V := x - y.
have hz : a z = 0 by rewrite /z linearB hxy subrr.
have hexp : z = \sum_i B z (e i) *: e i.
  have h := @inner_finite_synthesis_coordinates R V B hB n e he ho z.
  rewrite /inner_finite_synthesis in h; rewrite -[LHS]h; apply: eq_bigr=> i _.
  by rewrite inner_coordinateE.
have hc j : B z (e j) = 0.
  have h0 : B (a z) (a (e j)) = 0 by rewrite hz (bil0l hl).
  have hza : a z = \sum_i B z (e i) *: a (e i).
    by rewrite {1}hexp linear_sum; apply: eq_bigr=> i _; rewrite linearZ.
  rewrite hza inner_coordinate_sum in h0.
  rewrite (eq_bigr (fun i => if i == j then B z (e j) * B (a (e j)) (a (e j)) else 0)) in h0; last first.
    move=> i _; case: (eqVneq i j)=> [->|hij]; first by [].
    by rewrite horth // mulr0.
  rewrite -big_mkcond /= big_pred1_eq in h0.
  move: h0=> /eqP; rewrite mulf_eq0 (inner_self_eq0 hB) (negbTE (hnz j)) orbF.
  by move=> /eqP.
apply/eqP; rewrite -subr_eq0; apply/eqP.
change (z = 0); rewrite hexp; apply: big1=> i _; by rewrite hc scale0r.
Qed.

(** Source for [euclidean_singular_hyperplane]: Federer 2.7.16, p. 134,
    "In case det f = 0, im f is a proper subspace of R^n": there is an
    orthonormal base e of R^n and an index j with f(x) . e_j = 0 for
    every x. Supporting lemma, by 1.7.3, p. 30, and 1.7.6, p. 33. *)
Lemma euclidean_singular_hyperplane (f : {linear V -> V}) : euclidean_det f = 0 ->
  exists e : 'I_n -> V, exists j, [/\ is_basis e, orthonormal_family B e &
    forall x, B (f x) (e j) = 0].
Proof.
move=> h0.
pose a := inner_adjoint hB hB hb f.
have ha : is_adjoint B B f a := inner_adjointP hB hB hb f.
have hda : euclidean_det a = 0.
  by rewrite /euclidean_det (adjoint_determinant (euclidean_two_nonzero R) hB hb ha).
have hna : ~ injective a by move=> hi; have := (euclidean_det_injective a).2 hi; rewrite hda eqxx.
have [e [he [ho horth]]] := orthonormal_orthogonal_image_basis hB hB a hb.
case: (pselect (exists j, a (e j) = 0))=> [[j hj]|hne].
- exists e, j; split=> // x; rewrite -ha hj; exact: (bil0r hl).
- exfalso; apply: hna; apply: (euclidean_orthogonal_images_injective he ho horth)=> i.
  by apply/eqP=> h; apply: hne; exists i.
Qed.

(** Source for [euclidean_hyperplane_null]: the hyperplane
    {y : y . e_j = 0} has L^n measure 0, supporting Federer 2.7.16,
    p. 134, "hence has L^n measure 0": it is the image of the coordinate
    hyperplane {x : x_j = 0} under the orthogonal map x |-> sum_i x_i e_i,
    and L^n{x : x_j = 0} = L^1{0} . prod_(i <> j) L^1(R) = 0. *)
Lemma euclidean_hyperplane_null (e : 'I_n -> V) (j : 'I_n) : orthonormal_family B e ->
  Leb [set y : E | B y (e j) = 0] = 0%:E.
Proof.
move=> ho.
have hF := euclidean_frame_orthogonal ho.
rewrite -(euclidean_orthogonal_pushforward hF).
have hpre : (euclidean_frame_map e : E -> E) @^-1` [set y : E | B y (e j) = 0] =
    euclidean_coordinate_box (fun i => if i == j then [set 0 : R] else setT).
  apply/seteqP; split=> x /=.
  - by rewrite (euclidean_frame_inner ho)=> hx i; case: (eqVneq i j)=> [->|hij].
  - move=> h; rewrite (euclidean_frame_inner ho); have := h j; by rewrite /= eqxx.
rewrite hpre.
have hA i : measure_measurable (@lebesgue_scalar_measure R) (if i == j then [set 0 : R] else setT).
  case: (i == j).
  - have -> : [set 0 : R] = `[0, 0].
      apply/seteqP; split=> t /=; first by move=> ->; rewrite in_itv /= lexx.
      by rewrite in_itv /= => /andP[h1 h2]; apply/eqP; rewrite eq_le h2 h1.
    exact: lebesgue_scalar_segment_measurable.
  - exact: measure_measurable_whole (lebesgue_scalar_is_measure R).
have [_ hv] := @euclidean_coordinate_box_measure R n _ hA.
rewrite hv (bigD1 j) //= eqxx.
have h0 : @lebesgue_scalar_measure R [set 0] = 0%:E := lebesgue_scalar_singleton 0.
by rewrite h0 mul0e.
Qed.

(** Source for [euclidean_lebesgue_linear_pushforward]: Federer 2.7.16,
    pp. 134–135, "In case det f <> 0, the assertion to be proved is
    equivalent to the equation f_#(L^n) = |det f|^{-1} . L^n":
    L^n[f^{-1}(S)] = |det f|^{-1} L^n(S) for every S. Direct
    formalisation. *)
Theorem euclidean_lebesgue_linear_pushforward (f : {linear V -> V}) : euclidean_det f != 0 ->
  forall S, Leb ((f : E -> E) @^-1` S) = ((`|euclidean_det f|)^-1%:E * Leb S)%E.
Proof.
move=> hdet S.
have hinj := (euclidean_det_injective f).1 hdet.
have [e [he [ho horth]]] := orthonormal_orthogonal_image_basis hB hB f hb.
pose c i := inner_norm hB (f (e i)).
have hc i : 0 < c i.
  rewrite /c lt_def inner_norm_nonnegative andbT (inner_norm_eq0 hB).
  apply/negP=> /eqP h; have := orthonormal_nonzero ho i.
  by rewrite -(inj_eq hinj) h linear0 eqxx.
pose e' i := (c i)^-1 *: f (e i).
have ho' : orthonormal_family B e'.
  move=> i j; rewrite /e' (bilZl hl) (bilZr hl).
  case: (eqVneq i j)=> [->|hij].
  - rewrite -(inner_norm_sqr hB) -/(c j).
    change ((c j)^-1 * ((c j)^-1 * c j ^+ 2) = 1).
    by rewrite mulrA -expr2 -exprMn mulVf ?expr1n //; exact: lt0r_neq0.
  - rewrite horth //; change ((c i)^-1 * ((c j)^-1 * 0) = 0); by rewrite !mulr0.
pose F := euclidean_frame_map e; pose F' := euclidean_frame_map e'.
pose D := euclidean_diagonal_map c.
have hcomp : forall x, f (F x) = F' (D x).
  apply: (@basis_linear_ext R _ V eps hb V (linear_comp f F) (linear_comp F' D))=> j.
  rewrite /linear_comp /=.
  have hDj : D (eps j) = c j *: eps j.
    apply/ffunP=> k; rewrite /D /= /euclidean_diagonal !ffunE.
    case: (eqVneq k j)=> [->|hk]; rewrite ?eqxx ?(negbTE hk); last by rewrite mulr0 scaler0.
    reflexivity.
  rewrite /F /F' /= euclidean_frame_basis hDj linearZ /= euclidean_frame_basis /e'.
  by rewrite scalerA mulfV ?scale1r //; exact: lt0r_neq0.
have hF := euclidean_frame_orthogonal ho; have hF' := euclidean_frame_orthogonal ho'.
have hpre : (F : E -> E) @^-1` ((f : E -> E) @^-1` S) = (D : E -> E) @^-1` ((F' : E -> E) @^-1` S).
  by apply/seteqP; split=> x /=; rewrite hcomp.
have hmeas : Leb ((f : E -> E) @^-1` S) = ((\prod_(i < n) c i)^-1%:E * Leb S)%E.
  rewrite -(euclidean_orthogonal_pushforward hF) hpre (euclidean_diagonal_pushforward hc).
  by rewrite (euclidean_orthogonal_pushforward hF').
have hdeq : euclidean_det (linear_comp f F) = euclidean_det (linear_comp F' D).
  by apply: det_ext=> x; rewrite /linear_comp /=; exact: hcomp.
rewrite !euclidean_det_comp euclidean_diagonal_det in hdeq.
have hp : 0 < \prod_(i < n) c i by apply: prodr_gt0=> i _.
have habs : `|euclidean_det f| = \prod_(i < n) c i.
  have h := congr1 (fun r => `|r|) hdeq; rewrite /= !normrM (euclidean_orthogonal_det hF)
    (euclidean_orthogonal_det hF') !mulr1 mul1r in h.
  by rewrite h ger0_norm // ltW.
by rewrite hmeas habs.
Qed.

(** Source for [euclidean_lebesgue_linear_image]: Federer 2.7.16,
    p. 134, "for every linear endomorphism f of R^n,
    L^n[f(S)] = |det f| . L^n(S) whenever S is a subset of R^n". Direct
    formalisation; for det f = 0 the right side is 0 . L^n(S) = 0. *)
Theorem euclidean_lebesgue_linear_image (f : {linear V -> V}) (S : set E) :
  Leb ((f : E -> E) @` S) = ((`|euclidean_det f|)%:E * Leb S)%E.
Proof.
case: (eqVneq (euclidean_det f) 0)=> [h0|hdet].
- rewrite h0 normr0 mul0e.
  have [e [j [he ho hperp]]] := euclidean_singular_hyperplane h0.
  apply/eqP; rewrite eq_le (measure_nonnegative (euclidean_lebesgue_is_measure R n)) andbT.
  have hH := euclidean_hyperplane_null j ho.
  apply: le_trans (@measure_mono R E Leb (euclidean_lebesgue_is_measure R n) _
    [set y : E | B y (e j) = 0] _) _.
    by move=> y [x _ <-]; rewrite /=; exact: hperp.
  by rewrite hH.
- have hinj := (euclidean_det_injective f).1 hdet.
  have [g [hfg hgf]] := euclidean_linear_inverse hinj.
  have hgf1 := euclidean_det_inverse hfg.
  have hg0 : euclidean_det g != 0.
    by apply/eqP=> h; move: hgf1; rewrite h mul0r=> /eqP; rewrite eq_sym oner_eq0.
  have himg : (f : E -> E) @` S = (g : E -> E) @^-1` S.
    apply/seteqP; split=> y /=.
    + by move=> [x hx <-]; rewrite hfg.
    + by move=> hy; exists (g y)=> //; rewrite hgf.
  rewrite himg (euclidean_lebesgue_linear_pushforward hg0).
  congr (_%:E * _)%E.
  have h := congr1 (fun r => `|r|) hgf1; rewrite /= normrM normr1 in h.
  rewrite -[LHS]mulr1 -h mulrA mulVf ?mul1r //.
  by rewrite normr_eq0.
Qed.

End Determinant.
