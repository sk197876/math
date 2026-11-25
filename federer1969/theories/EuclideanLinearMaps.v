(** Linear algebra of R^n for Federer (1969), 2.7.16, pp. 134–136: the
    linear endomorphisms f of R^n, their determinants det f of 1.3.4, p. 16,
    and the two special types used on p. 135, "In case f is orthogonal" and
    "f(x) = (c_1 x_1, ..., c_n x_n)". The module proves that linear maps of
    R^n are continuous (1.7.1, p. 28), that det f <> 0 exactly when f is
    univalent (1.3.4 with 1.7.6, p. 34), that univalent endomorphisms have
    linear inverses, that |det g| = 1 for orthogonal g (1.7.6, p. 33), and
    that the diagonal map has determinant c_1 ... c_n (1.3.4). The map x |->
    sum_i x_i v_i sends the standard base to v_1, ..., v_n; it is orthogonal
    when v is orthonormal (1.7.2, p. 28). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module tvs.
From mathcomp Require Import fingroup perm.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerMetric InnerNormedTopology EuclideanCoordinateTopology CoordinateProjection
  LinearBasis FiniteIndependence FiniteBasisComparison FiniteBasisCriterion FiniteDimension
  Annihilator FiniteDualDimension Hom OrthogonalMaps OrthonormalFamilies TensorUP ExteriorGrading
  ExteriorMaps ExteriorDeterminant ExteriorLeibniz PermutationDeterminant AdjointDeterminant
  TopExteriorInjectivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

Section LinearMaps.
Variable R : realType.
Variable n : nat.
Local Notation V := (R_n R n).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation B := (@euclidean_inner_product R n).
Local Notation eps := (@coordinate_basis R n).

(** Source for [euclidean_two_nonzero]: 1 + 1 <> 0 in R, the hypothesis
    of the determinant of Federer 1.3.4, p. 16, as used in 2.7.16,
    p. 134. Supporting lemma. *)
Lemma euclidean_two_nonzero : (1 + 1 : R) != 0.
Proof. by change (2%:R != (0 : R)); rewrite pnatr_eq0. Qed.

(** Source for [euclidean_det]: det f for a linear endomorphism f of
    R^n, Federer 1.3.4, p. 16, computed with the standard base; by
    det_basis_independent the choice of base is immaterial. Definition
    used in 2.7.16, pp. 134–136. *)
Definition euclidean_det (f : {linear V -> V}) : R :=
  det euclidean_two_nonzero (@coordinate_basisP R n) f.

(** Source for [euclidean_linear_expansion]: f(x) = sum_i x_i f(e_i)
    for a linear map f of R^n, Federer 1.3.4, p. 16. Supporting lemma. *)
Lemma euclidean_linear_expansion (f : {linear V -> V}) (x : V) : f x = \sum_i x i *: f (eps i).
Proof.
rewrite -{1}(euclidean_coordinate_expansion x) linear_sum.
by apply: eq_bigr=> i _; rewrite linearZ.
Qed.

(** Source for [euclidean_linear_continuous]: every linear map of R^n
    is continuous, Federer 1.7.1, p. 28, as used for the image measures
    of 2.7.16, p. 135. Supporting lemma. *)
Lemma euclidean_linear_continuous (f : {linear V -> V}) : continuous (f : E -> E).
Proof.
have he : (f : E -> E) = (fun x : E => \sum_i (x i : R^o) *: (f (eps i) : E)).
  by apply: funext=> x; exact: euclidean_linear_expansion.
rewrite he; apply: continuous_big; first exact: add_continuous.
move=> i _ x; apply: continuousZ; last exact: cst_continuous.
exact: euclidean_coordinate_continuous.
Qed.

(** Source for [euclidean_det_comp]: det(g o f) = det g . det f,
    Federer 1.3.4, p. 16. Supporting lemma. *)
Lemma euclidean_det_comp (f g : {linear V -> V}) :
  euclidean_det (linear_comp g f) = euclidean_det g * euclidean_det f.
Proof. exact: det_comp. Qed.

(** Source for [euclidean_det_id]: det(1_V) = 1, Federer 1.3.4, p. 16.
    Supporting lemma. *)
Lemma euclidean_det_id : euclidean_det (linear_id V) = 1.
Proof. exact: det_id. Qed.

(** Source for [euclidean_det_injective]: det f <> 0 if and only if f
    is univalent, Federer 1.3.4, p. 16, with the criterion of 1.7.6,
    p. 34; used in 2.7.16, p. 134, "In case det f = 0, im f is a proper
    subspace". Supporting lemma. *)
Lemma euclidean_det_injective (f : {linear V -> V}) : euclidean_det f != 0 <-> injective f.
Proof.
have h := @top_exterior_nonzero_iff_injective R euclidean_two_nonzero V V n eps (@coordinate_basisP R n) f.
rewrite -h /euclidean_det; split.
- move=> hd; exists (top_vector eps); rewrite (detE euclidean_two_nonzero (@coordinate_basisP R n)).
  by rewrite scaler_eq0 negb_or hd (top_vector_nonzero euclidean_two_nonzero (@coordinate_basisP R n)).
- move=> [x]; rewrite (detE euclidean_two_nonzero (@coordinate_basisP R n)) scaler_eq0 negb_or.
  by move=> /andP[hd _].
Qed.

(** Source for [euclidean_injective_surjective]: a univalent linear
    endomorphism of R^n maps onto R^n, by the dimension count of
    Federer 1.1.2 and 1.3.2; supporting 2.7.16, p. 134, where f with
    det f <> 0 belongs to GL(n, R). *)
Lemma euclidean_injective_surjective (f : {linear V -> V}) :
  injective f -> forall y, exists x, f x = y.
Proof.
move=> hi.
have he := @coordinate_basisP R n.
have hfe := finite_independent_map hi (finite_basis_independent he).
pose U := finite_basis_vect he.
have hb : is_basis (fun i => f (eps i)).
  apply: (@finite_independent_basis R U n (fun i => f (eps i))) => //.
  by rewrite /U finite_basis_dimension card_ord.
move=> y; exists (\sum_i dual_basis hb i y *: eps i).
rewrite linear_sum; under eq_bigr do rewrite linearZ.
exact: esym (basis_vector_expansion hb y).
Qed.

(** Source for [euclidean_linear_inverse]: every f in GL(n, R), the
    linear group of R^n, Federer 2.7.16, pp. 134–135, has a linear
    inverse. Supporting lemma. *)
Lemma euclidean_linear_inverse (f : {linear V -> V}) :
  injective f -> exists g : {linear V -> V}, cancel f g /\ cancel g f.
Proof.
move=> hi; pose g := linear_inverse hi (euclidean_injective_surjective hi).
exists (GRing.Linear.clone _ _ _ _ g _); split; first exact: linear_inverseKV.
exact: linear_inverseK.
Qed.

(** Source for [euclidean_det_inverse]: det(f^{-1}) = (det f)^{-1},
    Federer 1.3.4, p. 16, since det is multiplicative. Supporting
    lemma. *)
Lemma euclidean_det_inverse (f g : {linear V -> V}) : cancel f g ->
  euclidean_det g * euclidean_det f = 1.
Proof.
move=> hfg; rewrite -euclidean_det_comp -euclidean_det_id; apply: det_ext=> x.
by rewrite /linear_comp /linear_id /= hfg.
Qed.

(** Source for [euclidean_orthogonal_det]: |det g| = 1 for an
    orthogonal endomorphism g of R^n, Federer 1.7.6, p. 33; used in
    2.7.16, p. 135. Supporting lemma. *)
Lemma euclidean_orthogonal_det (g : {linear V -> V}) :
  is_orthogonal_map B B g -> `|euclidean_det g| = 1.
Proof.
move=> hg.
have h := orthogonal_determinant_square euclidean_two_nonzero (@euclidean_inner_productP R n)
  (@coordinate_basisP R n) hg.
by apply/eqP; rewrite -sqr_norm_eq1; apply/eqP; exact: h.
Qed.

(** Source for [euclidean_diagonal]: the map
    f(x) = (c_1 x_1, ..., c_n x_n) of Federer 2.7.16, p. 135. Direct
    definition. *)
Definition euclidean_diagonal (c : 'I_n -> R) (x : V) : V := [ffun i => c i * x i].

(** Source for [euclidean_diagonal_linear]: the map of Federer 2.7.16,
    p. 135, is linear. Supporting lemma. *)
Lemma euclidean_diagonal_linear (c : 'I_n -> R) : linear (euclidean_diagonal c).
Proof.
move=> a x y; apply/ffunP=> i; rewrite /euclidean_diagonal !ffunE.
by rewrite mulrDr mulrCA.
Qed.
HB.instance Definition _ (c : 'I_n -> R) := GRing.isLinear.Build R V V *:%R
  (euclidean_diagonal c) (euclidean_diagonal_linear c).

(** Source for [euclidean_diagonal_map]: the linear endomorphism
    x |-> (c_1 x_1, ..., c_n x_n), Federer 2.7.16, p. 135. Definition
    packaging the map with its linearity. *)
Definition euclidean_diagonal_map (c : 'I_n -> R) : {linear V -> V} :=
  GRing.Linear.clone _ _ _ _ (euclidean_diagonal c) _.

(** Source for [euclidean_diagonal_basis]: the diagonal map sends e_i
    to c_i e_i, Federer 2.7.16, p. 135. Supporting lemma. *)
Lemma euclidean_diagonal_basis (c : 'I_n -> R) i :
  euclidean_diagonal c (eps i) = \sum_(j < n) (if i == j then c i else 0) *: eps j.
Proof.
rewrite (bigD1 i) //= eqxx big1 ?addr0; last first.
  by move=> j hj; rewrite eq_sym (negbTE hj) scale0r.
apply/ffunP=> k; rewrite /euclidean_diagonal !ffunE.
case: (eqVneq k i)=> [->|hk]; rewrite ?eqxx ?(negbTE hk); last by rewrite mulr0 scaler0.
reflexivity.
Qed.

(** Source for [euclidean_diagonal_det]: det f = c_1 ... c_n for
    f(x) = (c_1 x_1, ..., c_n x_n), by the permutation formula of
    Federer 1.3.4, p. 16; used in 2.7.16, p. 135. Supporting lemma. *)
Lemma euclidean_diagonal_det (c : 'I_n -> R) :
  euclidean_det (euclidean_diagonal_map c) = \prod_(i < n) c i.
Proof.
rewrite /euclidean_det (det_formula euclidean_two_nonzero (@coordinate_basisP R n)
  (f := euclidean_diagonal_map c) (b := fun i j => if i == j then c i else 0)); last first.
  move=> i; exact: euclidean_diagonal_basis.
rewrite (bigD1 (1%g : 'S_n)) //= index_one ?euclidean_two_nonzero // mul1r.
rewrite [X in _ + X]big1 ?addr0; first by apply: eq_bigr=> i _; rewrite perm1 eqxx.
move=> s hs; case: (pselect (exists i, s i != i))=> [[i hi]|hne].
  by rewrite (bigD1 i) //= eq_sym (negbTE hi) mul0r mulr0.
exfalso; move: hs=> /eqP; apply; apply/permP=> i; rewrite perm1.
by apply/eqP; apply: contrapT=> h; apply: hne; exists i; exact/negP.
Qed.

(** Source for [euclidean_frame]: the linear map of R^n sending the
    standard base e_1, ..., e_n to v_1, ..., v_n, x |-> sum_i x_i v_i,
    supporting Federer 2.7.16, pp. 135–136 (orthogonal maps and boxes
    with orthonormal edges). Direct definition. *)
Definition euclidean_frame (v : 'I_n -> V) (x : V) : V := \sum_i x i *: v i.

(** Source for [euclidean_frame_linear]: the frame map is linear,
    supporting Federer 2.7.16, p. 136. *)
Lemma euclidean_frame_linear (v : 'I_n -> V) : linear (euclidean_frame v).
Proof.
move=> a x y; rewrite /euclidean_frame scaler_sumr -big_split /=; apply: eq_bigr=> i _.
by rewrite !ffunE scalerDl scalerA.
Qed.
HB.instance Definition _ (v : 'I_n -> V) := GRing.isLinear.Build R V V *:%R
  (euclidean_frame v) (euclidean_frame_linear v).

(** Source for [euclidean_frame_map]: the frame map packaged with its
    linearity, supporting Federer 2.7.16, p. 136. Definition. *)
Definition euclidean_frame_map (v : 'I_n -> V) : {linear V -> V} :=
  GRing.Linear.clone _ _ _ _ (euclidean_frame v) _.

(** Source for [euclidean_frame_basis]: the frame map sends e_j to v_j,
    supporting Federer 2.7.16, p. 136. *)
Lemma euclidean_frame_basis (v : 'I_n -> V) j : euclidean_frame v (eps j) = v j.
Proof.
rewrite /euclidean_frame (bigD1 j) //= big1 ?addr0; last first.
  by move=> i hi; rewrite /coordinate_basis ffunE (negbTE hi) scale0r.
by rewrite /coordinate_basis ffunE eqxx scale1r.
Qed.

(** Source for [euclidean_frame_inner]: (sum_i x_i v_i) . v_j = x_j for
    an orthonormal family v, Federer 1.7.1, p. 28; supporting the box
    {x : 0 <= (x - a) . e_i <= c_i} of 2.7.16, p. 136. *)
Lemma euclidean_frame_inner (v : 'I_n -> V) : orthonormal_family B v ->
  forall x j, B (euclidean_frame v x) (v j) = x j.
Proof.
move=> hv x j.
rewrite -(inner_coordinateE (@euclidean_inner_productP R n)) /euclidean_frame linear_sum.
rewrite (eq_bigr (fun i => if i == j then x i else 0)); last first.
  move=> i _; rewrite linearZ inner_coordinateE hv.
  by case: (i == j); [change (x i * 1 = x i); exact: mulr1|exact: scaler0].
by rewrite -big_mkcond /= big_pred1_eq.
Qed.

(** Source for [euclidean_frame_orthogonal]: for an orthonormal family
    v the frame map x |-> sum_i x_i v_i is orthogonal, Federer 1.7.2,
    p. 28; supporting 2.7.16, p. 136. *)
Lemma euclidean_frame_orthogonal (v : 'I_n -> V) : orthonormal_family B v ->
  is_orthogonal_map B B (euclidean_frame_map v).
Proof.
move=> hv x y.
rewrite euclidean_inner_symmetric -(inner_coordinateE (@euclidean_inner_productP R n)).
change (inner_coordinate (@euclidean_inner_productP R n) (euclidean_frame v x)
  (euclidean_frame v y) = B x y).
rewrite {1}/euclidean_frame linear_sum /euclidean_inner_product; apply: eq_bigr=> j _.
rewrite linearZ inner_coordinateE.
change (y j * euclidean_inner_product (v j) (euclidean_frame v x) = x j * y j).
by rewrite euclidean_inner_symmetric (euclidean_frame_inner hv) mulrC.
Qed.

End LinearMaps.
