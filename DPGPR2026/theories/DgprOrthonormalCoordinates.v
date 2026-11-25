(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    section 2, mr:notation: coordinates with respect to an orthonormal
    basis of a finite dimensional inner product space, and the
    coordinate form of a symmetric endomorphism with an orthonormal
    basis of eigenvectors (Federer 1.7.1, 1.7.3, 1.7.5). These supporting
    identities serve lem:sv, def:spectral, lem:spectral and lem:trace. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Bilinear InnerProductUP InnerNorm LinearBasis Hom
  OrthonormalFamilies OrthonormalParseval OrthonormalBilinearCoordinates
  FiniteDualDimension BilinearFiniteCoordinates GramSchmidt OrthonormalisationUP
  AdjointUP EigenbasisUP InnerProductLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Coordinates.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [dgpr_inner_sumr]: Federer 1.7.1, p. 28, bilinearity of
    the inner product, in the form used for finite expansions in the
    blueprint (mr:notation). *)
Lemma dgpr_inner_sumr (I : finType) (c : I -> R) (u : I -> V) x :
  B x (\sum_i c i *: u i) = \sum_i c i * B x (u i).
Proof.
rewrite inner_symmetric // -(inner_coordinateE hB) linear_sum.
apply: eq_bigr => i _; by rewrite linearZ inner_coordinateE inner_symmetric.
Qed.

(** Source for [dgpr_inner_suml]: Federer 1.7.1, p. 28, bilinearity of
    the inner product in its first argument (blueprint mr:notation). *)
Lemma dgpr_inner_suml (I : finType) (c : I -> R) (u : I -> V) x :
  B (\sum_i c i *: u i) x = \sum_i c i * B (u i) x.
Proof.
rewrite inner_symmetric // dgpr_inner_sumr.
apply: eq_bigr => i _; by rewrite inner_symmetric.
Qed.

(** Source for [dgpr_innerZr]: Federer 1.7.1, p. 28, linearity of the
    inner product in its second argument. *)
Lemma dgpr_innerZr c x y : B x (c *: y) = c * B x y.
Proof.
have h := dgpr_inner_sumr (fun _ : 'I_1 => c) (fun _ => y) x.
by rewrite !big_ord1 in h.
Qed.

(** Source for [dgpr_innerZl]: Federer 1.7.1, p. 28, linearity of the
    inner product in its first argument. *)
Lemma dgpr_innerZl c x y : B (c *: x) y = c * B x y.
Proof. by rewrite inner_symmetric // dgpr_innerZr inner_symmetric. Qed.

(** Source for [dgpr_orthonormal_basis_exists]: Federer 1.7.1, p. 28,
    every finite dimensional inner product space has an orthonormal
    basis with the same number of elements as a given basis. *)
Lemma dgpr_orthonormal_basis_exists n (e : 'I_n -> V) :
  is_basis e -> exists u : 'I_n -> V, is_basis u /\ orthonormal_family B u.
Proof.
move=> he; have [u [hu ho]] := orthonormal_basis_exists hB he.
exists u; split=> //; exact: orthonormalisation_orthonormal ho.
Qed.

Variable I : finType.
Variable u : I -> V.
Hypothesis hu : is_basis u.
Hypothesis ho : orthonormal_family B u.

(** Source for [dgpr_orthonormal_expansion]: Federer 1.7.5, p. 32, the
    expansion x = sum_i (x . u_i) u_i in an orthonormal basis. *)
Lemma dgpr_orthonormal_expansion x : x = \sum_i B x (u i) *: u i.
Proof.
rewrite {1}(orthonormal_basis_vector_expansion hu x).
apply: eq_bigr => i _; by rewrite (orthonormal_basis_inner_coordinate hB ho).
Qed.

(** Source for [dgpr_orthonormal_coefficient]: Federer 1.7.1, p. 28, the
    coefficient of u_i in a linear combination is its product with u_i. *)
Lemma dgpr_orthonormal_coefficient (c : I -> R) i :
  B (\sum_j c j *: u j) (u i) = c i.
Proof. by rewrite -(inner_coordinateE hB) orthonormal_coefficient. Qed.

(** Source for [dgpr_orthonormal_inner]: Federer 1.7.5, p. 32, the
    product x . y = sum_i (x . u_i)(y . u_i). *)
Lemma dgpr_orthonormal_inner x y : B x y = \sum_i B x (u i) * B y (u i).
Proof.
rewrite {1}(dgpr_orthonormal_expansion x) dgpr_inner_suml.
by apply: eq_bigr => i _; rewrite [B (u i) y](inner_symmetric hB).
Qed.

(** Source for [dgpr_orthonormal_parseval]: Federer 1.7.5, p. 32, the
    identity x . x = sum_i (x . u_i)^2. *)
Lemma dgpr_orthonormal_parseval x : B x x = \sum_i (B x (u i)) ^+ 2.
Proof. exact: (orthonormal_parseval hB ho hu x). Qed.

(** Source for [dgpr_orthonormal_zero]: Federer 1.7.5, p. 32, a vector
    orthogonal to every member of an orthonormal basis vanishes. *)
Lemma dgpr_orthonormal_zero x : (forall i, B x (u i) = 0) -> x = 0.
Proof.
move=> h; rewrite (dgpr_orthonormal_expansion x).
apply: big1 => i _; by rewrite h scale0r.
Qed.

(** Source for [dgpr_orthonormal_bilinear]: Federer 1.7.10, p. 35, the
    value of a bilinear form expressed through an orthonormal basis. *)
Lemma dgpr_orthonormal_bilinear (g : V -> V -> R) (hg : @bilinear R V V R^o g) x y :
  g x y = \sum_i \sum_j B x (u i) * B y (u j) * g (u i) (u j).
Proof.
by rewrite {1}(dgpr_orthonormal_expansion x) {1}(dgpr_orthonormal_expansion y)
  (bilinear_finite_expansion hg).
Qed.

Variable f : {linear V -> V}.
Variable a : I -> R.
Hypothesis hf : forall i, f (u i) = a i *: u i.

(** Source for [dgpr_eigen_expansion]: Federer 1.7.3, p. 29, an
    endomorphism with eigenvectors u_i and eigenvalues a_i satisfies
    f(x) = sum_i a_i (x . u_i) u_i (blueprint def:spectral). *)
Lemma dgpr_eigen_expansion x : f x = \sum_i (a i * B x (u i)) *: u i.
Proof.
rewrite {1}(dgpr_orthonormal_expansion x) linear_sum.
apply: eq_bigr => i _; by rewrite linearZ_LR hf scalerA mulrC.
Qed.

(** Source for [dgpr_eigen_coefficient]: Federer 1.7.3, p. 29, the
    identity f(x) . u_i = a_i (x . u_i). *)
Lemma dgpr_eigen_coefficient x i : B (f x) (u i) = a i * B x (u i).
Proof. by rewrite dgpr_eigen_expansion dgpr_orthonormal_coefficient. Qed.

(** Source for [dgpr_eigen_quadratic]: Federer 1.7.3, p. 29, the
    identity x . f(x) = sum_i a_i (x . u_i)^2. *)
Lemma dgpr_eigen_quadratic x : B x (f x) = \sum_i a i * (B x (u i)) ^+ 2.
Proof.
rewrite (dgpr_orthonormal_inner x (f x)); apply: eq_bigr => i _.
by rewrite dgpr_eigen_coefficient expr2 mulrCA.
Qed.

(** Source for [dgpr_weighted_square_lower]: blueprint lem:sv, proof of
    item rank: if d <= a_i whenever x . u_i is nonzero, then
    d (x . x) <= sum_i a_i (x . u_i)^2. *)
Lemma dgpr_weighted_square_lower x d :
  (forall i, B x (u i) != 0 -> d <= a i) ->
  d * B x x <= \sum_i a i * (B x (u i)) ^+ 2.
Proof.
move=> h; rewrite dgpr_orthonormal_parseval mulr_sumr; apply: ler_sum => i _.
have [hz|hz] := eqVneq (B x (u i)) 0; first by rewrite hz expr0n /= !mulr0.
by apply: ler_wpM2r; [exact: sqr_ge0|exact: h].
Qed.

(** Source for [dgpr_weighted_square_upper]: blueprint lem:sv, proof of
    item eigen: if a_i <= d whenever x . u_i is nonzero, then
    sum_i a_i (x . u_i)^2 <= d (x . x). *)
Lemma dgpr_weighted_square_upper x d :
  (forall i, B x (u i) != 0 -> a i <= d) ->
  \sum_i a i * (B x (u i)) ^+ 2 <= d * B x x.
Proof.
move=> h; rewrite dgpr_orthonormal_parseval mulr_sumr; apply: ler_sum => i _.
have [hz|hz] := eqVneq (B x (u i)) 0; first by rewrite hz expr0n /= !mulr0.
by apply: ler_wpM2r; [exact: sqr_ge0|exact: h].
Qed.
End Coordinates.

Section ImageSquare.
Variable R : realType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable X : {linear V -> W}.
Variable Xs : {linear W -> V}.
Hypothesis hXs : is_adjoint B C X Xs.
Variable I : finType.
Variable u : I -> V.
Hypothesis hu : is_basis u.
Hypothesis ho : orthonormal_family B u.
Variable a : I -> R.
Hypothesis hf : forall i, Xs (X (u i)) = a i *: u i.

(** Source for [dgpr_image_square]: blueprint lem:sv, proof of item
    eigen: if X* o X (u_i) = a_i u_i for an orthonormal basis u, then
    |X(v)|^2 = v . X* o X (v) = sum_i a_i (u_i . v)^2. *)
Lemma dgpr_image_square x : C (X x) (X x) = \sum_i a i * (B x (u i)) ^+ 2.
Proof.
rewrite -hXs.
exact: (@dgpr_eigen_quadratic R V B hB I u hu ho (linear_comp Xs X) a hf x).
Qed.

(** Source for [dgpr_image_eigenvalue]: blueprint lem:spectral, proof
    of lem:DGPR32: a_i = |X(u_i)|^2, in particular a_i >= 0. *)
Lemma dgpr_image_eigenvalue i : a i = C (X (u i)) (X (u i)).
Proof.
rewrite -hXs hf dgpr_innerZr //.
by rewrite (orthonormal_diagonal ho) mulr1.
Qed.

(** Source for [dgpr_image_eigenvalue_nonnegative]: blueprint lem:sv, the
    eigenvalues of X* o X are nonnegative. *)
Lemma dgpr_image_eigenvalue_nonnegative i : 0 <= a i.
Proof. by rewrite dgpr_image_eigenvalue; exact: inner_nonnegative. Qed.
End ImageSquare.
