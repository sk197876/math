(** Federer (1969), 1.9.2, p. 42: if a single vector forms a basis, its m-th
    power forms a basis of the m-th symmetric power. Here the whole
    symmetric algebra of the scalar line is given the homogeneous basis of
    all powers of one. Arbitrary fields are allowed. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import TensorUP FreeVector LinearBasis Bilinear AlgebraUP
  WordEvaluation CommutativeWords ScalarCoefficients GradedAlgebra GradedBasis
  SymmetricAlgebra SymmetricGrading.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Line.
Variable K : fieldType.
Local Notation E := (symmetric_space K^o).
Local Notation F := (free_vector K (Choice.clone nat _)).

(** Source for [symmetric_line_power]: Federer 1.9.2, p. 42,
    the displayed m-fold power of a one-dimensional basis vector.
    On the scalar line choose the basis vector one; degree zero is empty. *)
Definition symmetric_line_power m : E := symmetric_word (nseq m (1 : K^o)).

(** Source for [symmetric_line_coefficient]: Federer 1.9.2,
    p. 42, supporting coefficient calculation: multiply the scalar
    coordinates of all factors in a word. *)
Definition symmetric_line_coefficient (s : seq K^o) : K :=
  @word_eval K K^o (scalar_algebra K) (linear_id K^o) s.

(** Source for [symmetric_line_coordinates_word]: Federer 1.9.2,
    p. 42, supporting coordinates of a line word: its coefficient
    multiplies the basis vector indexed by its word length. *)
Definition symmetric_line_coordinates_word (s : seq K^o) : F :=
  symmetric_line_coefficient s *: delta K (size s).

(** Source for [symmetric_line_coordinates_multilinear]: Federer
    1.9.2, p. 42, supporting multilinearity of these word coordinates. *)
Lemma symmetric_line_coordinates_multilinear :
  multilinear_words symmetric_line_coordinates_word.
Proof.
move=> s t a v w; rewrite /symmetric_line_coordinates_word
  /symmetric_line_coefficient !size_cat /=.
have h := @word_eval_multilinear K K^o (scalar_algebra K) (linear_id K^o) s t a v w.
rewrite h; change ((a * symmetric_line_coefficient (s ++ v :: t) +
  symmetric_line_coefficient (s ++ w :: t)) *: delta K (size s + (size t).+1) =
  a *: (symmetric_line_coefficient (s ++ v :: t) *: delta K (size s + (size t).+1)) +
  symmetric_line_coefficient (s ++ w :: t) *: delta K (size s + (size t).+1)).
by rewrite scalerDl scalerA.
Qed.

(** Source for [symmetric_line_coordinates_symmetric]: Federer
    1.9.2, p. 42, supporting invariance of the word coordinates under
    permutation, using commutativity of scalar multiplication. *)
Lemma symmetric_line_coordinates_symmetric s t : perm_eq s t ->
  symmetric_line_coordinates_word s = symmetric_line_coordinates_word t.
Proof.
move=> hp; rewrite /symmetric_line_coordinates_word (perm_size hp).
congr (_ *: _); exact (@commutative_word_permutation K K^o (scalar_algebra K)
  (@mulrC K) (linear_id K^o) s t hp).
Qed.

(** Source for [symmetric_line_coordinates]: Federer 1.9.2,
    p. 42, supporting linear coordinate map, obtained from the
    symmetric-multilinear universal property. *)
Definition symmetric_line_coordinates : {linear E -> F} :=
  symmetric_word_extension symmetric_line_coordinates_multilinear
    symmetric_line_coordinates_symmetric.

(** Source for [symmetric_line_coordinatesE]: Federer 1.9.2,
    p. 42, the coordinates of the m-th power of the basis vector
    are the single unit coordinate indexed by m. *)
Lemma symmetric_line_coordinatesE m :
  symmetric_line_coordinates (symmetric_line_power m) = delta K m.
Proof.
rewrite /symmetric_line_power symmetric_word_extensionE
  /symmetric_line_coordinates_word size_nseq.
have h : symmetric_line_coefficient (nseq m (1 : K^o)) = 1.
  rewrite /symmetric_line_coefficient.
  by elim: m => [|m ih] //=; rewrite mul1r ih.
by rewrite h scale1r.
Qed.

(** Source for [symmetric_line_word_factor]: Federer 1.9.2,
    p. 42, every length-m product in the scalar line is its scalar
    coefficient times the m-th power of the basis vector. *)
Lemma symmetric_line_word_factor s :
  symmetric_word s = symmetric_line_coefficient s *: symmetric_line_power (size s).
Proof.
elim: s => [|v s ih]; first by rewrite /symmetric_line_coefficient /symmetric_line_power /= scale1r.
have hv : v = (v : K) *: (1 : K^o) by change (v = v * 1); rewrite mulr1.
rewrite symmetric_word_cons {1}hv linearZ (bilZl (symmetric_product_bilinear K^o)) ih
  (bilZr (symmetric_product_bilinear K^o)) scalerA.
change ((v * symmetric_line_coefficient s) *:
  symmetric_product (symmetric_generator 1) (symmetric_line_power (size s)) =
  (v * symmetric_line_coefficient s) *: symmetric_line_power (size s).+1).
by rewrite /symmetric_line_power symmetric_word_cons.
Qed.

(** Source for [symmetric_line_basis_synthesisK]: Federer 1.9.2,
    p. 42, supporting linear independence: extracting coordinates
    after synthesis recovers every finite coefficient family. *)
Lemma symmetric_line_basis_synthesisK :
  cancel (basis_synthesis symmetric_line_power) symmetric_line_coordinates.
Proof.
apply: free_induction => [|x y hx hy|a x hx|m].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
by rewrite basis_synthesisE symmetric_line_coordinatesE.
Qed.

(** Source for [symmetric_line_coordinatesK]: Federer 1.9.2,
    p. 42, supporting spanning: synthesis from coordinates recovers
    every symmetric element of the scalar line. *)
Lemma symmetric_line_coordinatesK :
  cancel symmetric_line_coordinates (basis_synthesis symmetric_line_power).
Proof.
apply: symmetric_word_induction => [|x y hx hy|a x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
rewrite symmetric_word_extensionE /symmetric_line_coordinates_word
  linearZ basis_synthesisE.
exact: esym (symmetric_line_word_factor s).
Qed.

(** Source for [symmetric_line_graded_basis]: Federer 1.9.2,
    p. 42, powers of a single basis vector form a homogeneous basis.
    This whole-algebra form implies the stated basis in each degree. *)
Theorem symmetric_line_graded_basis :
  is_graded_basis (symmetric_grading K^o) symmetric_line_power id.
Proof.
split.
- exists symmetric_line_coordinates; split.
  + exact: symmetric_line_basis_synthesisK.
  + exact: symmetric_line_coordinatesK.
- move=> m; have h := symmetric_word_homogeneous (nseq m (1 : K^o)).
  by rewrite size_nseq in h.
Qed.
End Line.
