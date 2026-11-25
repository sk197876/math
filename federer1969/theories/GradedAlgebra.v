(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear AlgebraUP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.2.1. Pairwise orthogonal projections and finite reconstruction
    specify an internal direct sum indexed by the nonnegative integers. *)
(** Source for [grading]: Federer (1969), 1.2.1, p. 11, opening paragraph
    and degree condition. In words: A graded algebra is a vector space with
    a specified direct sum indexed by nonnegative integers and a bilinear
    multiplication that adds degrees. Definition or construction used to
    formalise this passage. *)
Record grading (K : fieldType) (V : lmodType K) := Grading {
  grade : nat -> {linear V -> V};
  grade_orthogonal : forall m n x,
    grade m (grade n x) = if m == n then grade n x else 0;
  grade_finite : forall x, exists N, x = \sum_(i < N) grade i x
}.

Section Homogeneous.
Variable K : fieldType.
Variable V : lmodType K.
Variable G : grading V.

(** Source for [homogeneous]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Definition or construction
    used to formalise this passage. *)
Definition homogeneous n x : Prop := grade G n x = x.

(** Source for [homogeneous0]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma homogeneous0 n : homogeneous n 0.
Proof. exact: linear0. Qed.
(** Source for [homogeneousD]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma homogeneousD n x y :
  homogeneous n x -> homogeneous n y -> homogeneous n (x + y).
Proof. by move=> hx hy; rewrite /homogeneous linearD /= hx hy. Qed.
(** Source for [homogeneousZ]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma homogeneousZ n a x : homogeneous n x -> homogeneous n (a *: x).
Proof. by move=> hx; rewrite /homogeneous linearZ /= hx. Qed.
(** Source for [homogeneous_grade]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma homogeneous_grade n x : homogeneous n (grade G n x).
Proof. by rewrite /homogeneous grade_orthogonal eqxx. Qed.
(** Source for [grade_homogeneous]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma grade_homogeneous m n x : homogeneous n x ->
  grade G m x = if m == n then x else 0.
Proof.
move=> hx; rewrite -{1}hx grade_orthogonal.
by case: ifP=> _; rewrite ?hx.
Qed.
(** Source for [homogeneous_disjoint]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma homogeneous_disjoint m n x : m != n ->
  homogeneous m x -> homogeneous n x -> x = 0.
Proof.
move=> hmn hm hn.
by rewrite -hm (grade_homogeneous m hn) (negPf hmn).
Qed.
End Homogeneous.

Section GradedProducts.
Variable K : fieldType.
Variable V : lmodType K.
Variable G : grading V.
Variable mu : V -> V -> V.

(** Source for [graded_product]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Definition or construction
    used to formalise this passage. *)
Definition graded_product : Prop :=
  forall m n x y, homogeneous G m x -> homogeneous G n y ->
    homogeneous G (m + n)%N (mu x y).

(** Source for [graded_anticommutative]: Federer (1969), 1.2.1, p. 11, final
    displayed anticommutative law. In words: Interchanging homogeneous
    factors of degrees m and n multiplies the product by the sign (-1)^(mn).
    Definition or construction used to formalise this passage. *)
Definition graded_anticommutative : Prop :=
  forall m n x y, homogeneous G m x -> homogeneous G n y ->
    mu x y = (-1 : K) ^+ (m * n) *: mu y x.

(** Source for [degree_one_square_zero]: Federer (1969), 1.2.1, p. 11, final
    anticommutative law, applied twice to a degree-one element. In words:
    For a homogeneous element of degree one, the anticommutative law gives a
    square equal to its negative; hence the square vanishes when two is
    invertible. Supporting lemma for this passage; not separately stated in
    the book. The square-zero consequence is explicit in the proof of
    Federer 1.3.1, p. 14; the characteristic hypothesis must be retained. *)
Lemma degree_one_square_zero : graded_anticommutative ->
  (1 + 1 : K) != 0 -> forall x, homogeneous G 1 x -> mu x x = 0.
Proof.
move=> hc h2 x hx.
have e := hc 1 1 x x hx hx.
rewrite muln1 expr1 scaleN1r in e.
have hz : (1 + 1 : K) *: mu x x = 0.
  by rewrite scalerDl !scale1r {1}e addNr.
move/eqP: hz; rewrite scaler_eq0 (negPf h2) orFb.
exact/eqP.
Qed.
End GradedProducts.

(** Source for [graded_algebra]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Definition or construction
    used to formalise this passage. *)
Record graded_algebra (K : fieldType) := GradedAlgebra {
  graded_space :> lmodType K;
  algebra_grading : grading graded_space;
  graded_mul : graded_space -> graded_space -> graded_space;
  graded_bilinear : bilinear graded_mul;
  graded_mul_degree : graded_product algebra_grading graded_mul
}.

Section GradedMaps.
Variable K : fieldType.
Variables U V W : lmodType K.
Variables (GU : grading U) (GV : grading V) (GW : grading W).

(** Source for [preserves_grading]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Definition or construction
    used to formalise this passage. *)
Definition preserves_grading (f : {linear U -> V}) : Prop :=
  forall n x, homogeneous GU n x -> homogeneous GV n (f x).

(** Source for [preserves_grading_id]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma preserves_grading_id :
  forall n x, homogeneous GU n x -> homogeneous GU n (linear_id U x).
Proof. by []. Qed.

(** Source for [preserves_grading_comp]: Federer (1969), 1.2.1, p. 11,
    opening paragraph and degree condition. In words: A graded algebra is a
    vector space with a specified direct sum indexed by nonnegative integers
    and a bilinear multiplication that adds degrees. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma preserves_grading_comp (f : {linear V -> W}) (g : {linear U -> V}) :
  (forall n x, homogeneous GV n x -> homogeneous GW n (f x)) ->
  preserves_grading g ->
  forall n x, homogeneous GU n x -> homogeneous GW n (linear_comp f g x).
Proof. by move=> hf hg n x hx; apply: hf; exact: hg hx. Qed.
End GradedMaps.
