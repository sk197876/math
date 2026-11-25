(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear GradedAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section GradedInduction.
Variable K : fieldType.
Variable V : lmodType K.
Variable G : grading V.

(** Source for [graded_induction]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma graded_induction (P : V -> Prop)
  (h0 : P 0) (hD : forall x y, P x -> P y -> P (x + y))
  (hh : forall n x, homogeneous G n x -> P x) : forall x, P x.
Proof.
move=> x; have [N ->] := grade_finite G x.
apply: big_ind => // i _; exact: hh (homogeneous_grade G i x).
Qed.

(** Source for [grade_bounded]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Definition or construction
    used to formalise this passage. *)
Definition grade_bounded x N := forall n, (N <= n)%N -> grade G n x = 0.

(** Source for [grade_reconstruction_bound]: Federer (1969), 1.2.1, p. 11,
    opening paragraph and degree condition. In words: A graded algebra is a
    vector space with a specified direct sum indexed by nonnegative integers
    and a bilinear multiplication that adds degrees. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma grade_reconstruction_bound x N :
  x = \sum_(i < N) grade G i x -> grade_bounded x N.
Proof.
move=> hx n hn; rewrite {1}hx linear_sum /=.
apply: big1 => i _; rewrite grade_orthogonal.
have hni : n != i by apply/eqP=> e; move: (ltn_ord i); rewrite -e ltnNge hn.
by rewrite (negPf hni).
Qed.

(** Source for [grade_bound_exists]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma grade_bound_exists x : exists N, x == \sum_(i < N) grade G i x.
Proof. by have [N hN] := grade_finite G x; exists N; apply/eqP. Qed.
(** Source for [grade_bound]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Definition or construction
    used to formalise this passage. *)
Definition grade_bound x := xchoose (grade_bound_exists x).
(** Source for [grade_boundP]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma grade_boundP x : grade_bounded x (grade_bound x).
Proof. apply: grade_reconstruction_bound; apply/eqP; exact: (xchooseP (grade_bound_exists x)). Qed.

(** Source for [grade_bounded0]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma grade_bounded0 : grade_bounded 0 0.
Proof. by move=> n _; rewrite linear0. Qed.
(** Source for [grade_boundedD]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma grade_boundedD x y N : grade_bounded x N -> grade_bounded y N -> grade_bounded (x+y) N.
Proof. by move=> hx hy n hn; rewrite linearD /= hx // hy // addr0. Qed.
(** Source for [grade_boundedZ]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma grade_boundedZ x a N : grade_bounded x N -> grade_bounded (a *: x) N.
Proof. by move=> hx n hn; rewrite linearZ /= hx // scaler0. Qed.
(** Source for [grade_bounded_mono]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma grade_bounded_mono x N M : (N <= M)%N -> grade_bounded x N -> grade_bounded x M.
Proof. by move=> hNM hx n hn; apply: hx; exact: leq_trans hNM hn. Qed.

Variable W : lmodType K.
Variable f : nat -> {linear V -> W}.
(** Source for [graded_sum]: Federer (1969), 1.2.1, p. 11, opening paragraph
    and degree condition. In words: A graded algebra is a vector space with
    a specified direct sum indexed by nonnegative integers and a bilinear
    multiplication that adds degrees. Definition or construction used to
    formalise this passage. *)
Definition graded_sum x := \sum_(i < grade_bound x) f i (grade G i x).

(** Source for [graded_sum_widen]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma graded_sum_widen x N M : grade_bounded x N -> (N <= M)%N ->
  \sum_(i < N) f i (grade G i x) = \sum_(i < M) f i (grade G i x).
Proof.
move=> hx hNM; rewrite (big_ord_widen M (fun i : nat => f i (grade G i x)) hNM) big_mkcond.
apply: eq_bigr => i _; case: ifP => hi //.
by rewrite hx ?linear0 // leqNgt hi.
Qed.

(** Source for [graded_sum_on]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma graded_sum_on x N : grade_bounded x N ->
  graded_sum x = \sum_(i < N) f i (grade G i x).
Proof.
move=> hx; rewrite /graded_sum.
rewrite (graded_sum_widen (@grade_boundP x) (leq_maxl _ N)).
by rewrite (graded_sum_widen hx (leq_maxr (grade_bound x) _)).
Qed.

(** Source for [graded_sum_linear]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma graded_sum_linear : linear graded_sum.
Proof.
move=> a x y.
pose N := maxn (grade_bound x) (grade_bound y).
have hx : grade_bounded x N := grade_bounded_mono (leq_maxl _ _) (@grade_boundP x).
have hy : grade_bounded y N := grade_bounded_mono (leq_maxr _ _) (@grade_boundP y).
rewrite (graded_sum_on (grade_boundedD (grade_boundedZ a hx) hy))
  (graded_sum_on hx) (graded_sum_on hy) scaler_sumr -big_split /=.
by apply: eq_bigr => i _; rewrite !linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K V W *:%R graded_sum graded_sum_linear.

(** Source for [graded_sum_homogeneous]: Federer (1969), 1.2.1, p. 11,
    opening paragraph and degree condition. In words: A graded algebra is a
    vector space with a specified direct sum indexed by nonnegative integers
    and a bilinear multiplication that adds degrees. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma graded_sum_homogeneous n x : homogeneous G n x -> graded_sum x = f n x.
Proof.
move=> hx.
have hb : grade_bounded x n.+1.
  move=> i hi; rewrite (grade_homogeneous i hx).
  have hin : i != n by rewrite neq_ltn hi orbT.
  by rewrite (negPf hin).
rewrite (graded_sum_on hb).
under eq_bigr do rewrite (grade_homogeneous _ hx).
under eq_bigr do rewrite (fun_if (f _)) linear0.
rewrite -big_mkcond.
by rewrite (big_pred1 (Ordinal (ltnSn n))).
Qed.
End GradedInduction.

Section GradedParameter.
Variable K : fieldType.
Variables U V W : lmodType K.
Variable G : grading V.
Variable f : U -> nat -> {linear V -> W}.
Hypothesis hf : forall n v, linear (fun u => f u n v).
(** Source for [graded_sum_parameter_linear]: Federer (1969), 1.2.1, p. 11,
    opening paragraph and degree condition. In words: A graded algebra is a
    vector space with a specified direct sum indexed by nonnegative integers
    and a bilinear multiplication that adds degrees. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma graded_sum_parameter_linear v : linear (fun u => graded_sum G (f u) v).
Proof.
move=> a u u'; rewrite /graded_sum scaler_sumr -big_split /=.
by apply: eq_bigr => i _; rewrite hf.
Qed.
End GradedParameter.

(** Source for [graded_sum_constant]: Federer (1969), 1.2.1, p. 11, opening
    paragraph and degree condition. In words: A graded algebra is a vector
    space with a specified direct sum indexed by nonnegative integers and a
    bilinear multiplication that adds degrees. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma graded_sum_constant (K : fieldType) (V W : lmodType K) (G : grading V)
  (f : {linear V -> W}) x : graded_sum G (fun _ => f) x = f x.
Proof.
rewrite /graded_sum -linear_sum /=; congr (f _).
by apply/eqP; rewrite eq_sym; exact: (xchooseP (grade_bound_exists G x)).
Qed.
