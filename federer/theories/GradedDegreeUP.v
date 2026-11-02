(** Federer (1969), 1.10.4, p. 46: degree is the supremum of the nonzero
    coefficient degrees together with {0}. Supporting abstraction for any
    nonnegatively graded vector space. The specification here follows
    Federer. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded GradedSums.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_graded_degree]: Federer 1.10.4, p. 46,
    the supremum definition. In words: every nonzero component degree
    is bounded by d, and d is either zero or a nonzero component degree.
    This specifies the finite maximum independently of its construction. *)
Definition is_graded_degree (K : fieldType) (V : lmodType K) (G : grading V) x d : Prop :=
  (forall n, grade G n x != 0 -> (n<=d)%N) /\
  (d=0%N \/ grade G d x != 0).

(** Source for [graded_degree_unique]: Federer 1.10.4,
    p. 46, supporting uniqueness of the stated supremum. *)
Theorem graded_degree_unique (K : fieldType) (V : lmodType K) (G : grading V) x d e :
  is_graded_degree G x d -> is_graded_degree G x e -> d=e.
Proof.
move=> [hd hd'] [he he']; apply/eqP; rewrite eqn_leq; apply/andP; split.
- case: hd'=> [->|hn]; first exact: leq0n.
  exact: he.
- case: he'=> [->|hn]; first exact: leq0n.
  exact: hd.
Qed.

(** Source for [graded_degree_zero_law]: Federer 1.10.4,
    p. 46, adjoining {0} makes the degree of the zero element zero. *)
Lemma graded_degree_zero_law (K : fieldType) (V : lmodType K) (G : grading V) :
  is_graded_degree G (0 : V) 0.
Proof. split; last by left. by move=> n; rewrite linear0 eqxx. Qed.

(** Source for [graded_degree_homogeneous_law]: Federer 1.10.4,
    p. 46, a nonzero homogeneous element of degree m has degree m. *)
Lemma graded_degree_homogeneous_law (K : fieldType) (V : lmodType K) (G : grading V)
    m x : homogeneous G m x -> x != 0 -> is_graded_degree G x m.
Proof.
move=> hx hn; split.
- move=> n; rewrite (grade_homogeneous n hx).
  case: ifP=> [/eqP ->|_]; first by move=> _; exact: leqnn.
  by rewrite eqxx.
- right; by rewrite hx.
Qed.
