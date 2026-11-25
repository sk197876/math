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

From Federer Require Import GradedDegreeUP GradedDegreeSealed.
Section Interface.
Variable K : fieldType.
Variable V : lmodType K.
Variable G : grading V.
(** Source for [graded_degree]: Federer 1.10.4, p. 46,
    the degree of an element, exposed only through the sealed laws. *)
Definition graded_degree := @GradedDegree.degree K V G.
(** Source for [graded_degreeP]: Federer 1.10.4, p. 46,
    the public operation satisfies the supremum specification. *)
Theorem graded_degreeP x : is_graded_degree G x (graded_degree x).
Proof. exact: GradedDegree.laws. Qed.
(** Source for [graded_degree_zero]: Federer 1.10.4,
    p. 46, the zero element has degree zero. *)
Lemma graded_degree_zero : graded_degree 0=0%N.
Proof. exact: graded_degree_unique (graded_degreeP 0) (graded_degree_zero_law G). Qed.
(** Source for [graded_degree_component_bound]: Federer 1.10.4,
    p. 46, every nonzero component lies at or below the degree. *)
Lemma graded_degree_component_bound x n : grade G n x != 0 -> (n<=graded_degree x)%N.
Proof. exact: (proj1 (graded_degreeP x)). Qed.
(** Source for [graded_degree_homogeneous]: Federer 1.10.4,
    p. 46, the degree of a nonzero homogeneous element is its component index. *)
Lemma graded_degree_homogeneous m x : homogeneous G m x -> x!=0 -> graded_degree x=m.
Proof.
move=> hx hn; exact: graded_degree_unique (graded_degreeP x) (graded_degree_homogeneous_law hx hn).
Qed.
(** Source for [graded_degree_bound]: Federer 1.10.4,
    p. 46, all components of degree greater than the supremum vanish. *)
Lemma graded_degree_bound x : grade_bounded G x (graded_degree x).+1.
Proof.
move=> n hn; apply/eqP; apply/negPn/negP=> hne.
have hb := graded_degree_component_bound hne.
by move: hn; rewrite ltnNge hb.
Qed.
(** Source for [graded_degree_le_of_bound]: Federer
    1.10.4, p. 46, supporting upper-bound property
    of the degree supremum: vanishing above M implies degree at most M. *)
Lemma graded_degree_le_of_bound x M : grade_bounded G x M.+1 ->
  (graded_degree x <= M)%N.
Proof.
move=> hb; case: (proj2 (graded_degreeP x))=> [->|hn]; first exact: leq0n.
apply/negPn/negP=> h; have hMd : (M < graded_degree x)%N by rewrite ltnNge.
by move: hn; rewrite (hb _ hMd) eqxx.
Qed.
End Interface.
