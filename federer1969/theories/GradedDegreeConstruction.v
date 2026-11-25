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

From Federer Require Import GradedDegreeUP.
Section Construction.
Variable K : fieldType.
Variable V : lmodType K.
Variable G : grading V.

(** Source for [graded_degree_witness]: Federer 1.10.4,
    p. 46, supporting existence construction: take the finite maximum
    inside a support bound, replacing zero components by zero. *)
Definition graded_degree_witness x :=
  (\max_(i < (grade_bound G x).+1) if grade G i x != (0%R : V) then val i else 0)%N.

(** Source for [graded_degree_witness_laws]: Federer 1.10.4,
    p. 46, the finite maximum satisfies the abstract supremum laws. *)
Theorem graded_degree_witness_laws x : is_graded_degree G x (graded_degree_witness x).
Proof.
split.
- move=> n hn.
  have hnb : (n < grade_bound G x)%N.
    case: (ltnP n (grade_bound G x))=> hnb //= .
    by move: hn; rewrite (@grade_boundP K V G x n hnb) eqxx.
  pose i : 'I_(grade_bound G x).+1 := Ordinal (ltn_trans hnb (ltnSn _)).
  have h := @leq_bigmax 'I_(grade_bound G x).+1 (fun j : 'I_(grade_bound G x).+1 =>
    if grade G j x != (0%R : V) then val j else 0%N) i.
  by rewrite /i /= hn in h.
- have hc : (0 < #|'I_(grade_bound G x).+1|)%N by rewrite card_ord.
  have [i hi] := @eq_bigmax 'I_(grade_bound G x).+1 (fun j : 'I_(grade_bound G x).+1 =>
    if grade G j x != (0%R : V) then val j else 0%N) hc.
  change (graded_degree_witness x = if grade G i x != (0%R : V) then val i else 0%N) in hi.
  case he: (grade G i x != (0%R : V)).
  + right; by rewrite hi he.
  + left; by rewrite hi he.
Qed.
End Construction.
