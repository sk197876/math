(** Federer (1969), 2.4.16, p. 90, last proof line: replacing a test
    function u by u sign(u) sign(f) preserves its absolute bound and makes
    its product with f nonnegative. The corrected expression is already
    printed correctly by Federer. The erratum, p. 2, book p. 89 line 19,
    changes the test norm condition to at most one. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dual_test_sign_alignment]: corrected test function in
    Federer 2.4.16, p. 90, final proof line *)
Definition dual_test_sign_alignment (R : realType) (x u : R) :=
  u * Num.sg u * Num.sg x.

(** Source for [dual_test_sign_alignment_product]: supporting
    product identity in Federer 2.4.16, p. 90, final line. *)
Lemma dual_test_sign_alignment_product (R : realType) (x u : R) :
  x * dual_test_sign_alignment x u = `|x| * `|u|.
Proof.
by rewrite /dual_test_sign_alignment [u * Num.sg u]mulrC -normrEsg mulrCA
  [x * Num.sg x]mulrC -normrEsg mulrC.
Qed.

(** Source for [dual_test_sign_alignment_bound]: supporting
    norm domination of the corrected test, Federer 2.4.16, p. 90. *)
Lemma dual_test_sign_alignment_bound (R : realType) (x u : R) :
  `|dual_test_sign_alignment x u| <= `|u|.
Proof.
rewrite /dual_test_sign_alignment [u * Num.sg u]mulrC -normrEsg normrM
  normr_id normr_sg.
by case: (x != 0); rewrite ?mulr1 ?mulr0 ?normr_ge0.
Qed.

(** Source for [dual_test_missing_sign_counterexample]: Supporting check for
    Federer 2.4.16, p. 90: replacing sign(f) by f in the test function can
    violate its norm bound. At f=2 and u=1 the absolute value becomes two. *)
Lemma dual_test_missing_sign_counterexample (R : realType) :
  ~ (`|1 * Num.sg (1:R) * 2| <= `|(1:R)|).
Proof.
rewrite sgr1 !mul1r normr1 normr_nat.
move=> h; have ht : (1:R) < 2 by rewrite ltr1n.
have hh := le_lt_trans h ht; by move: hh; rewrite ltxx.
Qed.
