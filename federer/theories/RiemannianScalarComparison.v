(** Federer (1969), 3.2.46, printed p. 281: scalar details of
    the lambda comparison for positive quadratic forms. Every norm
    in the actual geometric application is nonnegative; no dimension
    restriction or nonzero-vector premise is needed. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_comparison_error_positive]: a positive
    quadratic-error budget for any 1<lambda, supporting the second
    paragraph of Federer 3.2.46, p. 281. *)
Lemma riemannian_comparison_error_positive (R : realType) (l : R) :
  1 < l -> 0 < Order.min (l^+2-1) (1-l^-1^+2).
Proof.
move=> hl.
have hl0 : 0 < l := lt_trans ltr01 hl.
have hInv : 0 < l^-1 by rewrite invr_gt0.
have hInv1 : l^-1 < 1 by rewrite invf_lt1.
have hSq : 1 < l^+2.
  have h := ltr_sqr ler01 (ltW hl0).
  rewrite expr1n in h; rewrite h; exact hl.
have hInvSq : l^-1^+2 < 1.
  have h := ltr_sqr (ltW hInv) ler01.
  rewrite expr1n in h; rewrite h; exact hInv1.
by rewrite lt_min !subr_gt0 hSq hInvSq.
Qed.

(** Source for [riemannian_quadratic_error_comparison]: a small
    relative quadratic error gives the printed two-sided norm
    comparison, Federer 3.2.46, p. 281. In the geometric theorem
    s=|L(v)| and t=g(x)(v,v)^(1/2), including v=0. *)
Lemma riemannian_quadratic_error_comparison (R : realType) (l s t : R) :
  1 < l -> 0 <= s -> 0 <= t ->
  `|t^+2-s^+2| <= Order.min (l^+2-1) (1-l^-1^+2) * s^+2 ->
  l^-1*s <= t /\ t <= l*s.
Proof.
move=> hl hs ht hError.
have hl0 : 0 < l := lt_trans ltr01 hl.
have hi0 : 0 <= l^-1 by rewrite invr_ge0; exact: ltW hl0.
have hS : 0 <= s^+2 := sqr_ge0 s.
have hUpper : t^+2-s^+2 <= (l^+2-1)*s^+2.
  apply: le_trans (ler_norm _) _; apply: le_trans hError _.
  apply: ler_wpM2r=> //; by rewrite ge_min lexx.
have hLower : s^+2-t^+2 <= (1-l^-1^+2)*s^+2.
  apply: le_trans (ler_norm _) _.
  rewrite distrC; apply: le_trans hError _.
  apply: ler_wpM2r=> //; by rewrite ge_min lexx orbT.
split.
- rewrite -(ler_sqr (mulr_ge0 hi0 hs) ht) exprMn.
  nra.
- rewrite -(ler_sqr ht (mulr_ge0 (ltW hl0) hs)) exprMn.
  nra.
Qed.
