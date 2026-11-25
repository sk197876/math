(** Federer (1969), 1.7.1, p. 28: Cauchy's inequality and the triangle
    inequality, both strict for independent vectors. The proof uses the
    diagonal quadratic expression and the norm's abstract square-root laws,
    without coordinates. Source context are recorded in InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws InnerCauchy
  InnerNorm IndependentPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Inequalities.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation N := (inner_norm hB).

(** Source for [inner_cauchy]: Federer 1.7.1, p. 28,
    Cauchy's inequality. The absolute-value version follows from
    the same quadratic argument and implies the printed upper bound. *)
Theorem inner_cauchy x y : `|B x y| <= N x * N y.
Proof.
rewrite -(ler_sqr (normr_ge0 _) (mulr_ge0 (inner_norm_nonnegative hB x) (inner_norm_nonnegative hB y))).
rewrite exprMn -normrX ger0_norm ?sqr_ge0 // !inner_norm_sqr.
exact (@inner_cauchy_squared R V B hB x y).
Qed.

(** Source for [inner_cauchy_upper]: Federer 1.7.1,
    p. 28, the printed inequality x.y <= |x| |y|. *)
Theorem inner_cauchy_upper x y : B x y <= N x * N y.
Proof. exact: le_trans (ler_norm _) (inner_cauchy x y). Qed.

(** Source for [inner_norm_triangle]: Federer 1.7.1,
    p. 28, the triangle inequality |x+y| <= |x|+|y|. *)
Theorem inner_norm_triangle x y : N (x+y) <= N x + N y.
Proof.
rewrite -(ler_sqr (inner_norm_nonnegative hB _) (addr_ge0 (inner_norm_nonnegative hB x) (inner_norm_nonnegative hB y))).
rewrite inner_norm_sqr (inner_sum_square hB) sqrrD !inner_norm_sqr mulr2n lerD2r lerD2l.
exact: lerD (inner_cauchy_upper x y) (inner_cauchy_upper x y).
Qed.

(** Source for [inner_cauchy_squared_strict]: Federer
    1.7.1, p. 28, strictness under linear independence, before
    taking square roots. The equality criterion rules out equality. *)
Theorem inner_cauchy_squared_strict x y :
  independent_pair x y -> B x y ^+ 2 < B x x * B y y.
Proof.
move=> h; rewrite lt_def; apply/andP; split.
  2: exact (@inner_cauchy_squared R V B hB x y).
apply/eqP=> he.
have he' : B x y ^+ 2 = B x x * B y y by rewrite he.
have hs := (proj1 (inner_cauchy_equality hB x (independent_pair_right_nonzero h))) he'.
by move: (independent_pair_not_scaled h (B x y / B y y)); rewrite -hs eqxx.
Qed.

(** Source for [inner_cauchy_strict]: Federer 1.7.1,
    p. 28, Cauchy's inequality is strict for independent x,y;
    the stronger absolute-value version is proved here. *)
Theorem inner_cauchy_strict x y :
  independent_pair x y -> `|B x y| < N x * N y.
Proof.
move=> h.
rewrite -(ltr_sqr (normr_ge0 _) (mulr_ge0 (inner_norm_nonnegative hB x) (inner_norm_nonnegative hB y))).
rewrite exprMn -normrX ger0_norm ?sqr_ge0 // !inner_norm_sqr.
exact: inner_cauchy_squared_strict h.
Qed.

(** Source for [inner_cauchy_upper_strict]: Federer 1.7.1,
    p. 28, the printed upper inequality is strict for independent vectors. *)
Theorem inner_cauchy_upper_strict x y :
  independent_pair x y -> B x y < N x * N y.
Proof. move=> h; exact: le_lt_trans (ler_norm _) (inner_cauchy_strict h). Qed.

(** Source for [inner_norm_triangle_strict]: Federer 1.7.1,
    p. 28, the triangle inequality is strict for independent vectors. *)
Theorem inner_norm_triangle_strict x y :
  independent_pair x y -> N (x+y) < N x + N y.
Proof.
move=> h.
rewrite -(ltr_sqr (inner_norm_nonnegative hB _) (addr_ge0 (inner_norm_nonnegative hB x) (inner_norm_nonnegative hB y))).
rewrite inner_norm_sqr (inner_sum_square hB) sqrrD !inner_norm_sqr mulr2n ltrD2r ltrD2l.
exact: ltrD (inner_cauchy_upper_strict h) (inner_cauchy_upper_strict h).
Qed.
End Inequalities.
