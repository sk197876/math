(** Federer (1969), 1.7.1, p. 28: Cauchy's inequality from positivity of the
    diagonal quadratic polynomial. We evaluate that polynomial at its
    minimising coefficient, keeping the zero-vector case separate. This is
    scalar algebra, without finite dimension. Source context are recorded in
    InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws Bilinear FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Cauchy.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation hb := (inner_bilinear hB).

(** Source for [inner_residual_orthogonal]: Federer 1.7.1,
    p. 28, supporting completion of the square. Subtracting
    B(x,y)/B(y,y) times y from x makes the residual orthogonal to y. *)
Lemma inner_residual_orthogonal x y (hy : y != 0) :
  B (x - (B x y / B y y) *: y) y = 0.
Proof.
rewrite (bilBl hb) (bilZl hb).
change (B x y - (B x y / B y y) * B y y = 0).
by rewrite divfK ?subrr // (inner_self_eq0 hB).
Qed.

(** Source for [inner_residual_square]: Federer 1.7.1,
    p. 28, the quadratic argument written by completing the square:
    the residual's squared length is B(x,x)-B(x,y)^2/B(y,y). *)
Lemma inner_residual_square x y (hy : y != 0) :
  B (x - (B x y / B y y) *: y) (x - (B x y / B y y) *: y) =
  B x x - B x y ^+ 2 / B y y.
Proof.
rewrite (bilBr hb) (bilZr hb) (inner_residual_orthogonal x hy) scaler0 subr0.
rewrite (bilBl hb) (bilZl hb) (inner_symmetric hB y x).
change (B x x - (B x y / B y y) * B x y = B x x - B x y ^+ 2 / B y y).
by rewrite mulrAC -expr2.
Qed.

(** Source for [inner_cauchy_squared]: Federer 1.7.1,
    p. 28, Cauchy's inequality before taking square roots.
    The square of the mixed product is bounded by the product
    of the diagonal values. Both zero-vector cases are included. *)
Theorem inner_cauchy_squared x y : B x y ^+ 2 <= B x x * B y y.
Proof.
case hy: (y == 0).
  move/eqP: hy => ->; by rewrite !(bil0r hb) expr0n mulr0.
have hny : y != 0 by rewrite hy.
have hp : 0 < B y y by rewrite (inner_positive hB) hny.
have h := inner_nonnegative hB (x - (B x y / B y y) *: y).
by rewrite (inner_residual_square x hny) subr_ge0 (ler_pdivrMr _ _ hp) in h.
Qed.

(** Source for [inner_cauchy_equality]: Federer 1.7.1, p. 28, strictness for
    independent vectors. Supporting equality criterion for nonzero y:
    equality holds exactly when x is the scalar projection B(x,y)/B(y,y)
    times y. *)
Theorem inner_cauchy_equality x y (hy : y != 0) :
  B x y ^+ 2 = B x x * B y y <-> x = (B x y / B y y) *: y.
Proof.
have hyy : B y y != 0 by rewrite (inner_self_eq0 hB).
split.
- move=> h.
  have hz : B (x - (B x y / B y y) *: y) (x - (B x y / B y y) *: y) = 0.
    by rewrite inner_residual_square // h mulfK // subrr.
  apply/eqP; rewrite -subr_eq0 -(inner_self_eq0 hB) hz eqxx; by [].
- move=> h.
  have hz : x - (B x y / B y y) *: y = 0 by rewrite -h subrr.
  have hh := inner_residual_square x hy.
  rewrite hz (bil0l hb) in hh.
  have hd : B x x = B x y ^+ 2 / B y y by apply/eqP; rewrite -subr_eq0 -hh eqxx.
  by rewrite hd divfK.
Qed.
End Cauchy.
