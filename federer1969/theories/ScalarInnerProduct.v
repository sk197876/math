(** Federer (1969), 1.10.6, pp. 48-49, the real scalar coefficient space in
    the inner product on scalar-valued forms. This supporting instance makes
    explicit the usual scalar inner product used throughout the book. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_inner_productP]: Federer 1.10.6,
    pp. 48-49, supporting instance: the scalar inner product is
    multiplication, positive on the square of every nonzero real scalar. *)
Lemma scalar_inner_productP (R : realFieldType) :
  @is_inner_product R R^o (fun x y : R => x*y).
Proof.
constructor.
- split=> [y a x z|x a y z].
  + change ((a*x+z)*y = a*(x*y)+z*y).
    by rewrite mulrDl mulrA.
  + change (x*(a*y+z) = a*(x*y)+x*z).
    by rewrite mulrDr !mulrA [x*a]mulrC.
- exact: mulrC.
- move=> x; by rewrite -expr2 lt_def sqr_ge0 andbT sqrf_eq0.
Qed.

(** Source for [scalar_inner_normE]: Federer 1.10.6,
    pp. 48-49, supporting agreement: length in the scalar
    inner product space is the usual absolute value. *)
Lemma scalar_inner_normE (R : rcfType) (x : R) :
  inner_norm (scalar_inner_productP R) x = `|x|.
Proof.
apply: inner_norm_value; first exact: normr_ge0.
by rewrite -normrX (ger0_norm (sqr_ge0 x)) expr2.
Qed.
