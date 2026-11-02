(** Federer (1969), 1.7.3, pp. 29-30: evaluation of a two-dimensional skew
    block. the evaluation below uses the antisymmetric difference required
    by the stated wedge formula. This is a correction to those supporting
    displays, not a change to Federer's statement. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP Bilinear SkewPairUP SkewNormalFormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [skew_pair_evaluation]: Federer 1.7.3,
    pp. 29-30, supporting evaluation on a two-dimensional
    invariant piece: f(v).w is lambda times the alternating
    product of the two inner-product coordinates. *)
Theorem skew_pair_evaluation (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (f : {linear V -> V}) x y lambda (hp : is_skew_pair B f x y lambda)
    v w : (exists a c : R, v = a *: x+c *: y) ->
  B (f v) w = lambda * skew_pair_form B x y v w.
Proof.
move=> [a [c ->]].
have hxy := skew_pair_orthogonal hp.
have hyx : B y x = 0 by rewrite (inner_symmetric hB).
rewrite linearD !linearZ (skew_pair_first_image hp) (skew_pair_second_image hp)
  /skew_pair_form !(bilDl (inner_bilinear hB)) !(bilZl (inner_bilinear hB))
  (skew_pair_first_unit hp) (skew_pair_second_unit hp) hxy hyx.
change (a * (lambda * B y w) + c * ((-lambda) * B x w) =
  lambda * ((a * 1+c * 0) * B w y - (a * 0+c * 1) * B w x)).
rewrite !mulr1 !mulr0 addr0 add0r (inner_symmetric hB y w)
  (inner_symmetric hB x w) mulrBr mulNr mulrN.
by rewrite !mulrA [a * lambda]mulrC [c * lambda]mulrC.
Qed.
