(** Supporting continuous integrands for the finite elementary integral
    evaluations in Federer (1969), 2.6.3(2), pp. 117–118 These polynomial
    expressions in the clipped reciprocal agree with the printed rational
    functions on their integration intervals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology normedtype.
From Federer Require Import StieltjesDaniellIntegral UniformPrimitivePowers ClippedReciprocal RationalPrimitiveExpressions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [rational_first_density_continuous]: supporting
    continuous extension of the first integrand for the
    primitive calculation in Federer 2.6.3(2), p. 117. *)
Lemma rational_first_density_continuous (R : realType) (y : R) :
  0 < y -> continuous (rational_clipped_first_density y).
Proof.
move=> hy; have hpos : 0 < 0+y by rewrite add0r.
have hU := @clipped_reciprocal_continuous R 0 y hpos.
have h2 := continuous_real_square hU; have h3 := continuous_real_cube hU; have h4 := continuous_real_fourth hU.
have hneg : continuous (fun x => -(clipped_reciprocal 0 y x)^+2).
  have he : (fun x => -(clipped_reciprocal 0 y x)^+2) =
    (fun x => (-1)*(clipped_reciprocal 0 y x)^+2) by apply: funext=> x; rewrite mulN1r.
  rewrite he; exact: continuous_scale h2.
have hc3 : continuous (fun x => (6*y)*(clipped_reciprocal 0 y x)^+3) := continuous_scale (c:=6*y) h3.
have hc4 : continuous (fun x => (6*y^+2)*(clipped_reciprocal 0 y x)^+4) := continuous_scale (c:=6*y^+2) h4.
move=> x; apply: (@continuousB R R^o R^o
  (fun x => -(clipped_reciprocal 0 y x)^+2+(6*y)*(clipped_reciprocal 0 y x)^+3)
  (fun x => (6*y^+2)*(clipped_reciprocal 0 y x)^+4) x).
- exact (@continuousD R R^o R^o _ _ x (hneg x) (hc3 x)).
- exact: hc4 x.
Qed.

(** Source for [rational_second_density_continuous]: supporting
    continuous extension of the second integrand for the
    primitive calculation in Federer 2.6.3(2), p. 118. *)
Lemma rational_second_density_continuous (R : realType) (a : R) :
  0 < a -> continuous (rational_clipped_second_density a).
Proof.
move=> ha; have hpos : 0 < 0+a by rewrite add0r.
have hU := @clipped_reciprocal_continuous R 0 a hpos.
have h2 := continuous_real_square hU; have h3 := continuous_real_cube hU.
have hc2 : continuous (fun y => (-a)*(clipped_reciprocal 0 a y)^+2) := continuous_scale (c:=-a) h2.
have hc3 : continuous (fun y => (2*a^+2)*(clipped_reciprocal 0 a y)^+3) := continuous_scale (c:=2*a^+2) h3.
move=> y; exact (@continuousD R R^o R^o _ _ y (hc2 y) (hc3 y)).
Qed.
