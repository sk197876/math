(** Federer (1969), 2.6.3(2), pp. 117–118: primitive laws for the two
    elementary rational integrals. We express the primitives as polynomials
    in a reciprocal, prove their finite-increment laws, and identify the
    printed formulas on the nonnegative half-line. The clipping outside that
    half-line only supplies continuous extensions for the existing
    Riemann-integral interface. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology normedtype ring lra.
From Federer Require Import UniformPrimitiveUP UniformPrimitiveAlgebra UniformPrimitivePowers
  ClippedReciprocal RationalFubiniKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [rational_clipped_first_primitive]: supporting
    reciprocal-polynomial expression for (x^2-xy)/(x+y)^3
    in Federer 2.6.3(2), p. 117, agreeing for x>=0. *)
Definition rational_clipped_first_primitive (R : realType) (y x : R) : R :=
  let U := clipped_reciprocal 0 y x in U-3*y*U^+2+2*y^+2*U^+3.

(** Source for [rational_clipped_first_density]: supporting
    continuous extension of the rational kernel's first-coordinate
    section in Federer 2.6.3(2), p. 117. At x=0
    the rational value differs from the piecewise kernel's zero;
    singleton nullity is used when transferring integral values. *)
Definition rational_clipped_first_density (R : realType) (y x : R) : R :=
  let U := clipped_reciprocal 0 y x in -U^+2+6*y*U^+3-6*y^+2*U^+4.

(** Source for [rational_clipped_second_primitive]: supporting
    reciprocal-polynomial expression for a*y/(a+y)^2 in
    Federer 2.6.3(2), p. 118, agreeing for y>=0. *)
Definition rational_clipped_second_primitive (R : realType) (a y : R) : R :=
  let U := clipped_reciprocal 0 a y in a*U-a^+2*U^+2.

(** Source for [rational_clipped_second_density]: supporting
    continuous extension of (a^2-ay)/(a+y)^3 for the
    second primitive calculation in Federer 2.6.3(2), p. 118. *)
Definition rational_clipped_second_density (R : realType) (a y : R) : R :=
  let U := clipped_reciprocal 0 a y in -a*U^+2+2*a^+2*U^+3.

(** Source for [rational_first_primitive_uniform]: proved elementary
    primitive law for the first integral in Federer 2.6.3(2), p. 117 The
    finite-increment condition is derived from reciprocal, product and
    linearity laws. *)
Lemma rational_first_primitive_uniform (R : realType) (y b : R) :
  0 < y -> is_uniform_primitive_on (rational_clipped_first_density y)
    (rational_clipped_first_primitive y) 0 b.
Proof.
move=> hy; have hpos : 0 < 0+y by rewrite add0r.
have hU := @clipped_reciprocal_continuous R 0 y hpos.
have h1 := @clipped_reciprocal_uniform_primitive R 0 b y hpos.
have h2 := @uniform_primitive_scale R _ _ 0 b (-3*y) (reciprocal_square_uniform_primitive hU h1).
have h3 := @uniform_primitive_scale R _ _ 0 b (2*y^+2) (reciprocal_cube_uniform_primitive hU h1).
have h := uniform_primitive_add (uniform_primitive_add h1 h2) h3.
apply: (@uniform_primitive_ext R _ _ _ _ 0 b _ h)=> x _.
rewrite /rational_clipped_first_density /rational_clipped_first_primitive; split; ring.
Qed.

(** Source for [rational_second_primitive_uniform]: proved elementary
    primitive law for the second integral in Federer 2.6.3(2), p. 118 *)
Lemma rational_second_primitive_uniform (R : realType) (a b : R) :
  0 < a -> is_uniform_primitive_on (rational_clipped_second_density a)
    (rational_clipped_second_primitive a) 0 b.
Proof.
move=> ha; have hpos : 0 < 0+a by rewrite add0r.
have hU := @clipped_reciprocal_continuous R 0 a hpos.
have h1 := @clipped_reciprocal_uniform_primitive R 0 b a hpos.
have h2 := @uniform_primitive_scale R _ _ 0 b a h1.
have h3 := @uniform_primitive_scale R _ _ 0 b (-a^+2) (reciprocal_square_uniform_primitive hU h1).
have h := uniform_primitive_add h2 h3.
apply: (@uniform_primitive_ext R _ _ _ _ 0 b _ h)=> x _.
rewrite /rational_clipped_second_density /rational_clipped_second_primitive; split; ring.
Qed.

(** Source for [rational_clipped_first_primitive_on]: exact
    identification with the first displayed primitive value
    in Federer 2.6.3(2), p. 117. *)
Lemma rational_clipped_first_primitive_on (R : realType) (y x : R) :
  0 < y -> 0 <= x -> rational_clipped_first_primitive y x = rational_first_primitive y x.
Proof.
move=> hy hx; have hp : 0 < x+y by lra.
have hn : x+y != 0 := lt0r_neq0 hp.
rewrite /rational_clipped_first_primitive clipped_reciprocal_on // /rational_first_primitive.
by field; rewrite hn.
Qed.

(** Source for [rational_clipped_first_density_on]: exact
    rational integrand on the nonnegative first half-line,
    supporting Federer 2.6.3(2), p. 117. *)
Lemma rational_clipped_first_density_on (R : realType) (y x : R) :
  0 < y -> 0 <= x -> rational_clipped_first_density y x = rational_fubini_density x y.
Proof.
move=> hy hx; have hp : 0 < x+y by lra.
have hn : x+y != 0 := lt0r_neq0 hp.
rewrite /rational_clipped_first_density clipped_reciprocal_on // /rational_fubini_density.
by field; rewrite hn.
Qed.

(** Source for [rational_clipped_second_primitive_on]: exact
    second primitive used for the final rectangle integral
    in Federer 2.6.3(2), p. 118. *)
Lemma rational_clipped_second_primitive_on (R : realType) (a y : R) :
  0 < a -> 0 <= y -> rational_clipped_second_primitive a y = rational_second_primitive a y.
Proof.
move=> ha hy; have hp : 0 < y+a by lra.
have hn : y+a != 0 := lt0r_neq0 hp.
rewrite /rational_clipped_second_primitive clipped_reciprocal_on // /rational_second_primitive [a+y]addrC.
by field; rewrite hn.
Qed.

(** Source for [rational_clipped_second_density_on]: exact
    first-primitive expression appearing as the second integrand
    in Federer 2.6.3(2), p. 118. *)
Lemma rational_clipped_second_density_on (R : realType) (a y : R) :
  0 < a -> 0 <= y -> rational_clipped_second_density a y = rational_first_primitive y a.
Proof.
move=> ha hy; have hp : 0 < y+a by lra.
have hn : y+a != 0 := lt0r_neq0 hp.
rewrite /rational_clipped_second_density clipped_reciprocal_on // /rational_first_primitive [a+y]addrC.
by field; rewrite hn.
Qed.
