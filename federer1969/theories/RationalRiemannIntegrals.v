(** Federer (1969), 2.6.3(2), pp. 117–118: the two finite primitive
    evaluations, first for the project's Riemann integral of 2.5.17.
    Conversion to actual Lebesgue subset integrals is separate; these
    results do not assume that conversion. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology normedtype.
From Federer Require Import StieltjesIntegral UniformPrimitiveIntegral RationalFubiniKernel
  RationalPrimitiveExpressions RationalPrimitiveContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [rational_first_riemann_integral]: first finite integral
    calculation in Federer 2.6.3(2), p. 117 The zero-length case is
    included. *)
Theorem rational_first_riemann_integral (R : realType) (y a : R) :
  0 < y -> 0 <= a ->
  stieltjes_integral (fun x => x) (rational_clipped_first_density y) 0 a = rational_first_primitive y a.
Proof.
move=> hy ha.
have h := uniform_primitive_riemann_integral (rational_first_density_continuous hy) ha
  (@rational_first_primitive_uniform R y a hy).
rewrite (rational_clipped_first_primitive_on hy ha)
  (rational_clipped_first_primitive_on hy (lexx 0)) rational_first_primitive_zero subr0 in h.
exact: esym h.
Qed.

(** Source for [rational_second_riemann_integral]: second finite integral
    calculation in Federer 2.6.3(2), p. 118 The upper endpoint is arbitrary
    and nonnegative, including m*a as printed. *)
Theorem rational_second_riemann_integral (R : realType) (a b : R) :
  0 < a -> 0 <= b ->
  stieltjes_integral (fun y => y) (rational_clipped_second_density a) 0 b = rational_second_primitive a b.
Proof.
move=> ha hb.
have h := uniform_primitive_riemann_integral (rational_second_density_continuous ha) hb
  (@rational_second_primitive_uniform R a b ha).
rewrite (rational_clipped_second_primitive_on ha hb)
  (rational_clipped_second_primitive_on ha (lexx 0)) rational_second_primitive_zero subr0 in h.
exact: esym h.
Qed.
