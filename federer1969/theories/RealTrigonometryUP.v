(** Federer (1969), 3.2.7, p. 246:
    elementary scalar trigonometry used in the first and
    third counterexamples. Specify the functions and their
    needed laws before proving existence and sealing them.
    The laws are background, not additional printed claims. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_real_trigonometric_system]: abstract scalar
    background for the sine examples of Federer 3.2.7,
    p. 246. All fields must be proved by an existence
    witness; none is a new project axiom. *)
Record is_real_trigonometric_system (R:realType) (S C A:R->R) (p:R):Prop:={
  (** Source for [real_trigonometry_pi_positive]: positive half-period,
      scalar background for Federer 3.2.7, p. 246. *)
  real_trigonometry_pi_positive:0<p;
  (** Source for [real_sine_zero]: sine normalization supporting
      the first example in Federer 3.2.7, p. 246. *)
  real_sine_zero:S 0= 0;
  (** Source for [real_cosine_zero]: cosine normalization supporting
      the actual sine derivative in Federer 3.2.7, p. 246. *)
  real_cosine_zero:C 0= 1;
  (** Source for [real_sine_bound]: bounded oscillation in the
      first and third examples of Federer 3.2.7, p. 246. *)
  real_sine_bound:forall x,`|S x|<= 1;
  (** Source for [real_cosine_bound]: derivative bound supporting
      absolute continuity in Federer 3.2.7, p. 246. *)
  real_cosine_bound:forall x,`|C x|<= 1;
  (** Source for [real_sine_odd]: negative half-cycle values in
      the oscillatory example of Federer 3.2.7, p. 246. *)
  real_sine_odd:forall x,S (-x)= -S x;
  (** Source for [real_sine_half_period]: sign alternation between
      successive half-cycles in Federer 3.2.7, p. 246. *)
  real_sine_half_period:forall x,S (x+p)= -S x;
  (** Source for [real_cosine_half_period]: cosine sign alternation
      supporting the sine examples in Federer 3.2.7, p. 246. *)
  real_cosine_half_period:forall x,C (x+p)= -C x;
  (** Source for [real_sine_peak]: unit peaks for the third
      example of Federer 3.2.7, p. 246. *)
  real_sine_peak:S (p/2)= 1;
  (** Source for [real_sine_derivative]: actual scalar derivative
      of sine used in Federer 3.2.7, p. 246. *)
  real_sine_derivative:forall x,has_real_curve_derivative S x (C x);
  (** Source for [real_cosine_derivative]: actual cosine derivative,
      supporting scalar calculus for Federer 3.2.7, p. 246. *)
  real_cosine_derivative:forall x,has_real_curve_derivative C x (-S x);
  (** Source for [real_sine_branch_injective]: injectivity of the
      principal closed sine branch, supporting Federer 3.2.7, p. 246. *)
  real_sine_branch_injective:forall x y,
    -(p/2)<=x -> x<=p/2 -> -(p/2)<=y -> y<=p/2 -> S x=S y -> x=y;
  (** Source for [real_arcsine_range]: the principal inverse
      branch range used to compute multiplicities in Federer 3.2.7, p. 246. *)
  real_arcsine_range:forall y,-1<=y -> y<= 1 -> -(p/2)<=A y /\ A y<=p/2;
  (** Source for [real_arcsine_sine]: every level between minus
      one and one is attained, supporting Federer 3.2.7, p. 246. *)
  real_arcsine_sine:forall y,-1<=y -> y<= 1 -> S (A y)=y
}.
