(** Scalar background for Federer (1969), 2.4.12, pp. 86–87, and 2.4.13, p.
    88: real powers, exponential and logarithm. These supporting scalar laws
    are not additional numbered claims in Federer. Existence is proved
    separately; downstream arguments use the abstract laws through an opaque
    seal. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_real_exponential_logarithm]: abstract elementary
    scalar background supporting the powers in Federer 2.4.12,
    p. 86, and the logarithmic proof of 2.4.13, p. 88.
    The tangent inequalities support strict concavity; Federer
    uses strict concavity as elementary background. *)
Record is_real_exponential_logarithm (R : realType) (e l : R -> R) : Prop := {
  (** Source for [real_exponential_positive]: positivity of the exponential,
      elementary scalar background for Federer 2.4.13, p. 88. *)
  real_exponential_positive : forall x, 0 < e x;
  (** Source for [real_exponential_zero]: normalisation of the exponential,
      elementary scalar background for Federer 2.4.13, p. 88. *)
  real_exponential_zero : e 0 = 1;
  (** Source for [real_exponential_add]: exponential addition law,
      elementary scalar background for Federer 2.4.13, p. 88. *)
  real_exponential_add : forall x y, e (x+y) = e x * e y;
  (** Source for [real_exponential_strict_order]: strict order preservation of the exponential,
      elementary scalar background for Federer 2.4.13, p. 88. *)
  real_exponential_strict_order : forall x y, (e x < e y) = (x < y);
  (** Source for [real_logarithm_exponential]: logarithm as left inverse,
      elementary scalar background for Federer 2.4.13, p. 88. *)
  real_logarithm_exponential : forall x, l (e x) = x;
  (** Source for [real_exponential_logarithm]: logarithm as inverse on positive reals,
      elementary scalar background for Federer 2.4.13, p. 88. *)
  real_exponential_logarithm : forall x, 0 < x -> e (l x) = x;
  (** Source for [real_exponential_tangent]: supporting tangent bound for the exponential,
      elementary scalar background for Federer 2.4.13, p. 88. *)
  real_exponential_tangent : forall x, 1+x <= e x;
  (** Source for [real_exponential_strict_tangent]: strict tangent bound away from zero,
      elementary scalar background for Federer 2.4.13, p. 88. *)
  real_exponential_strict_tangent : forall x, x != 0 -> 1+x < e x
}.
