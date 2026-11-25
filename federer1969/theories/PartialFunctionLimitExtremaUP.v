(** Federer (1969), 2.3.2, p. 74: lower and upper limits of numerical
    functions. The specifications express limsup as the infimum of eventual
    upper bounds and liminf as the supremum of eventual lower bounds;
    existence is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_function_eventual_domain]: Supporting Federer 2.3.2,
    p. 74. *)
Definition partial_function_eventual_domain (X Y : Type) (f : nat -> partial_function X Y) : set X :=
  [set x | exists N, forall n, (N <= n)%N -> partial_function_domain (f n) x].

(** Source for [partial_function_eventual_upper_bound]: supporting
    order-law form of a tail supremum bound in the upper-limit
    formula of Federer 2.3.2, p. 74. *)
Definition partial_function_eventual_upper_bound (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R)) x (b : \bar R) :=
  exists N, forall n, (N <= n)%N -> forall z, partial_function_graph (f n) x z -> z <= b.

(** Source for [partial_function_eventual_lower_bound]: supporting
    order-dual tail infimum bound in the lower-limit formula of
    Federer 2.3.2, p. 74. *)
Definition partial_function_eventual_lower_bound (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R)) x (b : \bar R) :=
  exists N, forall n, (N <= n)%N -> forall z, partial_function_graph (f n) x z -> b <= z.

(** Source for [is_partial_function_upper_limit]: abstract upper limit in
    Federer 2.3.2, p. 74, expressed as the infimum of all eventual upper
    bounds. *)
Record is_partial_function_upper_limit (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) : Prop := {
  (** Source for [partial_function_upper_limit_domain]: Federer 2.3.2, p. 74. *)
  partial_function_upper_limit_domain : partial_function_domain g = partial_function_eventual_domain f;
  (** Source for [partial_function_upper_limit_lower]: infimum lower
      bound for the upper-limit formula in Federer 2.3.2, p. 74. *)
  partial_function_upper_limit_lower : forall x y, partial_function_graph g x y ->
    forall b, partial_function_eventual_upper_bound f x b -> y <= b;
  (** Source for [partial_function_upper_limit_greatest]: greatest
      lower bound for the same upper-limit formula, Federer 2.3.2, p. 74. *)
  partial_function_upper_limit_greatest : forall x y, partial_function_graph g x y ->
    forall b, (forall c, partial_function_eventual_upper_bound f x c -> b <= c) -> b <= y
}.

(** Source for [is_partial_function_lower_limit]: abstract lower limit in
    Federer 2.3.2, p. 74, expressed as the supremum of all eventual lower
    bounds, on the eventual domain made explicit. *)
Record is_partial_function_lower_limit (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) : Prop := {
  (** Source for [partial_function_lower_limit_domain]: Federer 2.3.2, p. 74. *)
  partial_function_lower_limit_domain : partial_function_domain g = partial_function_eventual_domain f;
  (** Source for [partial_function_lower_limit_upper]: supremum upper
      bound for the lower-limit formula in Federer 2.3.2, p. 74. *)
  partial_function_lower_limit_upper : forall x y, partial_function_graph g x y ->
    forall b, partial_function_eventual_lower_bound f x b -> b <= y;
  (** Source for [partial_function_lower_limit_least]: least upper
      bound for the same lower-limit formula, Federer 2.3.2, p. 74. *)
  partial_function_lower_limit_least : forall x y, partial_function_graph g x y ->
    forall b, (forall c, partial_function_eventual_lower_bound f x c -> c <= b) -> y <= b
}.
