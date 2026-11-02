(** Federer (1969), 2.4.12, p. 86, opening paragraph: seminorms may take
    positive infinity and use 0 times infinity = 0. This specification
    retains that convention, unlike the real-valued specification previously
    needed in 1.10.5. Federer's erratum p. 1, book p. 86 lines 26–27 and
    bottom, requires total functions for the vector-space seminorm claim. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [is_extended_seminorm]: direct specification of
    Federer 2.4.12, p. 86, first displayed laws.
    Absolute homogeneity uses the distinguished total product,
    assigning zero to zero times infinity. *)
Record is_extended_seminorm (R : realType) (V : lmodType R)
    (N : V -> \bar R) : Prop := {
  (** Source for [extended_seminorm_nonnegative]: first inequality
      in the seminorm definition of Federer 2.4.12, p. 86. *)
  extended_seminorm_nonnegative : forall x, 0 <= N x;
  (** Source for [extended_seminorm_scale]: absolute homogeneity
      in Federer 2.4.12, p. 86, with zero times infinity zero. *)
  extended_seminorm_scale : forall (c : R) x, N (c *: x)%R = `|c|%:E * N x;
  (** Source for [extended_seminorm_triangle]: subadditivity in
      the defining display of Federer 2.4.12, p. 86. *)
  extended_seminorm_triangle : forall x y, N (x+y)%R <= N x + N y
}.
