(** Federer (1969), 2.5.7, pp. 98–99: linear functionals bounded on the unit
    ball of the total-domain Lebesgue space. The May 1987 erratum, p. 2,
    book p. 98 lines 10–11, specifies total functions and the closed unit
    ball. These abstract laws support that step; actual Lebesgue norms are
    supplied separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import FunctionLatticeUP LatticeAdditiveFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_linear_functional_on_functions]: linearity hypothesis in
    Federer 2.5.7, p. 98, after the total-domain correction, erratum p. 2,
    book p. 98 line 10 Laws concern only L. *)
Definition is_linear_functional_on_functions (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) :=
  is_lattice_additive_functional L A /\
  forall c f, L f -> A (fun x => c * f x)=c * A f.

(** Source for [is_finite_function_seminorm]: supporting abstract form of
    the Lebesgue seminorm restricted to L in Federer 2.5.7, p. 98; its laws
    come from 2.4.12, pp. 86–87. Only values on L matter, and those are
    finite by membership. *)
Record is_finite_function_seminorm (R : realType) (X : Type)
    (L : set (X -> R)) (N : (X -> R) -> R) : Prop := {
  (** Source for [function_seminorm_nonnegative]: positivity
      of the seminorm used in Federer 2.5.7, p. 98;
      its defining law is in 2.4.12, p. 86. *)
  function_seminorm_nonnegative : forall f, L f -> 0 <= N f;
  (** Source for [function_seminorm_scale]: absolute homogeneity used to
    normalize the tests in Federer 2.5.7, pp. 98–99 *)
  function_seminorm_scale : forall c f, L f -> N (fun x => c * f x)=`|c| * N f;
  (** Source for [function_seminorm_triangle]: the seminorm
      triangle law from Federer 2.4.12, p. 86, on the
      total-domain space used in 2.5.7, p. 98. *)
  function_seminorm_triangle : forall f g, L f -> L g ->
    N (fun x => f x+g x) <= N f+N g
}.

(** Source for [functional_unit_ball_values]: exact corrected set defining M
    in Federer 2.5.7, p. 98, erratum p. 2, book p. 98 line 11: norm <= 1
    replaces norm = 1. *)
Definition functional_unit_ball_values (R : realType) (X : Type)
    (L : set (X -> R)) (A N : (X -> R) -> R) :=
  [set v : R | exists f, L f /\ N f <= 1 /\ v=`|A f|].
