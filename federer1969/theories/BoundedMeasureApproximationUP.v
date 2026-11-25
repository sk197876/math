(** Federer (1969), 2.4.16, p. 90: bounded measurable functions gn with
    finite-measure nonzero loci, increasing absolute values, and pointwise
    limit f. Our witnesses instead keep f where |f|<=n+1 and put zero
    elsewhere; they are eventually equal to f at every point. This permitted
    variation preserves the displayed bounds and supports the same Fatou
    argument. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_bounded_measure_approximation]: abstract
    specification of the approximating sequence in Federer 2.4.16,
    p. 90, final paragraph. Eventual equality strengthens convergence;
    each value is either the original value or zero. *)
Record is_bounded_measure_approximation (R : realType) (X : choiceType)
    (mu : set X -> \bar R)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))
    (g : nat -> X -> real_norm_metric_space (scalar_absolute_value_norm R)) : Prop := {
  (** Source for [bounded_approximation_measurable]: measurable
      approximants in Federer 2.4.16, p. 90. *)
  bounded_approximation_measurable : forall n,
    is_measure_measurable_function mu (partial_function_total (g n));
  (** Source for [bounded_approximation_support]: boundedness and
      finite-measure support in Federer 2.4.16, p. 90. *)
  bounded_approximation_support : forall n, exists A : set X,
    measure_measurable mu A /\ (mu A < +oo)%E /\
    (forall x, ~ A x -> g n x=0) /\ forall x, `|g n x| <= n.+1%:R;
  (** Source for [bounded_approximation_restriction]: the
      include-or-omit witness variation described above, supporting
      the comparison step in Federer 2.4.16, p. 90. *)
  bounded_approximation_restriction : forall n x, g n x=0 \/ g n x=f x;
  (** Source for [bounded_approximation_monotone]: increasing
      absolute values in Federer 2.4.16, p. 90, final paragraph. *)
  bounded_approximation_monotone : forall n x, `|g n x| <= `|g n.+1 x|;
  (** Source for [bounded_approximation_eventually]: eventual
      equality for the chosen restriction witnesses, strengthening
      the pointwise convergence in Federer 2.4.16, p. 90. *)
  bounded_approximation_eventually : forall x, exists K, forall n,
    (K <= n)%N -> g n x=f x
}.
