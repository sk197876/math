(** Federer (1969), 2.4.16, p. 90: a countable finite- measure cover
    supplies a positive integrable weight on the nonzero locus, used to
    preserve the sign in the dual supremum. The abstract helper below
    permits overlapping and null cover pieces and specifies bounds by one
    for both the function and its integral. It supports all norm cases,
    including the sign restriction when the input norm is infinite, which. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionBasic MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_positive_integrable_weight]: abstract supporting
    weight specification for Federer 2.4.16, p. 90, first two displays.
    Positivity on A is pointwise, including measure-zero parts of A. *)
Record is_positive_integrable_weight (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A : set X)
    (w : X -> real_norm_metric_space (scalar_absolute_value_norm R)) : Prop := {
  (** Source for [positive_weight_nonnegative]: nonnegative
      summands in the weighted test of Federer 2.4.16, p. 90. *)
  positive_weight_nonnegative : forall x, 0 <= w x;
  (** Source for [positive_weight_bound]: supporting pointwise
      bound by one for a reusable unit test, Federer 2.4.16, p. 90. *)
  positive_weight_bound : forall x, w x <= 1;
  (** Source for [positive_weight_support]: exact positivity on
      the specified locus, supporting sign(u)=sign(f), Federer 2.4.16, p. 90. *)
  positive_weight_support : forall x, (0 < w x <-> A x);
  (** Source for [positive_weight_integrable]: finite integral at
      most one, supporting the corrected test ball in Federer 2.4.16,
      pp. 89–90 and erratum p. 2, book p. 89 line 19. *)
  positive_weight_integrable : exists b : R, 0 <= b /\ b <= 1 /\
    is_measure_integral mu (partial_function_total (fun x => ((w x)%:E : extended_real_line R))) b%:E
}.
