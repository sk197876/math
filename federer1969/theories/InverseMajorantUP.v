(** Federer (1969), 3.1.24, pp. 239–240: specify
    the positive-order scalar majorant sequence by its printed
    initial value and recurrence. Existence and exponential
    bounds must be proved, rather than supplied as axioms. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SymmetricMultiIndices SymmetricDividedMonomials CompositionMultiIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inverse_majorant_remainder]: the remainder
    sum over T(p) in Federer 3.1.24, p. 239.
    It is expressed as the ordinary-degree-greater-than-one
    part of S(p), with a redundant zero final exponent.
    CompositionRemainderIndices.v proves that only indices below
    p occur with positive exponent. *)
Definition inverse_majorant_remainder (R:realType) (g:R) (lambda:nat->R) p:R :=
  \sum_(a:composition_indices p p |
      (1<symmetric_multi_degree (composition_indices_unbound a))%N)
    ((g^+(symmetric_multi_degree (composition_indices_unbound a)))*
      (symmetric_multi_degree (composition_indices_unbound a))`!%:R/
      (symmetric_multi_factorial (composition_indices_unbound a))%:R)*
    \prod_(i<p) lambda (val i).+1^+(composition_indices_unbound a i).

(** Source for [is_inverse_majorant_sequence]: the defining
    recurrence for lambda_1,lambda_2,... in Federer 3.1.24,
    pp. 239–240. Order zero is set to zero as an
    auxiliary convention; it never occurs in the recurrence.
    This is a predicate on a supplied sequence, not an
    assertion of its existence or an unproved project axiom. *)
Definition is_inverse_majorant_sequence (R:realType) (b g:R) (lambda:nat->R) :=
  lambda 0%N=0 /\ lambda 1%N=(b*g)^-1 /\
  forall p,(2<=p)%N -> lambda p=lambda 1%N*inverse_majorant_remainder g lambda p.
