(** Federer (1969), 2.5.10, p. 101: the signed sum over each projection
    fibre, with the numerical summation convention of 2.1.1(4), p. 52. It is
    defined precisely when the difference of the two nonnegative sums is
    defined; no value is assigned to infinity minus infinity. The
    implementation uses existing partial arithmetic and sealed nonnegative
    sums. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionBasic PartialExtendedArithmetic NumericalSum FibreNonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [fibre_numerical_integrand]: the inner
    signed fibre sum in Federer 2.5.10, p. 101,
    expressed by its positive and negative sums according
    to 2.1.1(4), p. 52. *)
Definition fibre_numerical_integrand (R : realType) (X : choiceType) (Y : Type)
    (p : X -> Y) (f : X -> \bar R) :=
  partial_extended_function_subtract
    (partial_function_total (fun y =>
      (fibre_nonnegative_sum p (fun x => extended_positive_part (f x)) y : extended_real_line R)))
    (partial_function_total (fun y =>
      (fibre_nonnegative_sum p (fun x => extended_negative_part (f x)) y : extended_real_line R))).

(** Source for [fibre_numerical_integrand_graph]: exact
    numerical-sum specification of the integrand printed
    in Federer 2.5.10, p. 101. The graph includes
    a value z exactly when the sum over p^{-1}{y}
    exists and equals z, using 2.1.1(4), p. 52. *)
Lemma fibre_numerical_integrand_graph (R : realType) (X : choiceType) (Y : Type)
    (p : X -> Y) (f : X -> \bar R) y z :
  partial_function_graph (fibre_numerical_integrand p f) y z <->
  numerical_sum [set x | p x=y] f=Some z.
Proof.
rewrite /fibre_numerical_integrand /partial_extended_function_subtract partial_extended_function_add_graph.
split.
- move=> [a [b [ha [[c [hc hb]] he]]]].
  change (fibre_nonnegative_sum p (fun x => extended_positive_part (f x)) y=a) in ha.
  change (fibre_nonnegative_sum p (fun x => extended_negative_part (f x)) y=c) in hc.
  change (extended_add (fibre_nonnegative_sum p (fun x => extended_positive_part (f x)) y)
    (-fibre_nonnegative_sum p (fun x => extended_negative_part (f x)) y)=Some z).
  by rewrite ha hc hb.
- move=> he.
  exists (fibre_nonnegative_sum p (fun x => extended_positive_part (f x)) y),
    (-fibre_nonnegative_sum p (fun x => extended_negative_part (f x)) y).
  split=> //; split; last exact he.
  exists (fibre_nonnegative_sum p (fun x => extended_negative_part (f x)) y); by split.
Qed.
