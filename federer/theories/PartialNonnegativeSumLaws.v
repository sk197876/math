(** Federer (1969), 2.4.8, p. 84: nonnegative pointwise sums are defined on
    the common domain and may take positive infinity. The empty family's sum
    is the total zero function. These are consequences of the abstract graph
    specification and the numerical sums of 2.1.1, p. 52. Source context:
    PartialNumericalSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionSupremumUP
  NonnegativeSum NumericalSum PartialNumericalSumUP PartialFamilyValueSelection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_nonnegative_sum_domain]: exact common
    domain of the nonnegative sum in Federer 2.4.8, p. 84. *)
Lemma partial_nonnegative_sum_domain (R : realType) (X : Type) (J : choiceType)
    (D : set J) (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  is_partial_function_numerical_sum D f g ->
  (forall j, D j -> forall x y, partial_function_graph (f j) x y -> 0 <= y) ->
  partial_function_domain g = partial_function_common_domain D f.
Proof.
move=> hg hp; apply/seteqP; split=> x.
- move=> [z hz]; have [u [hu _]] := (hg x z).1 hz.
  move=> j hj; exists (u j); exact: hu j hj.
- move=> hx; have [u hu] := @partial_family_common_values_exists R X J D f x hx.
  exists (nonnegative_sum D u); apply: (hg x _).2; exists u; split=> //.
  apply: numerical_sum_nonnegative=> j hj; exact: hp j hj x (u j) (hu j hj).
Qed.

(** Source for [partial_nonnegative_sum_nonnegative]: the
    sum in Federer 2.4.8, p. 84, is nonnegative
    at every point of its domain. *)
Lemma partial_nonnegative_sum_nonnegative (R : realType) (X : Type) (J : choiceType)
    (D : set J) (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  is_partial_function_numerical_sum D f g ->
  (forall j, D j -> forall x y, partial_function_graph (f j) x y -> 0 <= y) ->
  forall x z, partial_function_graph g x z -> 0 <= z.
Proof.
move=> hg hp x z hz; have [u [hu hs]] := (hg x z).1 hz.
have hpu j : D j -> 0 <= u j by move=> hj; exact: hp j hj x (u j) (hu j hj).
rewrite (numerical_sum_nonnegative hpu) in hs; case: hs=> <-; exact: nonnegative_sum_nonnegative.
Qed.

(** Source for [partial_numerical_sum_empty_graph]: empty-family
    convention for Federer 2.4.8, p. 84, from
    numerical summation in 2.1.1, p. 52. *)
Lemma partial_numerical_sum_empty_graph (R : realType) (X : Type) (J : choiceType)
    (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  is_partial_function_numerical_sum set0 f g ->
  forall x z, partial_function_graph g x z <-> z = 0.
Proof.
move=> hg x z; rewrite (hg x z); split.
- move=> [u [_ hs]]; rewrite numerical_sum_empty in hs; by case: hs=> <-.
- move=> ->; exists (fun _ => 0); split; first by move=> j [].
  exact: numerical_sum_empty.
Qed.
