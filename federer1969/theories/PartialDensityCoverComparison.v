(** Federer (1969), 2.4.10, p. 85: supporting pointwise comparison for a
    covering family in the density- measure argument. The sum uses the
    approximants themselves, as explained in
    MeasureNonnegativeUpperApproximation.v. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension PartialExtendedOrderLoci
  PartialFunctionSupremumUP PartialFamilyValueSelection PartialNumericalSumUP NonnegativeSum NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_density_cover_sum_order]: the pointwise covering
    inequality for upper approximants in Federer 2.4.10, p. 85. This
    includes empty covering families and partial domains without arbitrary
    default values. *)
Lemma partial_density_cover_sum_order (R : realType) (X : Type) (J : choiceType)
    (D : set J) (A : set X) (B : J -> set X)
    (h : partial_function X (extended_real_line R))
    (v : J -> partial_function X (extended_real_line R))
    (s : partial_function X (extended_real_line R)) x :
  A `<=` \bigcup_(j in D) B j -> is_partial_function_numerical_sum D v s ->
  (forall j, D j -> forall t y, partial_function_graph (v j) t y -> 0 <= y) ->
  partial_extended_nonnegative_locus h x ->
  (forall j, D j -> partial_extended_le_locus
    (partial_function_zero_extension (0 : extended_real_line R) (B j) h) (v j) x) ->
  partial_extended_le_locus (partial_function_zero_extension (0 : extended_real_line R) A h) s x.
Proof.
move=> hcover hs hp [z [hz hzpos]] hbound.
have hd : partial_function_common_domain D v x.
  move=> j hj; have [a [b [_ [hb _]]]] := hbound j hj; by exists b.
have [u hu] := @partial_family_common_values_exists R X J D v x hd.
have hup j : D j -> 0 <= u j by move=> hj; exact: hp j hj x (u j) (hu j hj).
have hsum : partial_function_graph s x (nonnegative_sum D u).
  apply: (hs x _).2; exists u; split=> //; exact: numerical_sum_nonnegative hup.
have [hA|hA] := pselect (A x).
- exists z,(nonnegative_sum D u); split.
  + apply/partial_function_zero_extension_graph; left; by split.
  + split=> //; have [j hj hxj] := hcover x hA.
    have [a [b [ha [hb hab]]]] := hbound j hj.
    have hah : partial_function_graph h x a.
      exact ((@partial_function_zero_extension_on X (extended_real_line R) 0 (B j) h x a hxj).1 ha).
    have eza := partial_function_single_valued hz hah.
    have eub := partial_function_single_valued (hu j hj) hb.
    apply: le_trans _ (@nonnegative_sum_term R J D u j hj).
    by rewrite eza eub.
- exists 0,(nonnegative_sum D u); split.
  + apply/partial_function_zero_extension_graph; right; by split.
  + split=> //; exact: nonnegative_sum_nonnegative.
Qed.
