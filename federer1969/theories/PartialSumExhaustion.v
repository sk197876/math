(** Federer (1969), 2.4.8, p. 84: finite nonnegative partial sums increase
    to the pointwise full sum. The increasing finite exhaustion includes
    every index, so the eventual domain of the finite sums is exactly the
    common domain of all summands. This supplies the abstract lower limit
    needed to apply 2.4.7. Source context: PartialNumericalSumUP.v and
    CountableFiniteExhaustionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBoundsUP ExtendedLowerLimitUP
  ExtendedIncreasingLimitSupremum PartialFunctionUP PartialFunctionSupremumUP PartialFunctionLimitExtremaUP
  NonnegativeSum NumericalSum PartialNumericalSumUP PartialNumericalSum PartialNonnegativeSumLaws
  PartialFiniteNumericalSum CountableFiniteExhaustionUP FiniteExhaustionSumLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_sum_exhaustion_eventual_domain]: exact
    domain identity for the finite-sum approximation supporting
    Federer 2.4.8, p. 84. *)
Lemma partial_sum_exhaustion_eventual_domain (R : realType) (X : Type) (J : choiceType)
    (D : set J) (C : nat -> {fset J}) (f : J -> partial_function X (extended_real_line R)) :
  is_countable_finite_exhaustion D C ->
  (forall j, D j -> forall x y, partial_function_graph (f j) x y -> 0 <= y) ->
  partial_function_eventual_domain
    (fun n => partial_function_numerical_sum [set j | j \in C n] f) = partial_function_common_domain D f.
Proof.
move=> hC hp.
have hdom n : partial_function_domain (partial_function_numerical_sum [set j | j \in C n] f) =
    partial_function_common_domain [set j | j \in C n] f.
  apply: (partial_nonnegative_sum_domain (partial_function_numerical_sum_laws _ f))=> j hj.
  exact: hp j (@finite_exhaustion_subset J D C hC n j hj).
apply/seteqP; split=> x.
- move=> [N hN] j hj; have [m hm] := @finite_exhaustion_cover J D C hC j hj.
  have hx := hN (maxn N m) (leq_maxl N m); rewrite hdom in hx.
  have hjbig := (fsubsetP (@finite_exhaustion_increasing J D C hC m (maxn N m) (leq_maxr N m))) j hm.
  exact (hx j hjbig).
- move=> hx; exists 0%N=> n _; rewrite hdom=> j hj.
  exact: hx j (@finite_exhaustion_subset J D C hC n j hj).
Qed.

(** Source for [partial_sum_exhaustion_scalar_values]: supporting
    scalar lower-limit law for the finite-sum approximation in
    Federer 2.4.8, p. 84, by 2.1.1(13), p. 53. *)
Lemma partial_sum_exhaustion_scalar_values (R : realType) (X : Type) (J : choiceType)
    (D : set J) (C : nat -> {fset J}) (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  is_countable_finite_exhaustion D C -> is_partial_function_numerical_sum D f g ->
  (forall j, D j -> forall x y, partial_function_graph (f j) x y -> 0 <= y) ->
  forall x z, partial_function_graph g x z -> exists a : nat -> \bar R,
    (forall n, partial_function_graph (partial_function_numerical_sum [set j | j \in C n] f) x (a n)) /\
    is_extended_lower_limit a z.
Proof.
move=> hC hg hp x z hz; have [u [hu hs]] := (hg x z).1 hz.
have hu0 j : D j -> 0 <= u j by move=> hj; exact: hp j hj x (u j) (hu j hj).
have hval : nonnegative_sum D u = z.
  rewrite (numerical_sum_nonnegative hu0) in hs; by case: hs.
exists (fun n => \sum_(j <- C n) u j); split.
- move=> n.
  have hpC j : j \in C n -> forall x y, partial_function_graph (f j) x y -> 0 <= y.
    move=> hj; exact: hp j (@finite_exhaustion_subset J D C hC n j hj).
  apply: (partial_numerical_finite_sum_graph (partial_function_numerical_sum_laws _ f) hpC x _).2.
  exists u; split=> // j hj; exact: hu j (@finite_exhaustion_subset J D C hC n j hj).
- apply: extended_increasing_limit_lower_limit_laws.
  have h := finite_exhaustion_nonnegative_sum_limit hC hu0; by rewrite hval in h.
Qed.

(** Source for [partial_sum_exhaustion_lower_limit]: the full
    pointwise nonnegative sum of Federer 2.4.8, p. 84,
    is the abstract lower limit of its finite partial sums,
    with exact agreement of their domains. *)
Lemma partial_sum_exhaustion_lower_limit (R : realType) (X : Type) (J : choiceType)
    (D : set J) (C : nat -> {fset J}) (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  is_countable_finite_exhaustion D C -> is_partial_function_numerical_sum D f g ->
  (forall j, D j -> forall x y, partial_function_graph (f j) x y -> 0 <= y) ->
  is_partial_function_lower_limit (fun n => partial_function_numerical_sum [set j | j \in C n] f) g.
Proof.
move=> hC hg hp; constructor.
- rewrite (partial_nonnegative_sum_domain hg hp).
  symmetry; exact: partial_sum_exhaustion_eventual_domain hC hp.
- move=> x z hz b [N hN].
  have [a [ha hl]] := @partial_sum_exhaustion_scalar_values R X J D C f g hC hg hp x z hz.
  apply: (extended_lower_limit_eventual_bound hl); exists N=> n hn.
  exact: hN n hn (a n) (ha n).
- move=> x z hz b hb.
  have [a [ha hl]] := @partial_sum_exhaustion_scalar_values R X J D C f g hC hg hp x z hz.
  apply: (extended_real_supremum_least hl)=> c [N hN]; apply: hb.
  exists N=> n hn y hy; have he := partial_function_single_valued (ha n) hy.
  rewrite -he; exact: hN n hn.
Qed.
