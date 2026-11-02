(** Federer (1969), 2.1.1(9)-(10), p. 53: reindexing and iterated signed
    sums. Source context: NumericalSum.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial NonnegativeSum NonnegativeSumProduct
  NumericalSum NumericalSumGrouping.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [numerical_sum_injective_image]: Federer
    2.1.1(9), p. 53, singleton-fibre case; injective reindexing
    preserves both the value and the domain of a signed sum. *)
Lemma numerical_sum_injective_image (R : realType) (I J : choiceType)
    (A : set I) (h : I -> J) (g : J -> \bar R) :
  (forall x y, A x -> A y -> h x = h y -> x = y) ->
  numerical_sum (h @` A) g = numerical_sum A (fun x => g (h x)).
Proof.
move=> hi; rewrite /numerical_sum !nonnegative_sum_injective_image //.
- by move=> x _; exact: extended_negative_part_nonnegative.
- by move=> x _; exact: extended_positive_part_nonnegative.
Qed.

(** Source for [numerical_sum_product_first]: Federer 2.1.1(10), p. 53; each
    sum in the second variable is defined, and summing these actual values
    in the first variable gives the original sum. *)
Theorem numerical_sum_product_first (R : realType) (I J : choiceType)
    (U : set I) (V : set J) (f : I * J -> \bar R) z :
  numerical_sum (U `*` V) f = Some z ->
  exists g : I -> \bar R,
    (forall u, U u -> numerical_sum V (fun v => f (u,v)) = Some (g u)) /\
    numerical_sum U g = Some z.
Proof.
move=> hz; have hh : forall p, (U `*` V) p -> U p.1 by move=> p [hp _].
have [g [hg ht]] := numerical_sum_grouping hh hz.
exists g; split; last exact ht.
move=> u hu; have he : (U `*` V) `&` [set p | p.1 == u] = (fun v => (u,v)) @` V.
  apply/seteqP; split.
  - move=> [a b] [[ha hb] /= /eqP->]; by exists b.
  - move=> p [a ha <-]; by split; [split|rewrite /= eqxx].
have hi : forall a b, V a -> V b -> (u,a) = (u,b) -> a = b by move=> a b _ _ [].
have := hg u hu; by rewrite he (numerical_sum_injective_image f hi).
Qed.

(** Source for [numerical_sum_product_second]: Federer
    2.1.1(10), p. 53; the other order of iterated summation also
    has defined inner sums and gives the original value. *)
Theorem numerical_sum_product_second (R : realType) (I J : choiceType)
    (U : set I) (V : set J) (f : I * J -> \bar R) z :
  numerical_sum (U `*` V) f = Some z ->
  exists g : J -> \bar R,
    (forall v, V v -> numerical_sum U (fun u => f (u,v)) = Some (g v)) /\
    numerical_sum V g = Some z.
Proof.
move=> hz; have hh : forall p, (U `*` V) p -> V p.2 by move=> p [_ hp].
have [g [hg ht]] := numerical_sum_grouping hh hz.
exists g; split; last exact ht.
move=> v hv; have he : (U `*` V) `&` [set p | p.2 == v] = (fun u => (u,v)) @` U.
  apply/seteqP; split.
  - move=> [a b] [[ha hb] /= /eqP->]; by exists a.
  - move=> p [a ha <-]; by split; [split|rewrite /= eqxx].
have hi : forall a b, U a -> U b -> (a,v) = (b,v) -> a = b by move=> a b _ _ [].
have := hg v hv; by rewrite he (numerical_sum_injective_image f hi).
Qed.
