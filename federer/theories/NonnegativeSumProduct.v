(** Federer (1969), 2.1.1(9)-(10), p. 53: reindexing and iterated sums, for
    nonnegative functions. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumGrouping.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_injective_image]: Federer
    2.1.1(9), p. 53; injective reindexing, a supporting singleton-
    fibre case of the grouping identity. *)
Lemma nonnegative_sum_injective_image (R : realType) (I J : choiceType)
    (A : set I) (h : I -> J) (g : J -> \bar R) :
  (forall x y, A x -> A y -> h x = h y -> x = y) ->
  (forall x, A x -> 0 <= g (h x)) ->
  nonnegative_sum (h @` A) g = nonnegative_sum A (fun x => g (h x)).
Proof.
move=> hi hg; rewrite (@nonnegative_sum_grouping R I J A (h @` A) h); last 2 first.
- by move=> x hx; exists x.
- exact hg.
apply: nonnegative_sum_ext=> y [a ha <-].
symmetry; have hmem : (A `&` [set x | h x == h a]) a by split=> //; exact: eqxx.
have he := @nonnegative_sum_single_support R I
  (A `&` [set x | h x == h a]) (fun x => g (h x)) a hmem (hg a ha).
apply: he=> x [hx /eqP hxa] hneq.
have hEq := hi x a hx ha hxa; by rewrite hEq eqxx in hneq.
Qed.

(** Source for [nonnegative_sum_product_first]: Federer 2.1.1(10), p. 53;
    sum over a product as the first iterated sum. *)
Theorem nonnegative_sum_product_first (R : realType) (I J : choiceType)
    (U : set I) (V : set J) (f : I * J -> \bar R) :
  (forall p, (U `*` V) p -> 0 <= f p) ->
  nonnegative_sum (U `*` V) f =
    nonnegative_sum U (fun u => nonnegative_sum V (fun v => f (u,v))).
Proof.
move=> hf; rewrite (@nonnegative_sum_grouping R (I * J)%type I (U `*` V) U fst f).
- apply: nonnegative_sum_ext=> u hu.
  have he : (U `*` V) `&` [set p | p.1 == u] = (fun v => (u,v)) @` V.
    apply/seteqP; split.
    + move=> [a b] [[ha hb] /= /eqP->]; by exists b.
    + move=> p [a ha <-]; by split; [split|rewrite /= eqxx].
  rewrite he; apply: nonnegative_sum_injective_image.
  + by move=> a b _ _ [].
  + move=> v hv; apply: hf; by split.
- by move=> [u v] [hu hv].
- exact hf.
Qed.

(** Source for [nonnegative_sum_product_second]: Federer
    2.1.1(10), p. 53; sum over a product as the other iterated
    sum, including empty factors. *)
Theorem nonnegative_sum_product_second (R : realType) (I J : choiceType)
    (U : set I) (V : set J) (f : I * J -> \bar R) :
  (forall p, (U `*` V) p -> 0 <= f p) ->
  nonnegative_sum (U `*` V) f =
    nonnegative_sum V (fun v => nonnegative_sum U (fun u => f (u,v))).
Proof.
move=> hf; rewrite (@nonnegative_sum_grouping R (I * J)%type J (U `*` V) V snd f).
- apply: nonnegative_sum_ext=> v hv.
  have he : (U `*` V) `&` [set p | p.2 == v] = (fun u => (u,v)) @` U.
    apply/seteqP; split.
    + move=> [a b] [[ha hb] /= /eqP->]; by exists a.
    + move=> p [a ha <-]; by split; [split|rewrite /= eqxx].
  rewrite he; apply: nonnegative_sum_injective_image.
  + by move=> a b _ _ [].
  + move=> u hu; apply: hf; by split.
- by move=> [u v] [hu hv].
- exact hf.
Qed.
