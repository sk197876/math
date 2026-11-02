(** Federer (1969), 2.1.1(9), p. 53: grouping a numerical sum by the fibres
    of a map, here for nonnegative terms. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport
  NonnegativeSumRestriction NonnegativeSumFiniteFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_predicate]: Federer 2.1.1(3),
    p. 52; supporting zero extension for a Boolean predicate,
    equivalent to intersecting the summation set with its truth set. *)
Lemma nonnegative_sum_predicate (R : realType) (I : choiceType)
    (A : set I) (P : pred I) (f : I -> \bar R) :
  nonnegative_sum A (fun x => if P x then f x else 0) =
  nonnegative_sum (A `&` [set x | P x]) f.
Proof.
rewrite -nonnegative_sum_restrict; apply: nonnegative_sum_ext=> x _.
have he : (x \in [set x | P x]) = P x.
  apply/idP/idP; [exact: set_mem | exact: mem_set].
by rewrite he.
Qed.

(** Source for [nonnegative_finite_single_term]: Federer
    2.1.1(1), p. 52; supporting finite sum of a single supported
    term, including a point outside the indexing set. *)
Lemma nonnegative_finite_single_term (R : realType) (J : choiceType)
    (C : {fset J}) z (a : \bar R) : 0 <= a ->
  (\sum_(y <- C) (if z == y then a else 0)) = if z \in C then a else 0.
Proof.
move=> ha; rewrite -nonnegative_sum_finite; last first.
  by move=> y _; case: ifP=> _.
have [hz|hz] := boolP (z \in C).
- have he := @nonnegative_sum_single_support R J [set y | y \in C]
      (fun y => if z == y then a else 0) z hz.
  rewrite eqxx in he; apply: he ha _ => y _ hy.
  by rewrite eq_sym (negbTE hy).
- apply: nonnegative_sum_zero=> y hy.
  have hzy : z != y by apply/negP=> /eqP he; move: hy; rewrite /= -he (negbTE hz).
  by rewrite (negbTE hzy).
Qed.

(** Source for [nonnegative_sum_grouping]: Federer 2.1.1(9), p. 53,
    nonnegative case; grouping by every fibre of h preserves the sum. The
    codomain and the summation set may be uncountable. *)
Theorem nonnegative_sum_grouping (R : realType) (I J : choiceType)
    (A : set I) (Y : set J) (h : I -> J) (f : I -> \bar R) :
  (forall x, A x -> Y (h x)) -> (forall x, A x -> 0 <= f x) ->
  nonnegative_sum A f = nonnegative_sum Y
    (fun y => nonnegative_sum (A `&` [set x | h x == y]) f).
Proof.
move=> hh hf; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: nonnegative_sum_least=> B hB.
  rewrite (partition_big_imfset _ h).
  apply: le_trans (_ : (\sum_(y <- [fset h x | x in B])
    nonnegative_sum (A `&` [set x | h x == y]) f) <= _).
  + apply: lee_sum=> y _; rewrite big_fset_condE.
    apply: nonnegative_sum_upper=> x; rewrite inE => /andP[hx hy].
    split; [exact: hB | exact hy].
  + apply: nonnegative_sum_upper=> y /imfsetP[x hx ->]; exact: hh (hB x hx).
- apply: nonnegative_sum_least=> C hC.
  have he : (\sum_(y <- C) nonnegative_sum (A `&` [set x | h x == y]) f) =
      nonnegative_sum A (fun x => \sum_(y <- C) (if h x == y then f x else 0)).
    rewrite nonnegative_sum_finite_family; last first.
      move=> y hy x hx; case: ifP=> _; [exact: hf | exact: lexx].
    apply: eq_bigr=> y _; by rewrite nonnegative_sum_predicate.
  rewrite he; apply: nonnegative_sum_mono=> x hx.
  rewrite nonnegative_finite_single_term; last exact: hf.
  by case: ifP=> _; [exact: lexx | exact: hf].
Qed.
