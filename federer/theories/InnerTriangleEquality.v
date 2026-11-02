(** Federer (1969), 2.4.15, p. 89, bracketed inner-product equality
    criterion, supported by the strict triangle inequality in 1.7.1, p. 28. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import RealNormUP InnerProductUP InnerNormUP InnerNorm
  InnerNormInequalities IndependentPair DependentPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_positive_triangle_coefficient]: scalar support
    for Federer 2.4.15, p. 89: equality in the triangle
    inequality for a real coefficient and one forces that coefficient
    to be nonnegative. This is not a separately numbered book claim. *)
Lemma real_positive_triangle_coefficient (R : realFieldType) (t : R) :
  `|t+1| = `|t|+1 -> 0 <= t.
Proof.
move=> he.
have hh := congr1 (fun z : R => z ^+ 2) he.
rewrite -normrX ger0_norm ?sqr_ge0 // !sqrrD -normrX
  (ger0_norm (sqr_ge0 t)) !mulr1 in hh.
have hd : t *+ 2 = `|t| *+ 2.
  apply: (addrI (t ^+ 2)); apply: (addIr (1 ^+ 2)); exact hh.
have h2 : (2:R) != 0 by rewrite pnatr_eq0.
rewrite -[t *+ 2]mulr_natr -[`|t| *+ 2]mulr_natr in hd.
have ht : t = `|t| by apply: (mulIf h2); exact hd.
by rewrite ht normr_ge0.
Qed.

(** Source for [inner_triangle_positive_multiple]: pointwise support
    for the bracketed assertion in Federer 2.4.15, p. 89.
    With the second vector nonzero, equality in the inner-product
    triangle inequality forces a nonnegative scalar multiple. The norm
    is supplied by its abstract laws, not a coordinate construction. *)
Lemma inner_triangle_positive_multiple (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (N : V -> R) (hN : is_real_norm N) (hBN : is_inner_norm B N) (x y : V) :
  y != 0 -> N (x+y)=N x+N y -> exists t : R, 0 <= t /\ x=t *: y.
Proof.
move=> hy he.
have hcanon := @inner_norm_unique R V B N (inner_norm hB) hBN (inner_norm_laws hB).
have hdep : ~ independent_pair x y.
  move=> hi; have hh := @inner_norm_triangle_strict R V B hB x y hi.
  by rewrite -!hcanon he ltxx in hh.
have [hy0|[t ht]] := (proj1 (dependent_pair_cases x y)) hdep.
  by move: hy; rewrite hy0 eqxx.
exists t; split; last exact ht.
have hny : N y != 0 by rewrite (real_norm_zero_test hN.1 hN.2).
have hsum : x+y=(t+1) *: y by rewrite scalerDl scale1r ht.
rewrite hsum ht !(real_seminorm_scale hN.1) in he.
have he' : `|t+1|*N y=(`|t|+1)*N y by rewrite mulrDl mul1r; exact he.
have hs : `|t+1| = `|t|+1 by apply: (mulIf hny); exact he'.
exact: real_positive_triangle_coefficient hs.
Qed.
