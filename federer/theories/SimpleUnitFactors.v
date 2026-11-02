(** Federer (1969), 1.8.1, p. 38: supporting parametrisation of the simple
    unit ball for its compactness. Here the domain is enlarged to all tuples
    of factors of norm at most one: Hadamard's bound keeps their products in
    S, and the same orthonormal factorisation proves surjectivity. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  ExteriorNorm ExteriorGrading FiniteExteriorPowers SimpleUnitBall
  SimpleElementary SimpleOrthonormalFactor ExteriorProductFactors
  ExteriorHadamardBound OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Factors.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.
Hypothesis hm : (0 < m)%N.

(** Source for [unit_factors_simple_unit_ball]: Federer 1.8.1,
    p. 38, supporting image inclusion for compactness of S, by
    the product-norm estimate in 1.7.5, p. 32. *)
Lemma unit_factors_simple_unit_ball (u : 'I_m -> V) :
  (forall i, inner_norm hB (u i) <= 1) ->
  simple_unit_ball h2 hB (e_lambda u (ord_tuple m)).
Proof.
move=> hu; split; first exact: product_simple.
apply: (le_trans (exterior_product_norm_bound h2 hB u)).
have hp : (\prod_i inner_norm hB (u i)) <= \prod_(i : 'I_m) (1 : R).
  apply: ler_prod => i _; apply/andP; split; first exact: inner_norm_nonnegative.
  exact: hu.
have h1 : (\prod_(i : 'I_m) (1 : R)) = 1 by apply: big1.
by rewrite h1 in hp.
Qed.

(** Source for [simple_unit_ball_factors]: Federer 1.8.1, p. 38, supporting
    surjectivity of the compact parameter set Put the scalar of an
    orthonormal factorisation into the first factor. The zero vector is
    handled separately, including when the degree exceeds the ambient
    dimension. *)
Theorem simple_unit_ball_factors x : simple_unit_ball h2 hB x ->
  exists u : 'I_m -> V, (forall i, inner_norm hB (u i) <= 1) /\
    x = e_lambda u (ord_tuple m).
Proof.
move=> [hs hn]; have [->|hx] := eqVneq x 0.
- exists (fun _ => 0); split.
  + move=> i; by rewrite inner_norm0.
  + symmetry; apply: (@exterior_product_zero_entry R (Choice.clone 'I_m _) V
      (fun _ => 0) m (ord_tuple m) (Ordinal hm)) => //.
    exact: mem_enum.
have [e [c [ho [hc he]]]] := simple_orthonormal_factor h2 hB hx hs.
have hcn : `|c| <= 1.
  by rewrite he exterior_norm_scale (orthonormal_product_unit_norm h2 hB ho) mulr1 in hn.
pose j : 'I_m := Ordinal hm.
pose a (i : 'I_m) := if i == j then c else 1.
exists (fun i => a i *: e i); split.
- move=> i; rewrite inner_normZ (orthonormal_norm1 hB ho) mulr1 /a.
  case: ifP => _ //; by rewrite normr1.
- rewrite exterior_product_scaled_family.
  have ha : \prod_i a i = c.
    rewrite (bigD1 j) // /a eqxx.
    have hz : \prod_(i | i != j) (if i == j then c else 1) = 1.
      apply: big1 => i hij; by rewrite (negbTE hij).
    rewrite hz; change (c * 1 = c); by rewrite mulr1.
  by rewrite ha.
Qed.
End Factors.
