(** Federer (1969), 1.7.5, p. 32: the vanishing and triangular cases of the
    permutation formula. Empty products are included. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorProducts
  FiniteExteriorPowers TriangularPermutation InversionCount PermutationDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_fold_product_zero]: Federer 1.7.5,
    p. 32, supporting finite-product fact: a zero factor makes
    the scalar product zero. *)
Lemma scalar_fold_product_zero (R : pzRingType) (s : seq R) :
  0 \in s -> foldr ( *%R) 1 s = 0.
Proof.
elim: s => [|x s ih] //=; move/orP=> [/eqP <-|hs].
- exact: mul0r.
- by rewrite (ih hs) mulr0.
Qed.
Section Triangular.
Variable R : realFieldType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.
Variables e f : 'I_m -> V.

(** Source for [exterior_inner_orthogonal_factor]: Federer
    1.7.5, p. 32, first paragraph after the definition: if one
    factor of the second product is orthogonal to every factor
    of the first, the products have zero inner product. *)
Theorem exterior_inner_orthogonal_factor (i : 'I_m) :
  (forall j, B (e j) (f i) = 0) ->
  exterior_inner_form h2 hB (e_lambda e (ord_tuple m))
    (e_lambda f (ord_tuple m)) = 0.
Proof.
move=> ho; rewrite exterior_inner_product_permutations; apply: big1 => sigma _.
suff hz : foldr ( *%R) 1 [seq B (e (sigma j)) (f j) | j <- enum 'I_m] = 0.
  by rewrite hz mulr0.
apply: scalar_fold_product_zero; apply/mapP; exists i; first exact: mem_enum.
by rewrite ho.
Qed.

(** Source for [exterior_inner_triangular]: Federer 1.7.5,
    p. 32, the displayed product of v_i dot w_i: when all
    entries below the diagonal vanish, only the identity permutation
    contributes. This supports the orthogonal residual calculation. *)
Theorem exterior_inner_triangular :
  (forall i j : 'I_m, (j < i)%N -> B (e j) (f i) = 0) ->
  exterior_inner_form h2 hB (e_lambda e (ord_tuple m))
    (e_lambda f (ord_tuple m)) = foldr ( *%R) 1 [seq B (e i) (f i) | i <- enum 'I_m].
Proof.
move=> ht; rewrite exterior_inner_product_permutations (bigD1 1%g) //=.
have hz : (\sum_(sigma : 'S_m | sigma != 1%g) FedererPermutation.index R sigma *
    foldr ( *%R) 1 [seq B (e (sigma i)) (f i) | i <- enum 'I_m]) = 0.
  apply: big1 => sigma hs; have [i hi] := permutation_lower hs.
  have hp : foldr ( *%R) 1 [seq B (e (sigma j)) (f j) | j <- enum 'I_m] = 0.
    apply: scalar_fold_product_zero; apply/mapP; exists i; first exact: mem_enum.
    by rewrite (ht i (sigma i) hi).
  by rewrite hp mulr0.
rewrite hz addr0 (index_one h2) mul1r.
congr (foldr _ _ _); apply: eq_map => i; by rewrite perm1.
Qed.
End Triangular.
