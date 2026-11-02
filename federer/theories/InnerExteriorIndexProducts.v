(** Federer (1969), 1.7.5, pp. 32-33: orthonormal coordinate products used
    in the wedge norm estimates. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorProducts
  OrthonormalFamilies FiniteExteriorPowers ExteriorAlgebra GradedComponents
  ExteriorGrading SharedIndices CovectorProducts InversionCount PermutationDeterminant
  ExteriorExpansion ExteriorHomogeneousProducts Bilinear ScalarCoefficients
  ExteriorIndices SimpleAdaptedBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_basis_product_cat]: Federer
    1.7.5, p. 32, supporting multiplication of two indexed
    exterior products by concatenating their tuples. *)
Lemma exterior_basis_product_cat (R : fieldType) (I : choiceType)
    (V : lmodType R) (e : I -> V) p q (s : p.-tuple I) (t : q.-tuple I) :
  exterior_product (e_lambda e s) (e_lambda e t) = e_lambda e (cat_tuple s t).
Proof.
apply: val_inj; change (component_val (exterior_product (e_lambda e s) (e_lambda e t)) =
  component_val (e_lambda e (cat_tuple s t))).
by rewrite exterior_productE !e_lambdaE exterior_word_cat -map_cat.
Qed.

Section Orthonormal.
Variable R : realFieldType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : orthonormal_family B e.

(** Source for [exterior_orthonormal_index_permutations]:
    Federer 1.7.5, pp. 31-32, the permutation formula for
    arbitrary ordered selections from an orthonormal family, including
    repeated indices. It reduces every scalar factor to a Kronecker delta. *)
Lemma exterior_orthonormal_index_permutations m (s t : m.-tuple 'I_n) :
  exterior_inner_form h2 hB (e_lambda e t) (e_lambda e s) =
    \sum_(sigma : 'S_m) FedererPermutation.index R sigma *
      (if all (fun i => tnth s i == tnth t (sigma i)) (enum 'I_m) then 1 else 0).
Proof.
rewrite (indexed_productE e t) (indexed_productE e s)
  exterior_inner_product_permutations.
apply: eq_bigr => sigma _; congr (_ * _).
transitivity (foldr (fun x y : R => x*y) 1 [seq if tnth s i == tnth t (sigma i) then 1 else 0 | i <- enum 'I_m]).
- congr (foldr _ _ _); apply: eq_map => i; by rewrite he eq_sym.
- exact: scalar_delta_product.
Qed.

(** Source for [exterior_orthonormal_products_shared]: Federer
    1.7.5, p. 32, supporting diagonalisation: adjoining the
    same increasing product preserves orthogonality, and the squared
    length is one precisely when the index sets are disjoint. *)
Lemma exterior_orthonormal_products_shared p q
    (lambda mu : Lambda n p) (kappa : Lambda n q) :
  exterior_inner_form h2 hB
    (exterior_product (e_lambda e (val mu)) (e_lambda e (val kappa)))
    (exterior_product (e_lambda e (val lambda)) (e_lambda e (val kappa))) =
    if (lambda == mu) && uniq (val lambda ++ val kappa) then 1 else 0.
Proof.
rewrite !exterior_basis_product_cat.
case hu : (uniq (val lambda ++ val kappa)); last first.
- have hz : e_lambda e (cat_tuple (val lambda) (val kappa)) = 0.
    apply: val_inj; change (component_val (e_lambda e (cat_tuple (val lambda) (val kappa))) =
      component_val (0 : exterior_power V (p+q))).
    rewrite e_lambdaE linear0; exact: exterior_word_map_nonuniq (negbT hu).
  by rewrite hz (bil0r (exterior_inner_form_bilinear h2 hB (p+q))) andbF.
rewrite exterior_orthonormal_index_permutations andbT.
under eq_bigr do rewrite (@Lambda_shared_delta n p q lambda mu kappa _ hu).
case hm : (lambda == mu).
- rewrite (bigD1 1%g) //= eqxx (index_one h2) mul1r.
  have hz : (\sum_(sigma : 'S_(p+q) | sigma != 1%g)
    FedererPermutation.index R sigma * (if sigma == 1%g then 1 else 0)) = 0.
    apply: big1 => sigma hs; by rewrite (negbTE hs) mulr0.
  by rewrite hz addr0.
- apply: big1 => sigma _; exact: mulr0.
Qed.
End Orthonormal.
