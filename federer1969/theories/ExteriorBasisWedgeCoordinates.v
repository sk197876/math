(** Federer (1969), 1.7.5, pp. 32-33: each nonzero product of orthonormal
    exterior basis vectors is a signed orthonormal basis vector, with the
    sign prescribed in 1.3.4. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorBasis
  InnerExteriorIndexProducts OrthonormalFamilies ExteriorIndexSupport
  ExteriorIndices LambdaComplements OrderedBasisWords InversionCount Shuffles
  ExteriorAlgebra ExteriorGrading GradedComponents FiniteExteriorPowers
  ExteriorExpansion ExteriorHomogeneousProducts Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_basis_product_nonuniq]: Federer
    1.7.5, pp. 32-33, overlapping index sets give zero
    exterior product because a generating vector is repeated. *)
Lemma exterior_basis_product_nonuniq (R : fieldType) (V : lmodType R)
    n (e : 'I_n -> V) p q (lambda : Lambda n p) (mu : Lambda n q) :
  ~~ uniq (val lambda ++ val mu) ->
  exterior_product (e_lambda e (val lambda)) (e_lambda e (val mu)) = 0.
Proof.
move=> hu; apply: val_inj.
change (component_val (exterior_product (e_lambda e (val lambda)) (e_lambda e (val mu))) =
  component_val (0 : exterior_power V (p+q))).
rewrite exterior_productE !e_lambdaE exterior_word_cat -map_cat linear0.
exact: exterior_word_map_nonuniq hu.
Qed.

(** Source for [exterior_basis_product_ordered]: Federer
    1.7.5, pp. 32-33, sorting the disjoint concatenation
    produces the output basis vector with its permutation sign. *)
Lemma exterior_basis_product_ordered (R : fieldType) (V : lmodType R)
    n (e : 'I_n -> V) p q (lambda : Lambda n p) (mu : Lambda n q)
    (nu : Lambda n (p+q)) :
  perm_eq (val lambda ++ val mu) (val nu) ->
  exterior_product (e_lambda e (val lambda)) (e_lambda e (val mu)) =
    (-1 : R)^+(inversions (map val (val lambda ++ val mu))) *: e_lambda e (val nu).
Proof.
move=> hp; apply: val_inj.
change (component_val (exterior_product (e_lambda e (val lambda)) (e_lambda e (val mu))) =
  component_val ((-1 : R)^+(inversions (map val (val lambda ++ val mu))) *: e_lambda e (val nu))).
rewrite linearZ exterior_productE !e_lambdaE exterior_word_cat -map_cat.
have hs : sorted leq (map val (val nu)).
  have := valP nu; by rewrite ltn_sorted_uniq_leq => /andP [].
exact: exterior_index_word_order hs hp.
Qed.

(** Source for [exterior_basis_wedge_coordinate]: Federer
    1.7.5, pp. 32-33, the coefficient of e_nu in
    e_lambda wedge e_mu is its permutation sign on S(nu)
    and zero outside S(nu). *)
Theorem exterior_basis_wedge_coordinate (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : orthonormal_family B e)
    p q (lambda : Lambda n p) (mu : Lambda n q) (nu : Lambda n (p+q)) :
  exterior_inner_form h2 hB (exterior_product (e_lambda e (val lambda)) (e_lambda e (val mu)))
    (e_lambda e (val nu)) =
  if exterior_index_support lambda mu nu
  then (-1 : R)^+(inversions (map val (val lambda ++ val mu))) else 0.
Proof.
case hu : (uniq (val lambda ++ val mu)); last first.
- by rewrite (exterior_basis_product_nonuniq e (negbT hu))
    (bil0l (exterior_inner_form_bilinear h2 hB (p+q))) /exterior_index_support hu andbF.
have [rho [hr hp]] := exterior_index_union_exists hu.
rewrite (exterior_basis_product_ordered e hp) (bilZl (exterior_inner_form_bilinear h2 hB (p+q)))
  (@exterior_orthonormal_family R h2 V B hB n e he (p+q))
  /exterior_index_support hu andbT hr (inj_eq (@Lambda_set_injective n (p+q))).
change ((-1 : R)^+(inversions (map val (val lambda ++ val mu))) *
  (if rho == nu then 1 else 0) =
  if rho == nu then (-1 : R)^+(inversions (map val (val lambda ++ val mu))) else 0).
by case: (rho == nu); rewrite ?mulr1 ?mulr0.
Qed.
