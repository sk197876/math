(** Federer (1969), 1.7.6, p. 34: positivity of the top-source exterior
    operator norm is equivalent to injectivity. The argument uses the book's
    product-independence criterion. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP LinearBasis FiniteBasisCriterion
  FiniteIndependence FiniteBasisComparison IndependentMap IndependentProducts ExteriorHadamardBound
  ExteriorOperatorEstimate ExteriorOperatorNorm OperatorNormLaws
  ExteriorDeterminant ExteriorGrading ExteriorMaps FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [top_exterior_nonzero_iff_injective]: Federer
    1.7.6, p. 34, supporting algebraic criterion: the top-source
    exterior map is nonzero exactly when the original map is injective. *)
Theorem top_exterior_nonzero_iff_injective (R : fieldType)
    (h2 : (1+1 : R) != 0) (V U : lmodType R)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> U}) :
  (exists x : exterior_power V n, exterior_power_map f n x != 0) <-> injective f.
Proof.
pose t := @top_vector R n V b.
have ht : exterior_power_map f n t = e_lambda (fun i => f (b i)) (ord_tuple n).
  exact: exterior_map_indexed_product.
split.
- move=> [x hx].
  have hn : exterior_power_map f n t != 0.
    apply/eqP=> hz.
    have hzero : exterior_power_map f n x = 0.
      rewrite (@top_expansion R h2 n V b hb x) linearZ.
      change ((@top_coordinate R h2 n V b hb x : R) *: exterior_power_map f n t = 0).
      by rewrite hz scaler0.
    by rewrite hzero eqxx in hx.
  rewrite ht in hn.
  exact (@independent_basis_image_injective R V U n b hb f
    (@exterior_product_nonzero_independent R U n (fun i => f (b i)) hn)).
- move=> hi; exists t; rewrite ht.
  apply: (@independent_product_nonzero R h2 U n (fun i => f (b i))).
  exact (@finite_independent_map R (Finite.clone 'I_n _) V U f b hi (finite_basis_independent hb)).
Qed.

(** Source for [top_exterior_norm_positive_iff_injective]: Federer
    1.7.6, p. 34, ||exterior_n f|| > 0 iff f is a
    monomorphism, where n is the dimension of its source. *)
Theorem top_exterior_norm_positive_iff_injective (R : realType)
    (h2 : (1+1 : R) != 0) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> U}) :
  0 < exterior_operator_norm h2 hB hC hb f n <-> injective f.
Proof.
apply: iff_trans (operator_norm_positive_iff (exterior_operator_normP h2 hB hC hb f n)) _.
exact (@top_exterior_nonzero_iff_injective R h2 V U n b hb f).
Qed.
