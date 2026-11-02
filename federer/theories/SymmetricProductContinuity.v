(** Federer (1969), 1.10.5, p. 48: supporting continuity of the product map
    for finite-dimensional compactness. Source context and the distributive
    expansion: SymmetricWordExpansion.v. The symmetric inner product is that
    of 1.10.5, p. 47. The proof uses finite coordinate polynomials and
    general topological rules only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology
  InnerFiniteSynthesis InnerCoordinateContinuity GradedComponents SymmetricAlgebra
  SymmetricGrading SymmetricFormIsomorphism SymmetricWordExpansion InnerSymmetricPositivity
  OrthonormalFamilies LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Section Continuity.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.
Variable m : nat.
Local Notation M := (inner_metric_space hB).
Local Notation E := (inner_metric_space (@symmetric_inner_productP R V B hB m)).

(** Source for [symmetric_product_coordinate_expansion]: Federer
    1.10.5, p. 48, supporting finite-coordinate expression of
    a product of vectors. The coefficients are products of the
    corresponding coordinates of its factors. *)
Lemma symmetric_product_coordinate_expansion (u : 'I_m -> M) :
  @symmetric_tuple_component R V m [tuple u i | i<m] =
    \sum_(f : {ffun 'I_m -> 'I_n})
      (\prod_i inner_coordinate hB (e (f i)) (u i)) *:
      symmetric_tuple_component [tuple e (f i) | i<m].
Proof.
have hu i : u i = \sum_j inner_coordinate hB (e j) (u i) *: e j.
  exact: esym (@inner_finite_synthesis_coordinates R V B hB n e he ho (u i)).
apply: val_inj.
change (component_val (@symmetric_tuple_component R V m [tuple u i | i<m]) = component_val
  (\sum_(f : {ffun 'I_m -> 'I_n})
    (\prod_i inner_coordinate hB (e (f i)) (u i)) *:
    symmetric_tuple_component [tuple e (f i) | i<m])).
rewrite symmetric_tuple_componentE linear_sum.
change (@symmetric_word R V [seq u i | i <- enum 'I_m] =
  \sum_(f : {ffun 'I_m -> 'I_n}) component_val
    ((\prod_i inner_coordinate hB (e (f i)) (u i)) *:
      symmetric_tuple_component [tuple e (f i) | i<m])).
rewrite (eq_map hu) symmetric_word_expansion.
apply: eq_bigr=> f _.
change ((\prod_i inner_coordinate hB (e (f i)) (u i)) *:
  symmetric_word [seq e (f i) | i <- enum 'I_m] =
  (\prod_i inner_coordinate hB (e (f i)) (u i)) *:
  component_val (symmetric_tuple_component [tuple e (f i) | i<m])).
by rewrite symmetric_tuple_componentE.
Qed.

(** Source for [symmetric_product_continuous_orthonormal]: Federer
    1.10.5, p. 48, supporting continuity of finite products.
    An orthonormal basis expresses the map as a finite sum of
    scalar coordinate products times fixed symmetric vectors. *)
Theorem symmetric_product_continuous_orthonormal :
  continuous (fun u : 'I_m -> M => (@symmetric_tuple_component R V m [tuple u i | i<m] : E)).
Proof.
have hf : (fun u : 'I_m -> M => (@symmetric_tuple_component R V m [tuple u i | i<m] : E)) =
    (fun u : 'I_m -> M =>
      \sum_(f : {ffun 'I_m -> 'I_n})
        (\prod_i inner_coordinate hB (e (f i)) (u i)) *:
        (symmetric_tuple_component [tuple e (f i) | i<m] : E)).
  apply: funext=> u; exact: symmetric_product_coordinate_expansion.
rewrite hf; apply: continuous_big; first exact: add_continuous.
move=> f _ u; apply: continuousZ; last exact: cst_continuous.
apply: continuous_big; first exact: mul_continuous.
move=> i _ v.
apply: (@continuous_comp (Topological.clone ('I_m -> M) _)
  (Topological.clone M _) (Topological.clone R^o _)
  (fun v => v i) (inner_coordinate hB (e (f i))) v).
- exact: proj_continuous.
- exact: inner_coordinate_continuous.
Qed.
End Continuity.
