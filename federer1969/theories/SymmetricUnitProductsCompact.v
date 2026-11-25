(** Federer (1969), 1.10.5, p. 48: supporting compactness for an optimal
    finite product decomposition. The parameter set consists of m copies of
    the arbitrary norm unit ball, and the continuous product map has exactly
    the desired image. The norm is not replaced by an inner-product norm.
    Source context for mass: SymmetricUnitProducts.v; continuity and finite
    norm comparison are supporting arguments, not claims of an identical. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology
  LinearBasis GramSchmidt OrthonormalisationUP RealNormUP FiniteNormCompactness
  SymmetricAlgebra SymmetricGrading SymmetricFormIsomorphism InnerSymmetricPositivity
  SymmetricUnitProducts SymmetricProductContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [symmetric_unit_products_compact]: Federer 1.10.5,
    p. 48, compactness of products of unit-ball factors in finite
    dimension. This supports attainment of the decomposition infimum.
    The empty product and zero-dimensional ambient space are included. *)
Theorem symmetric_unit_products_compact (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (N : V -> R) (hN : is_real_norm N) n (e : 'I_n -> V) (he : is_basis e) m :
  compact (@symmetric_unit_products R V N m :
    set (inner_metric_space (@symmetric_inner_productP R V B hB m))).
Proof.
pose M := inner_metric_space hB.
pose E := inner_metric_space (@symmetric_inner_productP R V B hB m).
pose A : set ('I_m -> M) := fun u => forall i, N (u i)<=1.
pose f (u : 'I_m -> M) : E := @symmetric_tuple_component R V m [tuple u i | i<m].
have hb : compact [set x : M | N x<=1].
  exact (@finite_norm_ball_compact R V B hB N hN n e he 1).
have hA : compact A.
  exact (@tychonoff _ (fun _ : 'I_m => (Topological.clone M _))
    (fun _ => [set x : M | N x<=1]) (fun _ => hb)).
have hf : continuous f.
  have [d [hd ho]] := orthonormal_basis_exists hB he.
  exact (@symmetric_product_continuous_orthonormal R V B hB n d hd
    (orthonormalisation_orthonormal ho) m).
have heq : @symmetric_unit_products R V N m = f @` A.
  apply: funext=> x; apply: propext; split.
  - move=> [t [ht ->]]; exists (fun i => tnth t i).
    + move=> i; apply: ht; exact: mem_tnth.
    + rewrite /f; congr symmetric_tuple_component.
      apply: eq_from_tnth=> i; by rewrite tnth_mktuple.
  - move=> [u hu <-]; exists [tuple u i | i<m]; split=> // v /tnthP [i ->].
    by rewrite tnth_mktuple; exact: hu.
rewrite heq; apply: continuous_compact hA; exact: continuous_subspaceT hf.
Qed.
