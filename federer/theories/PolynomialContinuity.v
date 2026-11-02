(** Federer (1969), 2.6.5, p. 120: polynomial zero sets are measurable for
    the application of Fubini because finite-dimensional polynomial
    functions are continuous. This supporting argument uses the
    symmetric-form representation of 1.10.4, pp. 45–47, and its
    finite-dimensional continuity already established for 1.10.5, pp. 47–48.
    The measure-zero conclusion is not asserted by those items. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology LinearBasis
  SymmetricForms HomogeneousPolynomialFunctions PolynomialFunctions PolynomialRepresentations
  PolynomialDiagonalNorm HilbertFormCompactness TopologicalBorel ContinuousBorelPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [constant_tuple_map_continuous]: supporting
    diagonal-map continuity for polynomial evaluation in
    Federer 2.6.5, p. 120. This is general product-topology
    background, not a separate assertion in the book. *)
Lemma constant_tuple_map_continuous (T : topologicalType) n :
  continuous (fun x : T => (fun _ : 'I_n => x)).
Proof.
move=> x; apply/cvg_sup.
move=> i; move: x; apply/(@continuousP _ (initial_topology (@^~ i)))=> A [B hB <-].
exact: hB.
Qed.

(** Source for [finite_inner_polynomial_continuous]: supporting
    continuity of the polynomial in Federer 2.6.5, p. 120,
    using the finite sum of homogeneous forms in 1.10.4,
    p. 46. Any finite-dimensional inner-product space is allowed. *)
Theorem finite_inner_polynomial_continuous (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (P : V -> R^o) :
  is_polynomial_function P -> continuous (fun x : inner_metric_space hB => P x).
Proof.
move/polynomial_finite_representation=> [N [f hf]].
have hfun : (fun x : inner_metric_space hB => P x) =
    (fun x : inner_metric_space hB => \sum_(i < N) sform_polynomial_value (f i) x).
  exact: funext hf.
rewrite hfun; apply: continuous_big; first exact: add_continuous.
move=> i _ x.
have heval : (fun x : inner_metric_space hB => sform_polynomial_value (f i) x) =
    (fun x : inner_metric_space hB => (i`!%:R : R)^-1 * f i [tuple x | j<i]).
  by apply: funext=> y; rewrite sform_polynomial_diagonal_value.
rewrite heval; apply: cvgM.
- exact: nbhs_filter.
- apply: cvg_cst; exact: nbhs_filter.
apply: (@continuous_comp (Topological.clone (inner_metric_space hB) _)
  (Topological.clone ('I_i -> inner_metric_space hB) _) (Topological.clone R^o _)
  (fun x => fun _ : 'I_i => x) (fun u => f i [tuple u j | j<i]) x).
- exact: constant_tuple_map_continuous.
- exact (@finite_scalar_symmetric_form_continuous R V B hB n e he i (f i) (fun _ => x)).
Qed.

(** Source for [finite_inner_polynomial_zero_set_borel]: the
    Borel measurability needed in the Fubini induction in
    Federer 2.6.5, p. 120. The inverse image of the
    closed singleton zero is Borel; no measure is assumed here. *)
Corollary finite_inner_polynomial_zero_set_borel (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (P : V -> R^o) :
  is_polynomial_function P -> borel_set [set x : inner_metric_space hB | P x = 0].
Proof.
move=> hp.
exact (@continuous_borel_preimage (Topological.clone (inner_metric_space hB) _)
  (Topological.clone R^o _) (fun x => P x) (@finite_inner_polynomial_continuous R V B hB n e he P hp)
  [set 0] (closed_borel_set (compact_closed (@norm_hausdorff R R^o) (@compact_set1 R^o 0)))).
Qed.
