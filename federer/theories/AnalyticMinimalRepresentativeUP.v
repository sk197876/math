(** Federer (1969), 3.4.8(12), p. 327:
    independent laws for an actual representative contained
    in every original analytic subvariety whose germ
    contains the given variety germ. Existence is proved
    separately by the finite stratification and analytic continuation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness SetGermUP SetGermOrder FiniteAnalyticVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_analytic_minimal_representative]: every
    conclusion of 3.4.8(12), p. 327. The
    universal bound concerns actual analytic subvarieties
    on the original prescribed neighbourhood. *)
Record is_analytic_minimal_representative (R:realType) n
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0)
    (U S:set (R_n R n)):Prop:={
  (** Source for [analytic_minimal_representative_germ]: the
      selected set represents alpha, 3.4.8(12), p. 327. *)
  analytic_minimal_representative_germ:
    @set_germ (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 S=alpha;
  (** Source for [analytic_minimal_representative_bound]: actual
      containment for every original analytic supergerm,
      3.4.8(12), p. 327. *)
  analytic_minimal_representative_bound:forall T:set (R_n R n),
    @is_finite_analytic_variety R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U T ->
    set_germ_subset alpha (@set_germ (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 T) ->S `<=` T
}.
