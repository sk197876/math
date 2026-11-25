(** Federer (1969), 4.1.14, pp. 370–371: the
    actual flat-current image is independent of evidence
    for its image, regularity and original flat membership.
    These are propositions, and the opaque operator keeps
    the same actual source current and original map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces FlatCurrentsUP CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzPushforwardBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_flat_lipschitz_pushforward_data_independent]:
    the independence in the original definition of f#T,
    Federer 4.1.14, pp. 370–371, includes arbitrary
    evidence of its unchanged original hypotheses. No opaque
    current value or chosen construction is unfolded. *)
Theorem current_flat_lipschitz_pushforward_data_independent
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu)
    (hImage0 hImage1:forall x,U x->V (f x))
    (hLocal0 hLocal1:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (T:@current_space R h2 n U hU m)
    (hFlat0 hFlat1:@is_flat_current R h2 n m U hU T) :
  @CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
    f hImage0 hLocal0 T hFlat0=
  @CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
    f hImage1 hLocal1 T hFlat1.
Proof.
have -> : hImage0=hImage1 := Prop_irrelevance _ _.
have -> : hLocal0=hLocal1 := Prop_irrelevance _ _.
exact: current_flat_lipschitz_pushforward_proof_independent.
Qed.
