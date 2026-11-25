(** Federer (1969), 4.1.18, p. 374: compact
    parameter control proves the original closed-cylinder
    properness needed for the smoothing deformation.
    This adapter is the converse compact-locus direction
    of the existing containing-set theorem.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain SmoothCompactSet ProperMapUP IsotropyGroupTopology
  CurrentProperOnContainingSet CurrentProperContainingCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_containing_compact_loci_proper]:
    compact inverse target loci are precisely the original
    properness condition, by 2.2.17, p. 72,
    supporting the translation homotopies of 4.1.18,
    p. 374. Relative carriers are retained exactly. *)
Theorem current_containing_compact_loci_proper (R:realType) n nu
    (U:set (R_n R n)) (V:set (R_n R nu)) (C:set (R_n R n))
    (hCU:C `<=` U) (f:R_n R n->R_n R nu)
    (hImage:forall x,U x->V (f x)):
  (forall K:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) V,
    @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      [set x|C x /\smooth_compact_carrier K (f x)]) ->
  is_proper_map (@current_map_on_containing_set R n nu U V C hCU f hImage).
Proof.
exact:(@current_containing_proper_compact_loci R n nu U V C hCU f hImage).2.
Qed.
