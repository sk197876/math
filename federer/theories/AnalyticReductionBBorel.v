(** Federer (1969), 3.4.8(5), p. 328:
    every original B_j is Borel. Its actual positive
    directional-jet condition is open, while the actual
    coordinate germ subring is closed. Compact projection
    supplies the conclusion for the original rotated ideal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HomInner LinearGroupTopology HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology AnalyticGermUP AnalyticGermRing AnalyticGermMetric
  CommutativeIdealUP TopologicalBorel AnalyticPrefixGermSubring AnalyticRotatedGermIdeal
  AnalyticReductionLociUP AnalyticDirectionalJetOpen AnalyticRotatedPrefixIncidenceBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_B_borel]: the original
    B_(j+1) in 3.4.8(2),(5), pp. 326, 328,
    is Borel. Natural array index j denotes the printed
    basis direction e_(j+1); the coordinate prefix has
    dimension j+1. *)
Theorem analytic_reduction_B_borel
    (R:realType) (X:lmodType R) (B:X->X->R) (hB:is_inner_product B)
    n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o)
    (hDual:forall i k,omega i (e k)=if i==k then 1 else 0)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    (j:'I_n):
  is_commutative_ideal I ->
  borel_set [set g:@orthogonal_group R X B hB n e he|exists beta,
    @analytic_rotated_germ_ideal R X B hB n e he I g beta /\
    @analytic_prefix_germ_subring R X (inner_norm hB) (inner_norm_real_norm hB)
      n e he omega (j:nat).+1 (ltn_ord j) beta /\
    has_nonzero_analytic_directional_jet beta (e j)].
Proof.
move=>hI.
exact:(@analytic_rotated_prefix_open_incidence_borel R X B hB n e he omega hDual
  I (j:nat).+1 (ltn_ord j) [set beta|has_nonzero_analytic_directional_jet beta (e j)] hI
  (@analytic_positive_directional_jet_open R X (inner_norm hB) (inner_norm_real_norm hB) (e j))).
Qed.
