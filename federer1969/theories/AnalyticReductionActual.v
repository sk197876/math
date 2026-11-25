(** Federer (1969), 3.4.8(1),(2), p. 326:
    the original reduction loci use the actual
    coordinate germs, coordinate subrings, orthogonal
    pullbacks and original ideal. All selected objects
    remain behind their independent opaque interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology AnalyticGermUP AnalyticGermRing AnalyticCoordinateGermsSealed
  AnalyticCoordinateSubringFamilySealed AnalyticRotatedGermIdeal
  AnalyticReductionLociUP AnalyticReductionLociSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Actual.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation G:=(@analytic_germ_ring R X NX hNX 0).
Variable I:set G.
Local Notation gamma:=(@AnalyticCoordinateGerms.value R X NX hNX n e he omega).
Local Notation Q:=(@AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega).
Local Notation rotated:=(@analytic_rotated_germ_ideal R X B hB n e he I).

(** Source for [analytic_reduction_actual_A]: original
    A_j with actual Q_j and I_g, 3.4.8(2), p. 326. *)
Definition analytic_reduction_actual_A:=@AnalyticReductionLoci.A R X NX hNX n O e gamma Q rotated.
(** Source for [analytic_reduction_actual_B]: original
    B_(j+1) with actual positive directional tests,
    3.4.8(2), p. 326. *)
Definition analytic_reduction_actual_B:=@AnalyticReductionLoci.B R X NX hNX n O e gamma Q rotated.
(** Source for [analytic_reduction_actual_C]: original
    C_m with actual coordinate germs and independent
    denominators, 3.4.8(2), p. 326. *)
Definition analytic_reduction_actual_C:=@AnalyticReductionLoci.C R X NX hNX n O e gamma Q rotated.
(** Source for [analytic_reduction_actual_E]: original
    E_m, including its full-prefix endpoint,
    3.4.8(2), p. 326. *)
Definition analytic_reduction_actual_E:=@AnalyticReductionLoci.E R X NX hNX n O e gamma Q rotated.

(** Source for [analytic_reduction_actual_laws]: every
    actual reduction set satisfies the exact original
    membership equations, 3.4.8(2), p. 326. *)
Lemma analytic_reduction_actual_laws:is_analytic_reduction_loci e gamma Q rotated
  analytic_reduction_actual_A analytic_reduction_actual_B analytic_reduction_actual_C analytic_reduction_actual_E.
Proof. exact:(@AnalyticReductionLoci.laws R X NX hNX n O e gamma Q rotated). Qed.
End Actual.
