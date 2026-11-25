(** Federer (1969), 4.1.21, p. 378: retain the
    zero-current endpoint above the ambient dimension. The
    existing I_1^m interface is indexed by m<=n; degrees
    above n require no new measure definition, since the
    actual current is already zero by 4.1.10, p. 364. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSpaces CurrentSupportGeometry CurrentSupportExtensionality
  CurrentAboveDimension CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentMassSealed CurrentMassRepresentation CurrentMassFiniteAlgebra
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentNullCorollaryAboveDimension.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Hypothesis hNM:(n<m)%N.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable T:@current_space R h2 n U hU m.

(** Source for [current_null_corollary_above_dimension_support]:
    the support conclusion of 4.1.21, p. 378, holds
    trivially above the ambient dimension. Reuse the actual
    current-space vanishing theorem of 4.1.10, p. 364,
    without adding flatness, representation or finite mass. *)
Theorem current_null_corollary_above_dimension_support:
  @current_support R h2 n U hU m T `<=` set0.
Proof.
apply:(@current_empty_support_iff_zero R h2 n m U hU T).2.
exact:(@current_above_dimension R h2 n m hNM U hU T).
Qed.

(** Source for [current_null_corollary_above_dimension_variation]:
    every subset of the original domain has zero variation
    above dimension, covering the remaining degree endpoint
    of 4.1.21, p. 378. Every representation witness and
    arbitrary, possibly nonmeasurable, restricting set is retained. *)
Theorem current_null_corollary_above_dimension_variation
    (hT:@is_integration_representable_current R h2 n m U hU T)
    (A:set (current_domain R n U)):
  @NormalisedCurrent.measure R h2 n m U hU T hT A=0%E.
Proof.
pose mu:=@NormalisedCurrent.measure R h2 n m U hU T hT.
pose hBase:=normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n m U hU T hT).
pose hm:=distribution_representation_measure hBase.
have hTotal:mu setT=0%E.
  rewrite /mu.
  rewrite -(@current_represented_mass_total R h2 n m U hU T hT).
  by rewrite (@current_above_dimension R h2 n m hNM U hU T) current_mass_zero.
exact:(@measure_null_subset R (current_domain R n U) mu hm A setT (subsetT _) hTotal).
Qed.
End CurrentNullCorollaryAboveDimension.
