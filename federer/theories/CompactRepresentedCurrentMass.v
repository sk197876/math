(** Federer (1969), 4.1.7, p. 358: a
    compactly supported represented current has
    finite mass. Its original variation is
    carried by its compact current support;
    Radon compact finiteness then applies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology functions.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain CurrentSpaces CurrentIntegrationCriterion
  NormalisedCurrentSealed DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP MeasureNullModification RadonMeasureUP IsotropyGroupTopology CurrentRadonSupport
  CurrentMassSealed CurrentMassRepresentation FunctionalSupportUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactRepresentedCurrentMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation UT := (current_domain R n U).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation support := (@current_support R h2 n U hU m T).
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Let hBase:=normalised_distribution_representation_laws hRepresentation.
Let hm:=distribution_representation_measure hBase.
Let hr:=distribution_representation_radon hBase.

(** Source for [compact_represented_current_finite_mass]:
    compact support makes the mass of a
    represented current finite, supporting the
    assertion about normal currents in Federer
    4.1.7, p. 358. Compactness is
    taken in the original open domain. *)
Theorem compact_represented_current_finite_mass:
  compact [set x:XT|support x]->(@CurrentMass.value R h2 n m U hU T < +oo)%E.
Proof.
move=>hCompact.
pose K:set XT:=[set x:XT|support x].
have hInU:K `<=` U by move=>x hx;exact:hx.1.
have hKCompact:compact (set_val @^-1` K:set UT):=
  @set_type_compact_preimage XT U K hCompact hInU.
have hNull:=@current_radon_outside_support_null R h2 n m U hU T hT.
have hWhole:mu setT=mu (set_val @^-1` K).
  apply:(@measure_null_modification_value R UT mu hm setT (set_val @^-1` K)
    [set x:UT|~support (set_val x)] hNull)=>x hGood.
  split;last by [].
  move=>_;change (support (set_val x));apply:contrapT=>hNo;exact:hGood hNo.
rewrite (@current_represented_mass_total R h2 n m U hU T hT) hWhole.
exact:(radon_compact_finite hr hKCompact).
Qed.
End CompactRepresentedCurrentMass.
