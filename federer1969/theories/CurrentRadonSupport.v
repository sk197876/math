(** Federer (1969), 4.1.7, pp. 358–359:
    the original variation is carried by the
    original current support. Reuse the open
    annihilation calculation and the Radon support
    theorem of 2.2.5, pp. 62–63. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology functions.
From Federer Require Import IsotropyGroupTopology RealNormUP NormMetric NormDifferentialUP NormOpenTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain CurrentSpaces CurrentIntegrationCriterion
  NormalisedCurrentSealed DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP MeasureAlmostBasic MeasureSupportUP MeasureSupport RadonMeasureUP RadonSupport
  FunctionalSupportUP CurrentRadonAnnihilation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentRadonSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation support := (@current_support R h2 n U hU m T).
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Let hBase:=normalised_distribution_representation_laws hRepresentation.
Let hm:=distribution_representation_measure hBase.
Let hr:=distribution_representation_radon hBase.

(** Source for [current_radon_support_subset]: each
    point in the original variation support
    belongs to the current support, supporting
    Federer 4.1.7, pp. 358–359.
    The conclusion suffices for carrying the
    variation on the original properness locus. *)
Theorem current_radon_support_subset:
  measure_support mu `<=` [set x:UT|support (set_val x)].
Proof.
move=>x hx;split;first exact:set_valP.
move=>[W [[hW hZero] hWx]].
have hOpen:open (set_val @^-1` W:set UT).
  exact:((@continuousP UT (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) set_val).1
    (@set_type_val_continuous (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) U) W hW).
have hNotZero:mu (set_val @^-1` W)<>0.
  exact:((measure_support_neighborhood_law (measure_support_specification mu) x).1 hx
    (set_val @^-1` W) hOpen hWx).
apply:hNotZero.
apply:(@current_radon_annihilation_null R h2 n m U hU T hT W).
by split.
Qed.

(** Source for [current_radon_outside_support_null]:
    the original variation gives zero measure
    to the complement of the current support,
    supporting normality and support-proper pushforward
    in Federer 4.1.7, pp. 358–359. *)
Theorem current_radon_outside_support_null:
  mu [set x:UT|~support (set_val x)]=0.
Proof.
apply:(@measure_null_subset R UT mu hm _ (~` measure_support mu)).
- move=>x hx hMeasure;exact:hx (@current_radon_support_subset x hMeasure).
- exact:(@radon_support_complement_null R UT mu hm hr).
Qed.
End CurrentRadonSupport.
