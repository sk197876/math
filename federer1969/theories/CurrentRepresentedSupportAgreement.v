(** Federer (1969), 4.1.7, pp. 357–359,
    used in the support obstruction of 4.1.12,
    p. 368: a represented current depends only
    on the values of a test on its support.
    The actual variation is carried by that support.
    The representation hypothesis is essential here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain CurrentSpaces CurrentIntegrationCriterion
  MultivectorDualSealed NormalisedCurrentSealed CurrentRadonSupport DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralAlmostEquality MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentRepresentedSupportAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation value := (@current_test_value R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).

(** Source for [current_represented_support_values_equal]:
    equality on the original support suffices for
    represented currents, by the original Radon representation
    of Federer 4.1.7, pp. 357–359; this
    supports the first example of 4.1.12, p. 368.
    No such claim is made for arbitrary distributions. *)
Theorem current_represented_support_values_equal (phi psi:DT):
  (forall x,@current_support R h2 n U hU m T x->value phi x=value psi x)->
    action T phi=action T psi.
Proof.
move=>hEqual.
have hBase:=normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n m U hU T hT).
pose hm:=distribution_representation_measure hBase.
have hSupport:measure_almost_everywhere mu [set x:UT|@current_support R h2 n U hU m T (set_val x)].
  exact:(@current_radon_outside_support_null R h2 n m U hU T hT).
have hFirst:=distribution_representation_action hBase phi.
have hSecond:=distribution_representation_action hBase psi.
have hSame:measure_almost_equal mu
  (real_total_integrand (fun x:UT=>@MultivectorDualSealed.MultivectorDual.evaluation R (R_n R n) m
    (xi x) (value phi (set_val x))))
  (real_total_integrand (fun x:UT=>@MultivectorDualSealed.MultivectorDual.evaluation R (R_n R n) m
    (xi x) (value psi (set_val x)))).
  apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hSupport)=>x hx.
  exists (@MultivectorDualSealed.MultivectorDual.evaluation R (R_n R n) m
    (xi x) (value phi (set_val x)))%:E.
  split;rewrite real_total_integrand_graph;first by [].
  by rewrite (hEqual (set_val x) hx).
exact:(EFin_inj (measure_integral_unique (measure_integral_almost_equal hm hFirst hSame) hSecond)).
Qed.
End CurrentRepresentedSupportAgreement.
