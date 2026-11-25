(** Federer (1969), 4.1.7, pp. 355–356:
    independent local summability and test-action
    specifications for measurable current products.
    The current itself is constructed separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing CurrentDomain
  CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed PartialFunctionBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_locally_summable_current_field]:
    a field is measurable and its norm is
    summable on every original compact subset,
    exactly the condition in Federer 4.1.7,
    pp. 355–356. The field need not be
    smooth, bounded or globally summable. *)
Definition is_locally_summable_current_field (R:realType) (B:topologicalType)
    (V:lmodType R) (NV:V->R) (hNV:is_real_norm NV)
    (mu:set B->\bar R) (f:B->V):Prop:=
  is_measure_measurable_function mu (partial_function_total (fun x=>(f x:real_norm_metric_space hNV))) /\
  forall K:set B,compact K->exists c:R,
    is_measure_subset_integral mu K (real_total_integrand (fun x=>NV (f x))) c%:E.

(** Source for [is_current_measurable_multiplier]:
    the original product action integrates the
    actual coefficient operation against ||T||,
    supporting Federer 4.1.7, pp. 355–356.
    This specifies every original test before
    proving that the product is a current. *)
Definition is_current_measurable_multiplier (R:realType) (h2:(1+1:R)!=0)
    (n q p:nat) (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (V:lmodType R) (F:exterior_power (R_n R n) q->V->exterior_power (R_n R n) p)
    (T:@current_space R h2 n U hU q)
    (hT:@is_integration_representable_current R h2 n q U hU T)
    (f:current_domain R n U->V) (S:@current_space R h2 n U hU p):Prop:=
  forall psi:@current_test_space R h2 n U hU p,
    is_measure_integral (@NormalisedCurrent.measure R h2 n q U hU T hT)
      (real_total_integrand (fun x=>pairing
        (F (@NormalisedCurrent.auxiliary_density R h2 n q U hU T hT x) (f x))
        (@current_test_value R h2 n U hU p psi (set_val x))))
      (@current_value R h2 n U hU p S psi)%:E.
