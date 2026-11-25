(** Federer (1969), 4.1.23, pp. 379–380:
    null changes of a coefficient field
    leave its actual current unchanged.
    Reuse the original integral invariance
    on null sets for each compact
    test; the raw fields themselves
    are not identified pointwise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingPairing CurrentSpaces CurrentEvaluation CurrentDensityAction
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralAlmostEquality MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_density_almost_agreement]:
    almost-equal original coefficient densities
    have the same current on every
    original compact test, supporting the
    open/closed rectangular replacement in
    Federer 4.1.23, pp. 379–380.
    No mass or support premise
    is needed for this action identity. *)
Theorem current_density_almost_agreement (R : realType)
    (h2 : (1+1:R)!=0) n m (mu : set (R_n R n) -> \bar R) (hm : is_measure mu)
    (f g : R_n R n -> exterior_power (R_n R n) m)
    (T S : @current_space R h2 n (fun _ => True)
      (fun (x : R_n R n) (_ : True) => norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R n)) x) m) :
  @is_current_density_action R h2 n m mu f T ->
  @is_current_density_action R h2 n m mu g S ->
  measure_almost_everywhere mu [set x | f x=g x] -> T=S.
Proof.
move=> hT hS hEqual.
apply: current_values_extensional=> phi.
have hPair : measure_almost_equal mu
    (real_total_integrand (fun x => pairing (f x) (@current_test_value R h2 n
      (fun _ => True) (fun (x : R_n R n) (_ : True) => norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R n)) x) m phi x)))
    (real_total_integrand (fun x => pairing (g x) (@current_test_value R h2 n
      (fun _ => True) (fun (x : R_n R n) (_ : True) => norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R n)) x) m phi x))).
  apply: (@measure_almost_everywhere_mono R (R_n R n) mu hm _ _ _ hEqual)=> x hx.
  exists (pairing (f x) (@current_test_value R h2 n
      (fun _ => True) (fun (x : R_n R n) (_ : True) => norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R n)) x) m phi x))%:E.
  split; apply/real_total_integrand_graph; by rewrite hx.
have hTransfer := measure_integral_almost_equal hm (hT phi) hPair.
exact: EFin_inj (measure_integral_unique hTransfer (hS phi)).
Qed.
