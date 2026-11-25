(** Federer (1969), 4.1.7, p. 356: the
    original current with a locally mass-integrable
    multivector density. Its test action is specified
    before existence of a current is proved. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  AlternatingPairing CurrentSpaces MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDensityAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).

(** Source for [is_current_density_action]:
    (gamma wedge xi)(psi)=integral of the original
    pairing of xi and psi, Federer 4.1.7,
    p. 356. Neither continuity nor existence is
    a premise of this independent specification. *)
Definition is_current_density_action (gamma:set X->\bar R) (xi:X->exterior_power X m)
    (T:@current_space R h2 n (fun _=>True) hFull m):Prop:=
  forall psi,is_measure_integral gamma (real_total_integrand
    (fun x=>pairing (xi x) (@current_test_value R h2 n (fun _=>True) hFull m psi x)))
    (@current_value R h2 n (fun _=>True) hFull m T psi)%:E.
End CurrentDensityAction.
