(** Federer (1969), 4.1.19, p. 377: the
    weak exterior derivative relation between the
    bounded measurable forms phi and psi.
    Every original compact smooth eta on U
    is tested with the printed positive sign. *)
From mathcomp Require Import functions all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingPairing CurrentDomain CurrentCoefficientNorms
  CurrentVectorSpaces SmoothCompactSet SmoothFunctionSupport
  SmoothCurrentDivergence EuclideanOpenDomainMeasure
  MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section WeakExteriorPair.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation E d := (@current_vector_smooth_space R h2 n U hU d).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).
Local Notation mu := (@euclidean_open_domain_measure R n U).

(** Source for [is_weak_current_exterior_pair]:
    the literal equation integral_U(<div eta,phi>
    +<eta,psi>)=0 for every compact smooth eta,
    Federer 4.1.19, p. 377.
    Both integrals use the original U,
    degrees and actual divergence. Smoothness or
    pointwise derivative equality is not imposed on phi or psi. *)
Definition is_weak_current_exterior_pair
    (phi : UT -> A_m X R^o m) (psi : UT -> A_m X R^o m.+1) : Prop :=
  forall (eta : E m.+1) (K : smooth_compact_set hNX U),
    @smooth_function_support R X (exterior_power X m.+1) NX hNX U
      (E m.+1) (ev m.+1) eta `<=` smooth_compact_carrier K ->
    is_measure_integral mu (real_total_integrand (fun x : UT =>
      pairing (ev m (div eta) (set_val x)) (phi x)+
      pairing (ev m.+1 eta (set_val x)) (psi x))) 0%E.
End WeakExteriorPair.
