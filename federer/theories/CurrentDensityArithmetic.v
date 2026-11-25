(** Federer (1969), 4.1.7, p. 356: the original
    pairing integral respects finite linear operations.
    These supporting laws use only the integral
    arithmetic already proved in 2.4.4, pp. 82–83. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  AlternatingPairing CurrentSpaces CurrentDensityAction CurrentDensityUP CurrentPointEvaluation
  MeasureUP MeasureIntegralUP SummableRealFunctionUP SummableRealArithmetic FiniteSignedRealIntegral
  LatticeL1ApproximationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentDensityArithmetic.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation V := (exterior_power X m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation C := (@full_current_space R h2 n m).
Local Notation value := (@current_test_value R h2 n (fun _=>True) hFull m).
Local Notation ev := (@current_value R h2 n (fun _=>True) hFull m).
Variable gamma:set X->\bar R.
Hypothesis hm:is_measure gamma.

(** Source for [current_density_zero_action]: the
    zero density represents the zero current,
    supporting Federer 4.1.7, p. 356,
    by the original pairing integral. *)
Theorem current_density_zero_action:
  is_current_density_action gamma (fun _=>0:V) (0:C).
Proof.
move=>psi.
have hI:=@real_total_zero_integral R X gamma hm.
have hEq:(fun x=>pairing (0:V) (value psi x))=(fun _=>0:R).
  apply:funext=>x;by rewrite /pairing linear0.
rewrite hEq linear0 hom_zeroE;exact:hI.
Qed.

(** Source for [current_density_scaled_action]: scalar
    multiplication of the original density and
    current gives the same integral, supporting
    Federer 4.1.7, p. 356. *)
Theorem current_density_scaled_action (xi:X->V) (T:C) c:
  is_current_density_action gamma xi T ->
  is_current_density_action gamma (fun x=>c*:xi x) (c*:T).
Proof.
move=>h psi.
have hI:=@real_total_integral_scale R X gamma hm
  (fun x=>pairing (xi x) (value psi x)) (ev T psi) c (h psi).
have hEq:(fun x=>pairing (c*:xi x) (value psi x))=
    (fun x=>c*pairing (xi x) (value psi x)).
  apply:funext=>x;by rewrite /pairing linearZ.
rewrite hEq linearZ hom_scaleE;exact:hI.
Qed.

(** Source for [current_density_sum_action]: addition
    of the original densities represents addition
    of their currents, supporting Federer 4.1.7,
    p. 356. *)
Theorem current_density_sum_action (xi eta:X->V) (T S:C):
  is_current_density_action gamma xi T ->
  is_current_density_action gamma eta S ->
  is_current_density_action gamma (fun x=>xi x+eta x) (T+S).
Proof.
move=>hT hS psi.
have hI:=@real_total_integral_add R X gamma hm
  (fun x=>pairing (xi x) (value psi x)) (fun x=>pairing (eta x) (value psi x))
  (ev T psi) (ev S psi) (hT psi) (hS psi).
have hEq:(fun x=>pairing (xi x+eta x) (value psi x))=
    (fun x=>pairing (xi x) (value psi x)+pairing (eta x) (value psi x)).
  apply:funext=>x;by rewrite /pairing linearD.
rewrite hEq linearD hom_addE;exact:hI.
Qed.

(** Source for [current_density_finite_sum_action]:
    the original pairing integral commutes with
    finite coordinate sums, supporting the
    boundary and divergence formulas in Federer
    4.1.7, p. 356. Empty sums remain valid. *)
Theorem current_density_finite_sum_action (I:finType) (xi:I->X->V) (T:I->C):
  (forall i,is_current_density_action gamma (xi i) (T i)) ->
  is_current_density_action gamma (fun x=>\sum_i xi i x) (\sum_i T i).
Proof.
move=>h psi.
have hI:=@finite_signed_real_sum_integral R X I gamma hm (index_enum I)
  (fun i x=>pairing (xi i x) (value psi x)) (fun i=>ev (T i) psi)
  (fun i _=>h i psi).
have hEq:(fun x=>pairing (\sum_i xi i x) (value psi x))=
    (fun x=>\sum_i pairing (xi i x) (value psi x)).
  apply:funext=>x;by rewrite /pairing linear_sum.
rewrite hEq current_value_finite_sum;exact:hI.
Qed.
End CurrentDensityArithmetic.
