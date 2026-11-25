(** Federer (1969), 4.1.7, p. 356: a density
    current is determined by its original pairing
    integral. The comparison with 4.1.1 uses the
    public multivector-dual pairing law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  AlternatingPairing CurrentSpaces CurrentEvaluation CurrentDensityAction CurrentDensityUP
  MultivectorDualUP MultivectorDualSealed DistributionIntegralFieldUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDensityUniqueness.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation C := (@full_current_space R h2 n m).
Local Notation DT := (@current_test_space R h2 n (fun _=>True) hFull m).
Local Notation value := (@current_test_value R h2 n (fun _=>True) hFull m).
Local Notation ev := (@current_value R h2 n (fun _=>True) hFull m).
Local Notation ed := (@MultivectorDual.evaluation R X m).

(** Source for [current_density_distribution_action]:
    the current pairing integral is the original
    distribution integral, supporting the derivative
    identity in Federer 4.1.7, p. 356,
    by the definition in 4.1.1, p. 346. *)
Theorem current_density_distribution_action gamma xi (T:C):
  is_current_density_action gamma xi T <->
  is_distribution_integral_action gamma ed xi value (ev T).
Proof.
split=>h psi.
- have hEq:(fun x=>ed (xi x) (value psi x))=
      (fun x=>pairing (xi x) (value psi x)).
    apply:funext=>x;exact:MultivectorDual.laws.
  rewrite hEq;exact:h psi.
- have hEq:(fun x=>ed (xi x) (value psi x))=
      (fun x=>pairing (xi x) (value psi x)).
    apply:funext=>x;exact:MultivectorDual.laws.
  have hAction:=h psi;by rewrite hEq in hAction.
Qed.

(** Source for [current_density_action_unique]: the
    original integral determines a unique actual
    current, supporting Federer 4.1.7, p. 356.
    No continuity or representation premise is added. *)
Theorem current_density_action_unique gamma xi (T S:C):
  is_current_density_action gamma xi T ->
  is_current_density_action gamma xi S ->T=S.
Proof.
move=>hT hS;apply:(@current_values_extensional R h2 n m (fun _=>True) hFull)=>psi.
exact:(congr1 (@fine R) (measure_integral_unique (hT psi) (hS psi))).
Qed.
End CurrentDensityUniqueness.
