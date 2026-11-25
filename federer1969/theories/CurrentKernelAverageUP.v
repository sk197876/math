(** Federer (1969), 4.1.18, pp. 374–375: the
    compact probability zero-current used only to prove
    existence of the original reflected translation averages.
    Its original scalar test action is specified before
    existence, bounds or Cartesian use.  *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  AlternatingForms AlternatingZero CurrentSpaces CurrentEvaluation
  EuclideanLebesgueDimensions MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentKernelAverageUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation C:=(@current_space R h2 n Full hFull 0%N).
Local Notation value:=(@current_test_value R h2 n Full hFull 0%N).
Local Notation action:=(@current_value R h2 n Full hFull 0%N).
Variable w:X->R.

(** Source for [is_current_kernel_average]: the zero-current
    with density Phi_epsilon(-z) in the first average
    of 4.1.18, p. 374. The actual density, not
    a formal probability distribution, is used. *)
Definition is_current_kernel_average (S:C):Prop:=forall omega,
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun z=>w z*zero_form_value (value omega z)))
    (action S omega)%:E.

(** Source for [current_kernel_average_unique]: the literal
    original scalar test integral in 4.1.18, p. 374,
    determines the averaging zero-current uniquely. *)
Theorem current_kernel_average_unique (S P:C):
  is_current_kernel_average S->is_current_kernel_average P->S= P.
Proof.
move=>hS hP;apply:(@current_values_extensional R h2 n 0%N Full hFull)=>omega.
exact:(congr1 (@fine R) (measure_integral_unique (hS omega) (hP omega))).
Qed.
End CurrentKernelAverageUP.
