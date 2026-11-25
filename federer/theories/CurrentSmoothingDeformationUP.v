(** Federer (1969), 4.1.18, p. 374: independent
    literal scalar-action specification of the smoothing
    deformation. The defining integral averages the old
    fixed-z deformation chains with Phi_epsilon(-z).
    Existence, continuity and estimates are separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentEvaluation CurrentTranslationChain EuclideanLebesgueDimensions
  SummableRealFunctionUP MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSmoothingDeformationUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variable family:R->X->R.
Variable epsilon:R.
Variable T:@current_space R h2 n Full hFull m.
Local Notation Target:=(@current_space R h2 n Full hFull (1+m)%N).
Local Notation DT:=(@current_test_space R h2 n Full hFull (1+m)%N).
Local Notation action:=(@current_value R h2 n Full hFull (1+m)%N).

(** Source for [is_current_smoothing_deformation]:
    the displayed defining action of H_epsilon T,
    Federer 4.1.18, p. 374. This law imposes
    no mass, support or derivative assumption on T. *)
Definition is_current_smoothing_deformation (Q:Target):Prop:=
  forall omega:DT,is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun z=>family epsilon (-z)*
      action (@current_translation_chain R h2 n m z T) omega))
    (action Q omega)%:E.

(** Source for [current_smoothing_deformation_unique]:
    every original compact-test action is fixed by
    the integral, so the original smoothing
    deformation in 4.1.18, p. 374, is unique. *)
Theorem current_smoothing_deformation_unique (Q P:Target):
  is_current_smoothing_deformation Q->is_current_smoothing_deformation P->Q= P.
Proof.
move=>hQ hP;apply:(@current_values_extensional R h2 n (1+m)%N Full hFull)=>omega.
exact:(EFin_inj (measure_integral_unique (hQ omega) (hP omega))).
Qed.
End CurrentSmoothingDeformationUP.
Arguments is_current_smoothing_deformation {R} h2 n m family epsilon T Q.
