(** Federer (1969), 4.1.7, p. 358: compact
    scalar tests equal to one near a
    prescribed compact set. Reuse the actual
    cutoff replacement from 4.1.1, pp. 344–345. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct AlternatingForms AlternatingZero
  CurrentCoefficientNorms CurrentSpaces CurrentConstantFields SmoothCompactSet SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothTestEvaluation SmoothCutoffReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentScalarCutoffs.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o 0).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n 0%N).
Local Notation hNY := (@current_form_comass_real_norm R h2 n 0%N).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (@current_smooth_space R h2 n U hU 0%N).
Local Notation ev := (@current_smooth_value R h2 n U hU 0%N).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation D := (@current_smooth_derivatives R h2 n U hU 0%N).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU 0%N).
Local Notation DT := (@current_test_space R h2 n U hU 0%N).

(** Source for [current_compact_scalar_cutoff]: every
    compact K admits an actual scalar test
    equal to one on an open neighbourhood
    of K, supporting the two local-normality
    equivalences in Federer 4.1.7, p. 358. *)
Theorem current_compact_scalar_cutoff (K:smooth_compact_set hNX U):
  exists gamma:DT,exists W:set X,
    @open (real_norm_metric_space hNX) W /\
    smooth_compact_carrier K `<=` W /\ W `<=` U /\
    forall x,W x->@current_test_value R h2 n U hU 0%N gamma x=@zero_form R X R^o 1.
Proof.
pose one:=@current_constant_form R h2 n U hU 0%N (@zero_form R X R^o 1).
pose Q:=@smooth_cutoff_replacement R X Y NX NY hNX hNY n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE K.
have[W [hW [hKW [hWU hAgreement]]]]:=
  @smooth_cutoff_replacement_agrees_near_compact R X Y NX NY hNX hNY n
    (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE K.
exists (Q one),W;split=>//;split=>//;split=>// x hx.
have hCut:@current_test_value R h2 n U hU 0%N (Q one) x=ev one x.
  exact:(hAgreement one x hx).
exact:(eq_trans hCut
  (@current_constant_form_values R h2 n U hU 0%N (@zero_form R X R^o 1) x (hWU x hx))).
Qed.
End CurrentScalarCutoffs.
