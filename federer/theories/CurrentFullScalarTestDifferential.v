(** Federer (1969), 4.1.8, p. 362: the actual
    scalar differential in the segment boundary formula.
    Reuse the global first-differential and scalar
    coefficient laws already used for the original
    whole-line primitive in 4.1.7, p. 359. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  NormOpenDomainLaws NormClassOneUP NormClassOneLinearPostcompose
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading ExteriorPowers AlternatingForms AlternatingZero AlternatingPairing
  ExteriorDerivativeUP ExteriorDifferentialUP ExteriorDifferentialNormBound
  CurrentCoefficientNorms CurrentSpaces CurrentZeroCovectorMaps CurrentTestExteriorDerivative
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation
  SmoothGlobalFirstDifferential ExteriorFirstPairingTuple.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentFullScalarTestDifferential.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation Y := (A_m X R^o 0%N).
Local Notation NY := (@current_form_comass R h2 n 0%N).
Local Notation hNY := (@current_form_comass_real_norm R h2 n 0%N).
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation E := (@current_smooth_space R h2 n (fun _=>True) hFull 0%N).
Local Notation ev := (@current_smooth_value R h2 n (fun _=>True) hFull 0%N).
Local Notation hE := (@current_smooth_space_laws R h2 n (fun _=>True) hFull 0%N).
Local Notation dE := (@current_smooth_derivatives R h2 n (fun _=>True) hFull 0%N).
Local Notation hdE := (@current_smooth_derivative_laws R h2 n (fun _=>True) hFull 0%N).
Local Notation value := (@current_test_value R h2 n (fun _=>True) hFull 0%N).
Local Notation derivative := (@current_test_exterior_derivative R h2 n 0%N (fun _=>True) hFull).

(** Source for [current_full_scalar_test_differential]: the
    original scalar coefficient of an actual test has a
    continuous actual differential, whose directional value
    is the printed exterior one-form pairing, supporting
    Federer 4.1.8, p. 362. Every ambient dimension is retained. *)
Theorem current_full_scalar_test_differential psi:
  exists D:X->Hom X R^o,
    is_norm_class_one_field NX NS (fun _=>True) (fun x=>zero_form_value (value psi x)) D /\
    forall x w,pairing (exterior_first_inclusion X w)
      (@current_test_value R h2 n (fun _=>True) hFull 1%N (derivative psi) x)=D x w.
Proof.
pose p:=smooth_test_inclusion hE psi.
pose D0:=@smooth_global_first_differential R X Y NX NY hNX hNY E dE p.
pose a:=@current_zero_form_coefficient R n.
pose D x:=hom_comp a (D0 x).
have hGlobal:=@smooth_global_first_differential_class_one R X Y NX NY hNX hNY E ev hE dE hdE p.
exists D;split.
- exact:(@norm_class_one_linear_postcompose R X Y R^o NX NY NS hNX hNS
    (fun _=>True) (value psi) D0 a hGlobal (@current_zero_form_coefficient_bounded R h2 n)).
- move=>x w.
  have[L [hL hExterior]]:=@current_test_exterior_derivative_actual R h2 n 0%N
    (fun _=>True) hFull psi x Logic.I.
  have hSame:=norm_differential_unique hNX hNY hL
    (norm_class_one_differential hGlobal Logic.I).
  rewrite hSame in hExterior.
  rewrite exterior_first_pairing_tuple hExterior exterior_differential_trace_tuple_values
    big_ord1 expr0 scale1r (tuple0 (exterior_omitted_tuple [tuple w] ord0)).
  by rewrite /D hom_compE /a /current_zero_form_coefficient /zero_form_value /=.
Qed.
End CurrentFullScalarTestDifferential.
