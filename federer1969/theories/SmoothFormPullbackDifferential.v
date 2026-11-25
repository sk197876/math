(** Federer (1969), 4.1.7, p. 359:
    the original smooth pullback commutes
    with exterior differentiation. This is
    the actual-space consequence of the
    already proved coordinate-generator theorem in
    4.1.6, pp. 354–355, and
    supports boundary commutation for currents. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import AlternatingDual Hom RealNormUP NormDifferentialUP NormRegularity NormHigherDifferentialFirst
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms ExteriorDerivativeUP ExteriorDifferentialUP
  ExteriorDifferentialSealed ExteriorDerivativeFiniteSum RealDifferentialFormCalculus RealFormPullbackDifferential
  CurrentCoefficientNorms CurrentFormInducedNorm CurrentSpaces SmoothFunctionSpaceLaws
  SmoothFormPullbackUP SmoothFormPullbackSealed SmoothCurrentExteriorDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothFormPullbackDifferential.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation PN := (@current_form_comass R h2 v m).
Local Notation QN := (@current_form_comass R h2 n m).
Local Notation hPN := (@current_form_comass_real_norm R h2 v m).
Local Notation J := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ej := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation JN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hJ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation operator := (@continuous_multilinear_one_evaluation R X Y (J 1%N)
  NX NY (@ej 1%N) (@JN 1%N) (hJ 1%N)).
Variables (U:X->Prop) (V:Y->Prop).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Local Notation E := (fun k=>@current_smooth_space R h2 n V hV k).
Local Notation F := (fun k=>@current_smooth_space R h2 v U hU k).
Local Notation ev := (fun k=>@current_smooth_value R h2 n V hV k).
Local Notation fv := (fun k=>@current_smooth_value R h2 v U hU k).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation pull := (fun k=>@SmoothFormPullback.operator R h2 v n k U V hU hV f hImage hf).
Local Notation dU := (@smooth_current_exterior_derivative R h2 v m U hU).
Local Notation dV := (@smooth_current_exterior_derivative R h2 n m V hV).

(** Source for [smooth_form_pullback_exterior_commutes]:
    d(f#phi)=f#(d phi) as an
    equality in the original smooth
    form space on U, supporting
    Federer 4.1.7, p. 359,
    by 4.1.6, pp. 354–355.
    The norm adapters use the
    proved equality of the original
    comass and induced real-form norms. *)
Theorem smooth_form_pullback_exterior_commutes (phi:E m):
  dU (pull m phi)=pull m.+1 (dV phi).
Proof.
apply:(smooth_function_extensional (@current_smooth_space_laws R h2 v U hU m.+1))=>x hx.
have [_ [D1 [hFirst hFirstContinuous]]]:=hf 1%N.
have [_ [D2 [hSecond hSecondContinuous]]]:=hf 2%N.
have hOrdinary y (hy:U y):has_norm_differential NX NY U f y (operator (D1 y)).
  exact:((@norm_higher_differential_first R X Y NX NY hNX hNY J ej JN hJ
    U f y (D1 y)).1 (hFirst y hy)).
have hNormTarget:QN=@real_euclidean_form_norm R h2 n m.
  apply:funext=>a;exact:current_form_comass_induced_equal.
have hNormSource:PN=@real_euclidean_form_norm R h2 v m.
  apply:funext=>a;exact:current_form_comass_induced_equal.
have [M [hM hExteriorM]]:=@smooth_current_exterior_derivative_actual R h2 n m V hV phi
  (f x) (hImage x hx).
have hTargetValue:ev m.+1 (dV phi) (f x)=@ExteriorDifferential.value R h2 n R^o m M.
  exact:(exterior_differential_value_unique hExteriorM (@ExteriorDifferential.laws R h2 n R^o m M)).
rewrite hNormTarget in hM.
have hOriginal:=@original_real_pullback_exterior_derivative R h2 v n J ej JN hJ U f D1
  hFirst V hImage x (D2 x) m (ev m phi) M (hSecond x hx) hM.
change (has_exterior_derivative NX (@real_euclidean_form_norm R h2 v m) U
  (fun y=>A_m_dual (hom_as_linear (operator (D1 y))) (ev m phi (f y))) x
  (A_m_dual (hom_as_linear (operator (D1 x))) (@ExteriorDifferential.value R h2 n R^o m M))) in hOriginal.
rewrite -hNormSource in hOriginal.
have hAgreement y (hy:U y):
    A_m_dual (hom_as_linear (operator (D1 y))) (ev m phi (f y))=fv m (pull m phi) y.
  symmetry;exact:(@smooth_form_pullback_values R v n m U V (E m) (F m) (ev m) (fv m) f
    (pull m) (@SmoothFormPullback.laws R h2 v n m U V hU hV f hImage hf)
    phi y (operator (D1 y)) hy (hOrdinary y hy)).
have hActual:=@exterior_derivative_domain_agreement R X R^o NX hNX m PN U
  (fun y=>A_m_dual (hom_as_linear (operator (D1 y))) (ev m phi (f y)))
  (fv m (pull m phi)) x _ hAgreement hOriginal.
have hLeft:=exterior_derivative_unique hNX hPN
  (@smooth_current_exterior_derivative_actual R h2 v m U hU (pull m phi) x hx) hActual.
have hRight:=@smooth_form_pullback_values R v n m.+1 U V (E m.+1) (F m.+1)
  (ev m.+1) (fv m.+1) f (pull m.+1)
  (@SmoothFormPullback.laws R h2 v n m.+1 U V hU hV f hImage hf)
  (dV phi) x (operator (D1 x)) hx (hOrdinary x hx).
rewrite hTargetValue in hRight;exact:(eq_trans hLeft (esym hRight)).
Qed.
End SmoothFormPullbackDifferential.
