(** Federer (1969), 4.1.6, p. 355: the
    pullbacks of the original coordinate differentials
    are closed when f is twice differentiable.
    The actual second-differential symmetry supplies
    the two-term cancellation, without a class-two
    or second-derivative-continuity hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialFiniteCalculus
  NormDifferentialLocal NormHigherDifferentialUP NormHigherDifferentialFields NormSecondDifferential
  ContinuousMultilinearUP ContinuousMultilinearOne MultilinearSuccessorArguments
  InnerNorm HilbertFormCompactness EuclideanInnerProduct EuclideanScalarCoordinateMaps
  GrassmannAbbreviations Alternating OneFormLinear OneFormIdentification
  EuclideanCoordinateForms OneFormOperatorNorm OneFormPullbackIdentification
  ExteriorDerivativeUP SymmetricOneFormClosed RealDifferentialFormCalculus
  ExteriorIndices CovectorProducts OneFormProducts ScalarCoefficients CovectorProductNaturality
  CoordinatePullbackClosed ClosedOneFormProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CoordinateProductPullbackClosed.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n:nat.
Local Notation X:=(R_n R v).
Local Notation Y:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R v)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Z:nat->lmodType R.
Variable evaluation:forall k,{ffun 'I_k->X}->Hom (Z k) Y.
Variable ZN:forall k,Z k->R.
Hypothesis hZ:forall k,is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k).
Variable A:X->Prop.
Variable f:X->Y.
Variable F:X->Z 1%N.
Hypothesis hF:forall x,A x->has_norm_higher_differential NX evaluation ZN A f 1%N x (F x).
Local Notation J:=(@continuous_multilinear_one_evaluation R X Y (Z 1%N)
  NX NY (@evaluation 1%N) (@ZN 1%N) (@hZ 1%N)).

(** Source for [original_coordinate_product_pullback_closed]:
    the pulled-back DX_lambda is a product of
    the preceding closed one-form generators,
    Federer 4.1.6, p. 355. Empty products,
    dimension zero and every exterior degree remain included. *)
Theorem original_coordinate_product_pullback_closed a (z:Z 2%N) m (lambda:Lambda n m):
  has_norm_higher_differential NX evaluation ZN A f 2%N a z->
  has_real_form_derivative h2 A
    (fun x=>A_m_dual (hom_as_linear (J (F x)))
      (@omega_lambda R h2 Y n (@euclidean_coordinate_form R n) m lambda)) a 0.
Proof.
move=>hSecond.
have [L [hL _]]:=norm_higher_differential_field_step_elim hNX hF hSecond.
have hFunction:
    (fun x=>A_m_dual (hom_as_linear (J (F x)))
      (@omega_lambda R h2 Y n (@euclidean_coordinate_form R n) m lambda))=
    (fun x=>one_forms_wedge h2 (scalar_bilinear R) 1
      (fun i:'I_m=>A_m_dual (hom_as_linear (J (F x))) (euclidean_coordinate_form (tnth (val lambda) i)))).
  apply:funext=>x; rewrite /omega_lambda.
  exact:one_forms_wedge_natural.
rewrite hFunction.
apply:(@closed_real_one_form_products R h2 v m A
  (fun i x=>A_m_dual (hom_as_linear (J (F x))) (euclidean_coordinate_form (tnth (val lambda) i)))
  a (norm_differential_interior hL))=>i.
exact:(@original_coordinate_pullback_closed R h2 v n Z evaluation ZN hZ A f F hF
  a z (tnth (val lambda) i) hSecond).
Qed.
End CoordinateProductPullbackClosed.
