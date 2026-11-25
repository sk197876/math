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
  CoefficientCoordinates OriginalFormCoefficientExpansion OriginalFormCoefficientDifferentials
  ExteriorDifferentialCoefficients CoordinateProductPullbackClosed FormCoefficientProductBound
  NormDifferentialChain NormDifferentialBilinearProduct NormBilinearDifferentialAlgebra
  NormHigherDifferentialFirst NormHigherDifferentialUnique ExteriorIndices CovectorProducts
  GrassmannCoordinates FiniteCoordinates EuclideanFormNorm
  DifferentialFormCoefficientMaps ExteriorDifferentialCoefficientNaturality FormCoefficientSeparation
  FormCoefficients ExteriorDifferentialUP ExteriorDifferentialSealed
  VectorFormPullbackDifferentiable RealFormPullbackDifferential NormDifferentialDirectional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section VectorPullbackDerivative.
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

Variable W:lmodType R.
Variable NW:W->R.
Hypothesis hNW:is_real_norm NW.

(** Source for [original_vector_pullback_exterior_derivative]:
    d(f# phi)=f#(d phi), Federer 4.1.6,
    pp. 354–355, for arbitrary original normed
    coefficients. The real coordinate-generator proof
    and original bounded norming functionals identify
    the actual vector derivative. Completeness and
    separability of W are not required. *)
Theorem original_vector_pullback_exterior_derivative (B:Y->Prop)
    (hImage:forall x,A x->B (f x)) a (z:Z 2%N) m
    (phi:Y->A_m Y W m) (M:Hom Y (A_m Y W m)):
  has_norm_higher_differential NX evaluation ZN A f 2%N a z->
  has_norm_differential NY (@euclidean_form_norm R h2 n W NW hNW m) B phi (f a) M->
  has_exterior_derivative NX (@euclidean_form_norm R h2 v W NW hNW m) A
    (fun x=>A_m_dual (hom_as_linear (J (F x))) (phi (f x))) a
    (A_m_dual (hom_as_linear (J (F a))) (@ExteriorDifferential.value R h2 n W m M)).
Proof.
move=>hSecond hPhi.
have [L hL]:=@original_vector_form_pullback_differentiable R h2 v n Z evaluation ZN hZ
  A f F hF W NW hNW B hImage a z m phi M hSecond hPhi.
pose b:=@ExteriorDifferential.value R h2 v W m L.
have hB:has_exterior_derivative NX (@euclidean_form_norm R h2 v W NW hNW m) A
    (fun x=>A_m_dual (hom_as_linear (J (F x))) (phi (f x))) a b.
  exists L; split; first exact:hL. exact:ExteriorDifferential.laws.
have hEqual:b=A_m_dual (hom_as_linear (J (F a))) (@ExteriorDifferential.value R h2 n W m M).
  apply:(unit_coefficient_maps_separate_forms hNW)=>T hUnit.
  have hT:norm_bounded_linear NW (fun c:R^o=>`|c|) T.
    exists 1; split; first exact:ler01.
    move=>w; rewrite mul1r; exact:hUnit.
  pose CT:=hom_of_linear (@form_coefficients R Y W R^o (hom_as_linear T) m).
  have hCT:norm_bounded_linear (@euclidean_form_norm R h2 n W NW hNW m)
      (@real_euclidean_form_norm R h2 n m) CT.
    exact:(@bounded_form_coefficient_map R Y W R^o NY NW (fun c:R^o=>`|c|)
      hNY (@scalar_absolute_value_norm R) m
      (@euclidean_form_norm R h2 n W NW hNW m) (@real_euclidean_form_norm R h2 n m)
      (@euclidean_form_norm_laws R h2 n W NW hNW m) (@real_euclidean_form_norm_laws R h2 n m) T hT).
  have hScalarPhi:=norm_differential_postcompose hNY hPhi hCT.
  have hReal:=@original_real_pullback_exterior_derivative R h2 v n Z evaluation ZN hZ
    A f F hF B hImage a z m (fun y=>form_coefficients (hom_as_linear T) (phi y))
      (hom_comp CT M) hSecond hScalarPhi.
  have hProjected:=@exterior_derivative_change_coefficients R X W R^o NX NW (fun c:R^o=>`|c|)
    hNX (@scalar_absolute_value_norm R) m
    (@euclidean_form_norm R h2 v W NW hNW m) (@real_euclidean_form_norm R h2 v m)
    (@euclidean_form_norm_laws R h2 v W NW hNW m) (@real_euclidean_form_norm_laws R h2 v m)
    T A (fun x=>A_m_dual (hom_as_linear (J (F x))) (phi (f x))) a b hT hB.
  have hFunction:
      (fun x=>form_coefficients (hom_as_linear T)
        (A_m_dual (hom_as_linear (J (F x))) (phi (f x))))=
      (fun x=>A_m_dual (hom_as_linear (J (F x))) (form_coefficients (hom_as_linear T) (phi (f x)))).
    apply:funext=>x; exact:original_pullback_change_coefficients.
  rewrite hFunction in hProjected.
  have hScalarEqual:=@exterior_derivative_unique R X R^o NX hNX m
    (@real_euclidean_form_norm R h2 v m) (@real_euclidean_form_norm_norm R h2 v m) A
    (fun x=>A_m_dual (hom_as_linear (J (F x))) (form_coefficients (hom_as_linear T) (phi (f x)))) a
    (form_coefficients (hom_as_linear T) b)
    (A_m_dual (hom_as_linear (J (F a))) (@ExteriorDifferential.value R h2 n R^o m (hom_comp CT M)))
    hProjected hReal.
  have hNatural:=@exterior_differential_change_coefficients R h2 n W R^o T m M.
  rewrite -hNatural in hScalarEqual.
  rewrite original_pullback_change_coefficients; exact:hScalarEqual.
by rewrite -hEqual.
Qed.
End VectorPullbackDerivative.
