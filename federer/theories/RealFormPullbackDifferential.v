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
  AlternatingProduct ScalarCoefficients ExteriorIndices CovectorProducts GrassmannCoordinates FiniteCoordinates
  ExteriorDifferentialSealed ExteriorDifferentialCoefficients OriginalFormCoefficientDifferentials
  CoordinateProductPullbackClosed ClosedScalarFormProduct ExteriorDerivativeFiniteSum
  NormDifferentialChain NormHigherDifferentialFirst NormHigherDifferentialUnique.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section RealPullbackDerivative.
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

(** Source for [original_real_pullback_exterior_derivative]:
    d(f# phi)=f#(d phi), Federer 4.1.6,
    pp. 354–355, for the original real forms.
    The proof follows the scalar coefficients and
    closed coordinate products. Twice differentiability
    at a and differentiability of phi at f(a)
    suffice; no continuous second derivative is assumed. *)
Theorem original_real_pullback_exterior_derivative (B:Y->Prop)
    (hImage:forall x,A x->B (f x)) a (z:Z 2%N) m
    (phi:Y->A_m Y R^o m) (M:Hom Y (A_m Y R^o m)):
  has_norm_higher_differential NX evaluation ZN A f 2%N a z->
  has_norm_differential NY (@real_euclidean_form_norm R h2 n m) B phi (f a) M->
  has_real_form_derivative h2 A
    (fun x=>A_m_dual (hom_as_linear (J (F x))) (phi (f x))) a
    (A_m_dual (hom_as_linear (J (F a))) (@ExteriorDifferential.value R h2 n R^o m M)).
Proof.
move=>hSecond hPhi.
have ha:=norm_higher_differential_domain hNX hSecond.
have hFirst:=(@norm_higher_differential_first R X Y NX NY hNX hNY
  Z evaluation ZN hZ A f a (F a)).1 (@hF a ha).
pose cmap (lambda:Lambda n m):=@original_form_coefficient_map R Y R^o m
  (e_lambda (@coordinate_basis R n) (val lambda)).
pose coeff (lambda:Lambda n m):=hom_comp (cmap lambda) M.
pose omega:=@omega_lambda R h2 Y n (@euclidean_coordinate_form R n) m.
pose psi (lambda:Lambda n m) (x:X):=A_m_dual (hom_as_linear (J (F x))) (omega lambda).
pose terms (lambda:Lambda n m) (x:X):=cmap lambda (phi (f x))*:psi lambda x.
have hTerms (lambda:Lambda n m):exists d:A_m X R^o m.+1,
    has_real_form_derivative h2 A (terms lambda) a d /\
    form_include d=alternating_wedge h2 (scalar_bilinear R)
      (form_include (one_form (hom_comp (coeff lambda) (J (F a))))) (form_include (psi lambda a)).
  have hCoeff:=@original_form_coefficient_differential R n R^o m (fun c:R^o=>`|c|)
    (@real_euclidean_form_norm R h2 n m) (@real_euclidean_form_norm_laws R h2 n m)
    B phi (f a) M hPhi lambda.
  have hChain:=norm_differential_chain hNX hNY (@scalar_absolute_value_norm R) hFirst hCoeff.
  have hRestricted:=norm_differential_restrict (fun x hx=>conj hx (@hImage x hx))
    (norm_differential_interior hFirst) hChain.
  have hClosed:=@original_coordinate_product_pullback_closed R h2 v n Z evaluation ZN hZ A f F hF
    a z m lambda hSecond.
  exact:(@real_closed_form_scalar_product_derivative R h2 v m A
    (fun x=>cmap lambda (phi (f x))) (psi lambda) a (hom_comp (coeff lambda) (J (F a))) hRestricted hClosed).
pose d lambda:=sval (constructive_indefinite_description (hTerms lambda)).
have hd lambda:=svalP (constructive_indefinite_description (hTerms lambda)).
have hTotal:=@exterior_derivative_finite_sum R h2 v R^o NX hNX m
  (@real_euclidean_form_norm R h2 v m) (@real_euclidean_form_norm_norm R h2 v m)
  A a (Finite.clone (Lambda n m) _) terms d (norm_differential_interior hFirst) (fun lambda=>(hd lambda).1).
have hFunction:(\sum_(lambda:Lambda n m) terms lambda)=
    (fun x=>A_m_dual (hom_as_linear (J (F x))) (phi (f x))).
  apply:funext=>x; rewrite fct_sumE.
  rewrite {1}(euclidean_real_form_coordinate_expansion h2 (phi (f x))) linear_sum.
  apply:eq_bigr=>lambda _; by rewrite linearZ.
rewrite hFunction in hTotal.
have hTarget:
  form_include (A_m_dual (hom_as_linear (J (F a))) (@ExteriorDifferential.value R h2 n R^o m M))=
  \sum_(lambda:Lambda n m) alternating_wedge h2 (scalar_bilinear R)
    (form_include (one_form (hom_comp (coeff lambda) (J (F a))))) (form_include (psi lambda a)).
  rewrite -A_star_dual_include exterior_differential_coefficient_formula linear_sum.
  apply:eq_bigr=>lambda _.
  change (A_star_dual (hom_as_linear (J (F a)))
    (alternating_wedge h2 (scalar_bilinear R) (form_include (one_form (coeff lambda)))
      (form_include (omega lambda)))=
    alternating_wedge h2 (scalar_bilinear R)
      (form_include (one_form (hom_comp (coeff lambda) (J (F a))))) (form_include (psi lambda a))).
  rewrite A_star_dual_multiplicative !A_star_dual_include original_pullback_one_form.
  by [].
have hEqual:(\sum_(lambda:Lambda n m) d lambda)=
    A_m_dual (hom_as_linear (J (F a))) (@ExteriorDifferential.value R h2 n R^o m M).
  apply:(can_inj (@form_includeK R X R^o m.+1)).
  rewrite hTarget linear_sum; apply:eq_bigr=>lambda _; exact:(hd lambda).2.
by rewrite -hEqual.
Qed.
End RealPullbackDerivative.
