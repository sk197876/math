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
  GrassmannCoordinates FiniteCoordinates EuclideanFormNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section VectorPullbackDifferentiability.
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

(** Source for [original_vector_form_pullback_differentiable]:
    the actual pullback is differentiable under the
    hypotheses of Federer 4.1.6, pp. 354–355.
    The original finite coordinate expansion reduces
    this to coefficient functions and the proved
    closed coordinate products, with arbitrary W. *)
Theorem original_vector_form_pullback_differentiable (B:Y->Prop)
    (hImage:forall x,A x->B (f x)) a (z:Z 2%N) m
    (phi:Y->A_m Y W m) (M:Hom Y (A_m Y W m)):
  has_norm_higher_differential NX evaluation ZN A f 2%N a z->
  has_norm_differential NY (@euclidean_form_norm R h2 n W NW hNW m) B phi (f a) M->
  norm_differentiable_at NX (@euclidean_form_norm R h2 v W NW hNW m) A
    (fun x=>A_m_dual (hom_as_linear (J (F x))) (phi (f x))) a.
Proof.
move=>hSecond hPhi.
have ha:=norm_higher_differential_domain hNX hSecond.
have hFirst:=(@norm_higher_differential_first R X Y NX NY hNX hNY
  Z evaluation ZN hZ A f a (F a)).1 (@hF a ha).
pose P:=@euclidean_form_norm R h2 v W NW hNW m.
pose PN:=@real_euclidean_form_norm R h2 v m.
have hPN:=@real_euclidean_form_norm_norm R h2 v m.
have hP:=@euclidean_form_norm_real_norm R h2 v W NW hNW m.
pose cmap (lambda:Lambda n m):=@original_form_coefficient_map R Y W m
  (e_lambda (@coordinate_basis R n) (val lambda)).
pose coeff (lambda:Lambda n m):=hom_comp (cmap lambda) M.
pose omega:=@omega_lambda R h2 Y n (@euclidean_coordinate_form R n) m.
pose psi (lambda:Lambda n m) (x:X):=A_m_dual (hom_as_linear (J (F x))) (omega lambda).
pose terms (lambda:Lambda n m) (x:X):=form_with_coefficient (cmap lambda (phi (f x))) (psi lambda x).
have hTerms (lambda:Lambda n m):norm_differentiable_at NX P A (terms lambda) a.
  have hCoeff:=@original_form_coefficient_differential R n W m NW
    (@euclidean_form_norm R h2 n W NW hNW m) (@euclidean_form_norm_laws R h2 n W NW hNW m)
    B phi (f a) M hPhi lambda.
  have hChain:=norm_differential_chain hNX hNY hNW hFirst hCoeff.
  have hRestricted:=norm_differential_restrict (fun x hx=>conj hx (@hImage x hx))
    (norm_differential_interior hFirst) hChain.
  have hClosed:=@original_coordinate_product_pullback_closed R h2 v n Z evaluation ZN hZ A f F hF
    a z m lambda hSecond.
  have [D [hD _]]:has_exterior_derivative NX PN A (psi lambda) a 0:=hClosed.
  have hBound:forall w b,P (form_with_coefficient w b)<=1*(NW w*PN b).
    move=>w b; rewrite mul1r.
    exact:(@form_with_coefficient_norm_bound R X W NX NW hNX hNW m PN P
      (@real_euclidean_form_norm_laws R h2 v m) (@euclidean_form_norm_laws R h2 v W NW hNW m) w b).
  exists (norm_bilinear_product_linear_term (@form_with_coefficient_bilinear R X W m)
    (cmap lambda (phi (f a))) (psi lambda a) (hom_comp (coeff lambda) (J (F a))) D).
  exact:(@norm_differential_bilinear_product R X W (A_m X R^o m) (A_m X W m)
    NX NW PN P hNX hNW hPN hP (@form_with_coefficient R X W m)
    (@form_with_coefficient_bilinear R X W m) 1 A
    (fun x=>cmap lambda (phi (f x))) (psi lambda) a
    (hom_comp (coeff lambda) (J (F a))) D (ler01) hBound hRestricted hD).
have hTotal:=norm_differentiable_finite_sum hNX hP (norm_differential_interior hFirst) hTerms.
have hFunction:(\sum_(lambda:Lambda n m) terms lambda)=
    (fun x=>A_m_dual (hom_as_linear (J (F x))) (phi (f x))).
  apply:funext=>x; rewrite fct_sumE.
  rewrite {1}(@original_form_coefficient_expansion R h2 Y W n m (@coordinate_basis R n)
    (@coordinate_basisP R n) (@euclidean_coordinate_form R n) (@euclidean_coordinate_form_dual R n)
    (phi (f x))) linear_sum.
  apply:eq_bigr=>lambda _.
  change (form_with_coefficient (cmap lambda (phi (f x))) (psi lambda x)=
    A_m_dual (hom_as_linear (J (F x)))
      (form_with_coefficient (cmap lambda (phi (f x))) (omega lambda))).
  exact:(esym (@coefficient_form_pullback R X Y W (J (F x)) m
    (cmap lambda (phi (f x))) (omega lambda))).
by rewrite hFunction in hTotal.
Qed.
End VectorPullbackDifferentiability.
