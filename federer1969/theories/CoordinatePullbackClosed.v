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
  ExteriorDerivativeUP SymmetricOneFormClosed RealDifferentialFormCalculus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CoordinatePullbackClosed.
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

(** Source for [original_coordinate_pullback_closed]:
    d(f# DX_j)=d(d(f# X_j))=0,
    the second generator case in Federer
    4.1.6, p. 355, using the original
    actual first and second differentials. *)
Theorem original_coordinate_pullback_closed a (z:Z 2%N) (j:'I_n):
  has_norm_higher_differential NX evaluation ZN A f 2%N a z->
  has_real_form_derivative h2 A
    (fun x=>A_m_dual (hom_as_linear (J (F x))) (euclidean_coordinate_form j)) a 0.
Proof.
move=>hSecond.
have [L [hL hValues]]:=norm_higher_differential_field_step_elim hNX hF hSecond.
have hSym:forall u w,J (L u) w=J (L w) u.
  move=>u w.
  change (@evaluation 1%N [ffun i:'I_1=>w] (L u)=@evaluation 1%N [ffun i:'I_1=>u] (L w)).
  rewrite !hValues.
  exact:(@norm_second_differential_symmetric R X Y NX NY hNX hNY
    Z evaluation ZN hZ A f a z hSecond w u).
have [K [hValuesK hBoundK]]:=@one_form_postoperator_exists R X Y R^o (Z 1%N)
  NX NY (fun c:R^o=>`|c|) (@real_euclidean_form_norm R h2 v 1)
  (@real_euclidean_form_norm_laws R h2 v 1) J (@ZN 1%N)
  (@continuous_multilinear_one_operator_space R X Y (Z 1%N) NX NY
    (@evaluation 1%N) (@ZN 1%N) (@hZ 1%N))
  (@euclidean_scalar_coordinate_map R n j) (@euclidean_scalar_coordinate_bounded R n j).
have hDerivative:=norm_differential_postcompose hNX hL hBoundK.
have hFunction:(fun x=>K (F x))=
    (fun x=>A_m_dual (hom_as_linear (J (F x))) (euclidean_coordinate_form j)).
  apply:funext=>x.
  apply:(can_inj (@one_homK R X R^o)); apply:hom_ext=>u.
  rewrite /euclidean_coordinate_form original_pullback_one_form one_formK hom_compE.
  exact:hValuesK.
rewrite hFunction in hDerivative.
exists (hom_comp K L); split; first exact:hDerivative.
apply:symmetric_one_form_exterior_value_zero=>u w.
rewrite !hom_compE !hValuesK hSym.
by [].
Qed.
End CoordinatePullbackClosed.
