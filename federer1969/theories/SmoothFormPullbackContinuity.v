(** Federer (1969), 4.1.7, p. 359:
    the original smooth form pullback
    is continuous for the derivative-seminorm
    topologies. Its coordinate proof reuses
    4.1.6, pp. 352, 354–355,
    smooth precomposition and multiplication by
    the fixed pulled-back coordinate products. *)
From mathcomp Require Import functions all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import AlternatingDual Hom TensorUP Bilinear RealNormUP NormDifferentialUP NormClassOneUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates FiniteExteriorPowers ExteriorIndices AlternatingForms CovectorProducts
  EuclideanCoordinateForms ExteriorDifferentialCoefficients CoefficientCoordinates
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentPullbackClass
  SmoothFormPullbackUP Distributions SmoothFunctionSpaceUP SmoothFunctionSpaceLaws
  SmoothFunctionDerivativesUP SmoothFunctionTopology OpenFamilyTopologyUP OpenFamilyFiniteHomSum
  SmoothPrecompositionUP SmoothPrecompositionSealed SmoothPrecompositionContinuity
  SmoothBilinearMultiplierUP SmoothBilinearMultiplierSealed SmoothBilinearMultiplierContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothFormPullbackContinuity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation A := (A_m X R^o m).
Local Notation B := (A_m Y R^o m).
Local Notation PN := (@current_form_comass R h2 v m).
Local Notation QN := (@current_form_comass R h2 n m).
Local Notation hPN := (@current_form_comass_real_norm R h2 v m).
Local Notation hQN := (@current_form_comass_real_norm R h2 n m).
Variables (U:X->Prop) (V:Y->Prop).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Local Notation E := (@current_smooth_space R h2 n V hV m).
Local Notation F := (@current_smooth_space R h2 v U hU m).
Local Notation ev := (@current_smooth_value R h2 n V hV m).
Local Notation fv := (@current_smooth_value R h2 v U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n V hV m).
Local Notation hF := (@current_smooth_space_laws R h2 v U hU m).
Local Notation DE := (@current_smooth_derivatives R h2 n V hV m).
Local Notation DF := (@current_smooth_derivatives R h2 v U hU m).
Local Notation hDE := (@current_smooth_derivative_laws R h2 n V hV m).
Local Notation hDF := (@current_smooth_derivative_laws R h2 v U hU m).
Local Notation G := (@distribution_smooth_space R X B NX QN hNX hQN U hU).
Local Notation gv := (@distribution_smooth_value R X B NX QN hNX hQN U hU).
Local Notation hG := (@distribution_smooth_laws R X B NX QN hNX hQN U hU).
Local Notation DG := (@distribution_smooth_derivatives R X B NX QN hNX hQN U hU).
Local Notation hDG := (@distribution_smooth_derivative_laws R X B NX QN hNX hQN U hU).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.

(** Source for [smooth_form_pullback_continuous_witness]:
    a continuous linear witness has
    the exact original pullback values,
    supporting Federer 4.1.7, p. 359.
    Its finite coordinate construction is
    confined to this existence proof. *)
Theorem smooth_form_pullback_continuous_witness:
  exists P:Hom E F,is_smooth_form_pullback U V ev fv f P /\
    open_family_continuous (smooth_function_opens hDE) (smooth_function_opens hDF) P.
Proof.
have [D hD]:=(@norm_class_firstP R X Y NX NY hNX hNY U f).1 (hf 1%N).
have hActual (x:X) (hx:U x):=norm_class_one_differential hD hx.
pose omega:=@omega_lambda R h2 Y n (@euclidean_coordinate_form R n) m.
have hGenerator (lambda:Lambda n m):exists w:F,forall x,U x->
    fv w x=A_m_dual (hom_as_linear (D x)) (omega lambda).
  apply:(smooth_function_evaluation_surjective hF).
  exact:(@current_pullback_coordinate_product_smooth R h2 v n m U hU f D hActual hf lambda).
have [w hw]:=choice hGenerator.
pose coefficient (lambda:Lambda n m):=@original_form_coefficient_map R Y R^o m
  (e_lambda (@coordinate_basis R n) (val lambda)).
pose multiply (lambda:Lambda n m) (a:A) (b:B):=coefficient lambda b*:a.
have hMultiply lambda:bilinear (multiply lambda).
  split.
  - move=>b c a d;rewrite /multiply scalerDr !scalerA;by rewrite mulrC.
  - move=>a c b d;by rewrite /multiply (linearP (coefficient lambda)) scalerDl scalerA.
pose finiteA:=@current_form_finite_basis R h2 v m.
pose finiteB:=@current_form_finite_basis R h2 n m.
pose L lambda:=@SmoothBilinearMultiplier.operator R X A B A NX PN QN PN hNX hPN hQN hPN
  U F G F fv gv fv hF hG hF finiteA finiteB (multiply lambda) (hMultiply lambda) (w lambda).
have hL lambda:=@SmoothBilinearMultiplier.laws R X A B A NX PN QN PN hNX hPN hQN hPN
  U F G F fv gv fv hF hG hF finiteA finiteB (multiply lambda) (hMultiply lambda) (w lambda).
have hLC lambda:open_family_continuous (smooth_function_opens hDG) (smooth_function_opens hDF) (L lambda).
  exact:(@smooth_bilinear_multiplier_continuous R X A B A NX PN QN PN hNX hPN hQN hPN
    U F G F fv gv fv hF hG hF finiteA finiteB (multiply lambda) (hMultiply lambda) (w lambda)
    hU DG DF hDG hDF (L lambda) (hL lambda)).
pose pre:=@SmoothPrecomposition.operator R X Y B NX NY QN hNX hNY hQN U V E G ev gv
  hE hG f hImage hf.
have hPre:=@SmoothPrecomposition.laws R X Y B NX NY QN hNX hNY hQN U V E G ev gv
  hE hG f hImage hf.
have hPreC:=@smooth_precomposition_continuous R X Y B NX NY QN hNX hNY hQN U V E G ev gv
  hE DE DG hDE hDG f hImage hf pre hPre.
pose P:=hom_comp (\sum_(lambda:Lambda n m) L lambda) pre.
exists P;split.
- move=>phi x hx;split;first exact:hImage x hx.
  exists (D x);split;first exact:hActual x hx.
  rewrite /P hom_compE hom_sum_coefficientsE.
  change (smooth_function_values_hom hF (\sum_(lambda:Lambda n m) L lambda (pre phi)) x=
    A_m_dual (hom_as_linear (D x)) (ev phi (f x))).
  rewrite linear_sum fct_sumE.
  symmetry;rewrite {1}(euclidean_real_form_coordinate_expansion h2 (ev phi (f x))) linear_sum.
  apply:eq_bigr=>lambda _.
  rewrite linearZ.
  have hTerm:=hL lambda (pre phi) x hx.
  rewrite (hw lambda x hx) (hPre phi x hx) in hTerm.
  exact:esym hTerm.
- have hSum:=@open_family_finite_hom_sum_continuous R G F
    (smooth_function_opens hDG) (smooth_function_opens hDF)
    (smooth_function_topology_laws hDG).1 (smooth_function_topology_vector hDF)
    (Finite.clone (Lambda n m) _) L hLC.
  exact:(open_family_continuous_compose hPreC hSum).
Qed.

(** Source for [smooth_form_pullback_continuous]:
    every operator satisfying the independent
    original pullback law is continuous
    for the actual smooth-space topologies,
    supporting Federer 4.1.7, p. 359.
    No coordinate witness is exposed
    and no continuity of the final
    test topology as a vector space
    is assumed. *)
Theorem smooth_form_pullback_continuous (P:Hom E F):
  is_smooth_form_pullback U V ev fv f P->
  open_family_continuous (smooth_function_opens hDE) (smooth_function_opens hDF) P.
Proof.
move=>hP.
have [Q [hQ hContinuous]]:=smooth_form_pullback_continuous_witness.
have hEqual:=@smooth_form_pullback_unique R v n m U V E F ev fv f PN hPN hF P Q hP hQ.
by rewrite hEqual.
Qed.
End SmoothFormPullbackContinuity.
