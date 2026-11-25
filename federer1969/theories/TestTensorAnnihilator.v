(** Federer (1969), 4.1.3, p. 348: a continuous real functional is determined on the
    original pure coordinate tests by 4.1.3, p. 348.
    This supporting theorem reuses that density result with
    the literal final topology and the tensor universal properties. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import Hom TensorUP TensorFamilyUP RealNormUP NormMetric CompleteMetricUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  TestTensorMapUP TestTensorDensityTheorem DenseImageScalarZero OpenFamilyTopologyUP NormOpenTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section TestTensorAnnihilator.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable A:lmodType R.
Variable av:A->R^o->R^o.
Hypothesis hA:is_smooth_function_space hR hR (fun _=>True) av.
Local Notation D1 := (smooth_test_space hA).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y N NY hN hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Variable T W:lmodType R.
Variable mu:{dffun forall i:'I_n,D1}->T.
Variable nu:T->Y->W.

(** Source for [test_tensor_annihilator_zero]: a continuous
    real linear functional vanishing on every original pure
    coordinate test tensor vanishes on every test, supporting
    Federer 4.1.8, p. 360, by the complete original
    tensor-density assertion 4.1.3, p. 348. *)
Theorem test_tensor_annihilator_zero (F:Hom W DT) (L:Hom DT R^o):
  is_tensor_product_family mu->is_tensor_product nu->
  is_test_tensor_map hA hE mu nu F->
  open_family_continuous (smooth_test_opens hE hD)
    (norm_open_family (@scalar_absolute_value_norm R)) L->
  (forall f y,L (F (nu (mu f) y))=0)->forall phi,L phi=0.
Proof.
move=>hMu hNu hF hContinuous hZero.
pose J:=hom_comp L F.
have hPure:forall t y,J (nu t y)=0.
  move=>t y.
  have hLinear:linear (fun t=>J (nu t y)).
    move=>c u v;rewrite ((tensor_bilinear hNu).1 y) (hom_linear J).
    reflexivity.
  pose H:Hom T R^o:=@HomMap R T R^o (fun t=>J (nu t y)) (introT (asboolP _) hLinear).
  pose Z0:{linear T->R^o}:=GRing.Linear.clone _ _ _ _ (\0:T->R^o) _.
  apply:(tensor_family_ext hMu (hom_as_linear H) Z0) t=>f.
  exact:(hZero f y).
have hImage:forall w,L (F w)=0.
  pose Z0:{linear W->R^o}:=GRing.Linear.clone _ _ _ _ (\0:W->R^o) _.
  apply:(tensor_ext hNu (hom_as_linear J) Z0)=>t y.
  exact:hPure.
apply:(@dense_image_scalar_zero R DT W (smooth_test_opens hE hD) F L).
- exact:(@test_tensor_map_dense R n A av hA Y NY hNY hY E ev hE D hD T W mu nu F hF).
- exact:hContinuous.
- exact:hImage.
Qed.
End TestTensorAnnihilator.
