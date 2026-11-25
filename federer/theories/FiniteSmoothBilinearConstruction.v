(** Federer (1969), 4.1.7, pp. 355–356:
    construct fixed smooth coefficient operations by
    the original finite coordinate expansion of 4.1.6,
    p. 352. Existing scalar multipliers and constant
    coefficient maps supply each term. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP NormRegularity
  LinearBasis FiniteDualDimension Annihilator CoefficientCoordinates NormFiniteLinearBound NormSmoothPostcompose
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothMultiplierUP SmoothMultiplierSealed
  SmoothTargetOperatorUP SmoothTargetOperatorSealed SmoothBilinearMultiplierUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section FiniteSmoothBilinearConstruction.
Variable R:realType.
Variables X Y1 Y2 Y3:lmodType R.
Variables (NX:X->R) (N1:Y1->R) (N2:Y2->R) (N3:Y3->R).
Hypotheses (hNX:is_real_norm NX) (hN1:is_real_norm N1)
  (hN2:is_real_norm N2) (hN3:is_real_norm N3).
Variable U:X->Prop.
Variables E1 E2 E3:lmodType R.
Variables (v1:E1->X->Y1) (v2:E2->X->Y2) (v3:E3->X->Y3).
Hypothesis hE1:is_smooth_function_space hNX hN1 U v1.
Hypothesis hE2:is_smooth_function_space hNX hN2 U v2.
Hypothesis hE3:is_smooth_function_space hNX hN3 U v3.
Variables n1 n2:nat.
Variable b1:'I_n1->Y1.
Variable b2:'I_n2->Y2.
Hypotheses (hb1:is_basis b1) (hb2:is_basis b2).
Variable B:Y1->Y2->Y3.
Hypothesis hB:bilinear B.
Variable u:E1.

(** Source for [finite_smooth_bilinear_scalar]: original
    scalar coordinates of the fixed smooth field,
    supporting Federer 4.1.7, pp. 355–356. *)
Definition finite_smooth_bilinear_scalar (i:'I_n1):X->R:=
  fun x=>dual_basis hb1 i (v1 u x).

(** Source for [finite_smooth_bilinear_scalar_regular]:
    those coordinates are actual smooth scalars,
    supporting Federer 4.1.7, pp. 355–356. *)
Lemma finite_smooth_bilinear_scalar_regular i:
  norm_class_all_orders hNX (@scalar_absolute_value_norm R) U (finite_smooth_bilinear_scalar i).
Proof.
have hBound:=@norm_finite_linear_bounded R Y1 R^o N1 (fun c:R^o=>`|c|)
  hN1 (@scalar_absolute_value_norm R) n1 b1 hb1 (dual_basis hb1 i).
exact:(@norm_smooth_postcompose R X Y1 R^o NX N1 (fun c:R^o=>`|c|)
  hNX hN1 (@scalar_absolute_value_norm R) U (v1 u) (dual_basis hb1 i) hBound
  (smooth_function_evaluation_smooth hE1 u)).
Qed.

(** Source for [finite_smooth_bilinear_left_map]: fixed
    coordinate coefficient operation, supporting the
    current products of Federer 4.1.7, pp. 355–356. *)
Definition finite_smooth_bilinear_left_map (i:'I_n1):Hom Y2 Y3:=
  @HomMap R Y2 Y3 (fun y=>B (b1 i) y) (introT (asboolP _) (hB.2 (b1 i))).

(** Source for [finite_smooth_bilinear_left_bounded]:
    constant coefficient maps are bounded on the
    original finite coefficient space, supporting
    Federer 4.1.7, pp. 355–356. *)
Lemma finite_smooth_bilinear_left_bounded i:
  norm_bounded_linear N2 N3 (finite_smooth_bilinear_left_map i).
Proof. exact:(@norm_finite_linear_bounded R Y2 Y3 N2 N3 hN2 hN3 n2 b2 hb2 _). Qed.

(** Source for [finite_smooth_bilinear_scalar_operator]:
    the earlier actual smooth scalar multiplier,
    supporting Federer 4.1.7, pp. 355–356. *)
Definition finite_smooth_bilinear_scalar_operator i:Hom E2 E2:=
  @SmoothMultiplier.operator R X Y2 NX N2 hNX hN2 U E2 v2 hE2
    (finite_smooth_bilinear_scalar i) (finite_smooth_bilinear_scalar_regular i).

(** Source for [finite_smooth_bilinear_target_operator]:
    the earlier actual constant coefficient map,
    supporting Federer 4.1.7, pp. 355–356. *)
Definition finite_smooth_bilinear_target_operator i:Hom E2 E3:=
  @SmoothTargetOperator.operator R X Y2 Y3 NX N2 N3 hNX hN2 hN3 U E2 E3 v2 v3 hE2 hE3
    (finite_smooth_bilinear_left_map i) (finite_smooth_bilinear_left_bounded i).

(** Source for [finite_smooth_bilinear_term]: one
    original coordinate term, supporting Federer
    4.1.7, pp. 355–356. *)
Definition finite_smooth_bilinear_term i:Hom E2 E3:=
  hom_comp (finite_smooth_bilinear_target_operator i) (finite_smooth_bilinear_scalar_operator i).

(** Source for [finite_smooth_bilinear_witness]: finite
    coordinate construction used only to prove the
    original operator exists, supporting Federer
    4.1.7, pp. 355–356. *)
Definition finite_smooth_bilinear_witness:Hom E2 E3:=\sum_i finite_smooth_bilinear_term i.

(** Source for [finite_smooth_bilinear_scalar_expansion]:
    original expansion of the fixed coefficient
    field, supporting Federer 4.1.7, pp. 355–356. *)
Lemma finite_smooth_bilinear_scalar_expansion x:
  v1 u x=\sum_i finite_smooth_bilinear_scalar i x *: b1 i.
Proof. exact:(@basis_vector_expansion R Y1 n1 b1 hb1 (v1 u x)). Qed.

(** Source for [finite_smooth_bilinear_term_value]: exact
    original value of each coordinate term,
    supporting Federer 4.1.7, pp. 355–356. *)
Lemma finite_smooth_bilinear_term_value i f x:U x->
  v3 (finite_smooth_bilinear_term i f) x=
    finite_smooth_bilinear_scalar i x *: B (b1 i) (v2 f x).
Proof.
move=>hx.
have hT:=@SmoothTargetOperator.laws R X Y2 Y3 NX N2 N3 hNX hN2 hN3 U E2 E3 v2 v3 hE2 hE3
  (finite_smooth_bilinear_left_map i) (finite_smooth_bilinear_left_bounded i)
  (finite_smooth_bilinear_scalar_operator i f) x hx.
have hS:=@SmoothMultiplier.laws R X Y2 NX N2 hNX hN2 U E2 v2 hE2
  (finite_smooth_bilinear_scalar i) (finite_smooth_bilinear_scalar_regular i) f x hx.
rewrite /finite_smooth_bilinear_term hom_compE hT hS /finite_smooth_bilinear_left_map /=.
exact:(bilZr hB).
Qed.

(** Source for [finite_smooth_bilinear_witness_values]:
    the finite construction has precisely the original
    pointwise bilinear action, supporting Federer
    4.1.7, pp. 355–356. *)
Theorem finite_smooth_bilinear_witness_values:
  is_smooth_bilinear_multiplier U v1 v2 v3 u B finite_smooth_bilinear_witness.
Proof.
move=>f x hx.
rewrite /finite_smooth_bilinear_witness hom_sum_coefficientsE.
change (smooth_function_values_hom hE3 (\sum_i finite_smooth_bilinear_term i f) x=
  B (v1 u x) (v2 f x)).
rewrite linear_sum fct_sumE.
change (\sum_i v3 (finite_smooth_bilinear_term i f) x=B (v1 u x) (v2 f x)).
under eq_bigr do rewrite (finite_smooth_bilinear_term_value _ _ hx).
rewrite (finite_smooth_bilinear_scalar_expansion x).
pose L:Hom Y1 Y3:=@HomMap R Y1 Y3 (fun z=>B z (v2 f x))
  (introT (asboolP _) (hB.1 (v2 f x))).
symmetry.
change (L (\sum_i finite_smooth_bilinear_scalar i x *: b1 i)=
  \sum_i finite_smooth_bilinear_scalar i x *: L (b1 i)).
rewrite linear_sum; apply:eq_bigr=>i _; exact:linearZ.
Qed.

End FiniteSmoothBilinearConstruction.
