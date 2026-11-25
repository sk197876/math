(** Federer (1969), 3.2.28(1), printed p. 263:
    apply the regular-level theorem in a suitable finite
    inner-product ambient space. Isometric source coordinates
    preserve the metric; target coordinates need only be invertible. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP RealNormUP LinearBasis FiniteDimension
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerProductUP
  InnerNorm HilbertFormCompactness NormDifferentialUP NormLinearIsometryInverse
  NormFiniteLinearBound NormClassOneUP NormClassOneLinearConjugate
  NormRegularity NormRegularityLinearMaps FiniteInnerChartUP FiniteInnerChart
  FiniteInnerSubmanifoldUP RegularFibreSubmanifold.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_regular_fibre_submanifold]: the
    regular-level argument for P into Y_m, Federer
    3.2.28(1), p. 263, in actual finite ambient
    inner-product spaces. All coordinate choices remain local
    to existence, and all surjectivity hypotheses refer to
    the actual differential at points of the stated fibre. *)
Theorem finite_inner_regular_fibre_submanifold (R:realType)
    (X Y:lmodType R) (B:X->X->R) (hB:is_inner_product B)
    (NY:Y->R) (hNY:is_real_norm NY) N (b:'I_N->X) (hb:is_basis b)
    q (d:'I_q->Y) (hd:is_basis d) k (f:X->Y) (D:X->Hom X Y) (c:Y):
  (1<=k)%N ->
  norm_class (inner_norm_real_norm hB) hNY (fun _=>True) f k ->
  is_norm_class_one_field (inner_norm hB) NY (fun _=>True) f D ->
  (forall x,f x=c ->forall y,exists z,D x z=y) ->
  is_inner_submanifold B (N-q) k [set x|f x=c].
Proof.
move=>hk hf hD hSurj.
have [e [p hChart]]:=finite_inner_chart_exists hB hb.
pose A:=R_n R N; pose C:=R_n R q.
pose NX:=inner_norm hB; pose NA:=inner_norm (@euclidean_inner_productP R N).
pose NC:=inner_norm (@euclidean_inner_productP R q).
pose hNX:=inner_norm_real_norm hB.
pose hNA:=inner_norm_real_norm (@euclidean_inner_productP R N).
pose hNC:=inner_norm_real_norm (@euclidean_inner_productP R q).
pose u:Hom C Y:=hom_of_linear
  (@finite_basis_synthesis R (Finite.clone 'I_q _) Y d).
pose v:Hom Y C:=hom_of_linear
  (@finite_basis_coordinates R (Finite.clone 'I_q _) Y d hd).
have hUV:cancel u v:=@finite_basis_synthesisK R (Finite.clone 'I_q _) Y d hd.
have hVU:cancel v u:=@finite_basis_coordinatesK R (Finite.clone 'I_q _) Y d hd.
have hVinj:injective v:=can_inj hVU.
have hEbound:norm_bounded_linear NA NX e.
  apply:norm_linear_isometry_bounded=>z.
  exact:(@finite_inner_chart_norm R X B hB N e p hChart z).
have hVbound:norm_bounded_linear NY NC v:=norm_finite_linear_bounded hNY hNC hd v.
pose F (a:A):C:=v (f (e a)).
pose DF (a:A):Hom A C:=hom_comp v (hom_comp (D (e a)) e).
have hPre:=@norm_class_precompose_linear R A X Y NA NX NY hNA hNX hNY
  (fun _=>True) f e k hEbound hf.
have hF:=@norm_class_postcompose_linear R A Y C NA NY NC hNA hNY hNC
  (fun _=>True) (fun a=>f (e a)) v k hVbound hPre.
have hDF:=@norm_class_one_full_linear_conjugate R A X Y C NA NX NY NC
  hNA hNX hNY hNC e v f D hEbound hVbound hD.
have hSurjF a (ha:F a=v c):forall y,exists z,DF a z=y.
  have hfc:f (e a)=c:=hVinj _ _ ha.
  move=>y; have [z hz]:=hSurj (e a) hfc (u y).
  exists (p z); rewrite /DF !hom_compE
    (finite_inner_chart_right_inverse hChart) hz hUV; reflexivity.
have hManifold:=@regular_fibre_submanifold R N q k F DF (v c) hk hF hDF hSurjF.
exists N,e,p; split; first exact:hChart.
have hImage:p @` [set x|f x=c]=[set a|F a=v c].
  apply/seteqP; split=>a.
  - move=>[x hx <-]; change (v (f (e (p x)))=v c).
    by rewrite (finite_inner_chart_right_inverse hChart) hx.
  - move=>ha; exists (e a).
    + exact:(hVinj _ _ ha).
    + exact:(finite_inner_chart_left_inverse hChart a).
by rewrite hImage.
Qed.
