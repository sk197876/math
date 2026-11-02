(** Federer (1969), 3.2.28(1), printed p. 263:
    identify the actual regular-fibre tangent in its
    finite inner-product ambient space, using only
    invertible linear coordinate and tangent-image laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP RealNormUP LinearBasis FiniteDimension
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerProductUP
  InnerNorm HilbertFormCompactness NormDifferentialUP NormLinearIsometryInverse
  NormFiniteLinearBound NormClassOneUP NormClassOneLinearConjugate
  FiniteInnerChartUP FiniteInnerChart TangentConeUP
  NormLinearIsomorphismTangent RegularFibreTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_regular_fibre_tangent]: the
    exact tangent kernel used in Federer 3.2.28(1),
    p. 263, in the original inner-product ambient
    space. Surjectivity is required only at the stated
    point; the coordinate witnesses stay local to this proof. *)
Theorem finite_inner_regular_fibre_tangent (R:realType)
    (X Y:lmodType R) (B:X->X->R) (hB:is_inner_product B)
    (NY:Y->R) (hNY:is_real_norm NY) N (b:'I_N->X) (hb:is_basis b)
    q (d:'I_q->Y) (hd:is_basis d) (f:X->Y) (D:X->Hom X Y) a:
  is_norm_class_one_field (inner_norm hB) NY (fun _=>True) f D ->
  (forall y,exists z,D a z=y) ->
  norm_tangent_cone (inner_norm hB) [set x|f x=f a] a=[set w|D a w=0].
Proof.
move=>hD hSurj.
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
have hPbound:norm_bounded_linear NX NA p.
  apply:norm_linear_isometry_bounded=>z.
  exact:(@finite_inner_chart_inverse_norm R X B hB N e p hChart z).
have hVbound:norm_bounded_linear NY NC v:=norm_finite_linear_bounded hNY hNC hd v.
pose F (z:A):C:=v (f (e z)).
pose DF (z:A):Hom A C:=hom_comp v (hom_comp (D (e z)) e).
have hDF:=@norm_class_one_full_linear_conjugate R A X Y C NA NX NY NC
  hNA hNX hNY hNC e v f D hEbound hVbound hD.
have hSurjF:forall y,exists z,DF (p a) z=y.
  move=>y; have [z hz]:=hSurj (u y).
  exists (p z); rewrite /DF !hom_compE
    !(finite_inner_chart_right_inverse hChart) hz hUV; reflexivity.
have hT:=@regular_fibre_tangent R N q F DF (p a) hDF hSurjF.
pose W:= [set x:X|f x=f a].
have hSource:p @` W=[set z:A|F z=F (p a)].
  apply/seteqP; split=>z.
  - move=>[x hx <-]; change (v (f (e (p x)))=v (f (e (p a)))).
    by rewrite !(finite_inner_chart_right_inverse hChart) hx.
  - move=>hz; exists (e z).
    + apply:hVinj; change (v (f (e z))=v (f a)).
      have hh:F z=F (p a):=hz.
      by rewrite /F (finite_inner_chart_right_inverse hChart) in hh.
    + exact:(finite_inner_chart_left_inverse hChart z).
have hImage:e @` (p @` W)=W.
  apply/seteqP; split=>x.
  - move=>[z [y hy <-] <-]; by rewrite (finite_inner_chart_right_inverse hChart).
  - move=>hx; exists (p x).
    + by exists x.
    + exact:(finite_inner_chart_right_inverse hChart x).
have hTransport:=@norm_linear_isomorphism_tangent_image R A X NA NX hNA hNX
  e p (p @` W) (p a) hEbound hPbound
  (finite_inner_chart_left_inverse hChart) (finite_inner_chart_right_inverse hChart).
rewrite hImage (finite_inner_chart_right_inverse hChart) in hTransport.
rewrite -hSource in hT.
have hKernel:e @` [set z:A|DF (p a) z=0]=[set w:X|D a w=0].
  apply/seteqP; split=>w.
  - move=>[z hz <-].
    have hh:v (D a (e z))=0.
      have hz':DF (p a) z=0:=hz.
      change (v (D (e (p a)) (e z))=0) in hz'.
      by rewrite (finite_inner_chart_right_inverse hChart) in hz'.
    apply:hVinj; by rewrite linear0.
  - move=>hw; exists (p w); last exact:(finite_inner_chart_right_inverse hChart w).
    change (v (D (e (p a)) (e (p w)))=0).
    by rewrite !(finite_inner_chart_right_inverse hChart) hw linear0.
rewrite hT hKernel in hTransport; exact:esym hTransport.
Qed.
