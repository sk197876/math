(** Federer (1969), 3.1.21, p. 234: the tangent
    space of the local image at a generic value is the
    image of the differential, through the chart laws of 3.1.18. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric NormDifferentialUP NormFiniteLinearBound
  EuclideanBlockLinearMaps LinearRangeProjectionUP ConstantRankChartUP ConstantRankSectionImage TangentConeUP SectionTangentImage
  FiniteNormLinearRangeClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [constant_rank_image_tangent]: Tan[f(U),f(a)]
    equals im Df(a), the second constant-rank identity in
    Federer 3.1.21, p. 234. The section derivative
    is the normalized p* of 3.1.18; inverse continuity is
    proved from p psi=id, including rank and ambient dimension zero. *)
Theorem constant_rank_image_tangent (R:realType) v l n k
    (A U:set (R_n R (v+l))) (f:R_n R (v+l)->R_n R n)
    (D:R_n R (v+l)->Hom (R_n R (v+l)) (R_n R n)) a e p j g G psi :
  @is_euclidean_constant_rank_chart R v l n k A f D a U e p j g G psi ->
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) (f @` U) (f a)=range (D a).
Proof.
move=>hC.
pose V:=R_n R v.
pose Y:=R_n R n.
pose NV:=inner_norm (@euclidean_inner_productP R v).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNV:=inner_norm_real_norm (@euclidean_inner_productP R v).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose T:=@constant_rank_parameter_domain R v l g a e.
pose u0:=@euclidean_first_block R v l (g a).
pose L:=hom_of_linear j.
pose P:=hom_of_linear p.
have hp:=@norm_finite_linear_bounded R Y V NY NV hNY hNV n
  (@coordinate_basis R n) (@coordinate_basisP R n) P.
have hclosed:=@finite_norm_linear_range_closed R V Y NY hNY n
  (@coordinate_basis R n) (@coordinate_basisP R n) L.
have hcan u (hu:T u):P (psi u)=u:=constant_rank_section_right_inverse hC hu.
have htan:=@norm_section_tangent_image R V Y NV NY hNV hNY T psi u0 L P
  (constant_rank_section_differential hC) hp hcan hclosed.
rewrite (constant_rank_section_image hC) (constant_rank_section_base hC) in htan.
have him:range L=range (D a).
  have hpr:=range_projection_image (constant_rank_projection hC).
  apply/seteqP; split=>y.
  - move=>[u _ hu].
    have [x hx]:=(hpr y).1 (ex_intro _ u hu).
    by exists x.
  - move=>[x _ hx].
    have [u hu]:=(hpr y).2 (ex_intro _ x hx).
    by exists u.
by rewrite him in htan.
Qed.
