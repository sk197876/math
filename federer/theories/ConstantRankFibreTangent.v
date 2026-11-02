(** Federer (1969), 3.1.21, p. 234: tangent to a
    generic fibre, from the actual constant-rank source chart. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialUP NormClassOneUP NormDifferentialLocal
  NormDifferentialDirectional NormDifferentialFiniteCalculus NormDifferentialInverseIdentities
  NormRegularity NormDiffeomorphismUP NormFiniteLinearBound EuclideanBlockLinearMaps EuclideanProductBox
  LinearRangeProjectionUP ConstantRankChartUP TangentConeUP TangentConeLocal TangentLinearFibre NormDiffeomorphismTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [constant_rank_fibre_tangent]: the first
    constant-rank identity Tan[f^-1{f(a)},a]= ker Df(a)
    in Federer 3.1.21, p. 234. The inverse image
    uses the actual domain A. Its local source chart turns
    the fibre into an affine coordinate fibre; the kernel
    equality follows from p being injective on im Df(a). *)
Theorem constant_rank_fibre_tangent (R:realType) v l n
    (A U:set (R_n R (v+l))) (f:R_n R (v+l)->R_n R n)
    (D:R_n R (v+l)->Hom (R_n R (v+l)) (R_n R n)) a e p j g G psi :
  @is_euclidean_constant_rank_chart R v l n 1 A f D a U e p j g G psi ->
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R (v+l)))
    (inner_norm (@euclidean_inner_productP R n)) A f D ->
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R (v+l)))
    [set x|A x /\ f x= f a] a=[set w|D a w=0].
Proof.
move=>hC hD.
pose X:= R_n R (v+l).
pose Y:= R_n R n.
pose V:= R_n R v.
pose NX:= inner_norm (@euclidean_inner_productP R (v+l)).
pose NY:= inner_norm (@euclidean_inner_productP R n).
pose NV:= inner_norm (@euclidean_inner_productP R v).
pose hNX:= inner_norm_real_norm (@euclidean_inner_productP R (v+l)).
pose hNY:= inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNV:= inner_norm_real_norm (@euclidean_inner_productP R v).
pose r:=@euclidean_first_block_map R v l.
pose P:= hom_of_linear p.
pose C:=@euclidean_product_box R v l (g a) e.
pose S:= fun x=>A x /\ f x= f a.
pose T:= fun y=>r y= r (g a).
have hSource:= constant_rank_source_chart hC.
have haU:= constant_rank_base_member hC.
have hUA x (hx:U x):A x:= constant_rank_domain_subset hC hx.
have haA:= hUA a haU.
have hmap x (hx:U x):C (g x):=@norm_diffeomorphism_maps R X X NX NX hNX hNX U C g G 1 hSource x hx.
have himap y (hy:C y):U (G y):=@norm_diffeomorphism_inverse_maps R X X NX NX hNX hNX U C g G 1 hSource y hy.
have hgf x (hx:U x):G (g x)= x:=@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX U C g G 1 hSource x hx.
have hfg y (hy:C y):g (G y)= y:=@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX U C g G 1 hSource y hy.
have [Dg hDg]:=(@norm_class_firstP R X X NX NX hNX hNX U g).1
  (norm_diffeomorphism_forward_class hSource).
have [DG hDG]:=(@norm_class_firstP R X X NX NX hNX hNX C G).1
  (norm_diffeomorphism_inverse_class hSource).
have hgaC:= hmap a haU.
have hDa:= norm_class_one_differential hD haA.
have hDga:= norm_class_one_differential hDg haU.
have hDGa:= norm_class_one_differential hDG hgaC.
have hintU:= norm_differential_interior hDga.
have hintC:= norm_differential_interior hDGa.
have hDaU:=@norm_differential_restrict R X Y NX NY A U f a (D a) hUA hintU hDa.
have hp:=@norm_finite_linear_bounded R Y V NY NV hNY hNV n
  (@coordinate_basis R n) (@coordinate_basisP R n) P.
have hr:=@norm_finite_linear_bounded R X V NX NV hNX hNV (v+l)
  (@coordinate_basis R (v+l)) (@coordinate_basisP R (v+l)) r.
have hrd:=@norm_differential_postcompose R X X V NX NX NV hNX U g a (Dg a) r hDga hr.
have hpd:=@norm_differential_postcompose R X Y V NX NY NV hNX U f a (D a) P hDaU hp.
have hprefix x (hx:U x):r (g x)= P (f x):= constant_rank_source_prefix hC hx.
have hEq:=@norm_differential_unique R X V NX NV hNX hNV U (fun x=>P (f x)) a
  (hom_comp r (Dg a)) (hom_comp P (D a))
  (norm_differential_domain_agreement hNX hprefix hrd) hpd.
have hPoint w:r (Dg a w)= P (D a w):= congr1 (fun H:Hom X V=>H w) hEq.
have hker w:P (D a w)=0 -> D a w=0.
  move=>hz.
  have [u hu]:=(@range_projection_image R X Y (@euclidean_inner_product R n) (D a) v p j
    (constant_rank_projection hC) (D a w)).2 (ex_intro _ w erefl).
  have hpu:=congr1 p hu.
  have hz0:p (D a w)=0:=hz.
  rewrite (range_projection_cancel (constant_rank_projection hC)) hz0 in hpu.
  rewrite hpu linear0 in hu; exact: esym hu.
have hk w:D a w=0 <-> r (Dg a w)=0.
  split.
  - move=>hz; by rewrite hPoint hz linear0.
  - move=>hz; apply: hker; by rewrite -hPoint.
have hImage:g @` (S `&` U)= T `&` C.
  apply/seteqP; split=>y.
  - move=>[x [[hxA hxf] hxU] <-]; split; last exact: hmap x hxU.
    change (r (g x)= r (g a)).
    by rewrite (hprefix x hxU) (hprefix a haU) hxf.
  - move=>[hyT hyC].
    pose x:= G y.
    have hxU:U x:= himap y hyC.
    have hgy:g x= y:= hfg y hyC.
    have hPf:P (f x)= P (f a).
      by rewrite -(hprefix x hxU) -(hprefix a haU) hgy.
    have hPf0:p (f x)=p (f a):=hPf.
    have hfx:f x=f a.
      exact (eq_trans (constant_rank_section_factor hC hxU)
        (eq_trans (congr1 psi hPf0) (esym (constant_rank_section_factor hC haU)))).
    exists x; last exact hgy.
    split; last exact hxU.
    exact (conj (hUA x hxU) hfx).
have htan:=@norm_diffeomorphism_tangent_image R X X NX NX hNX hNX U S C g G 1 a (Dg a)
  (leqnn 1) hSource haU hDga.
rewrite hImage (@norm_tangent_open_restriction R X NX T C (g a) hintC)
  (@norm_tangent_linear_fibre R X V NX NV hNX hNV r (g a) hr) in htan.
have hleft:=@norm_differentials_left_inverse R X X NX NX hNX hNX U C g G a (Dg a) (DG (g a))
  hmap hgf hDga hDGa.
have hcan:cancel (Dg a) (DG (g a)).
  move=>w; exact (congr1 (fun H:Hom X X=>H w) hleft).
have hi:injective (Dg a):= can_inj hcan.
apply/seteqP; split=>w.
- move=>hw; apply: (hk w).2.
  have hh:(Dg a @` norm_tangent_cone NX S a) (Dg a w) by exists w.
  rewrite htan in hh; exact hh.
- move=>hw.
  have hh:(Dg a @` norm_tangent_cone NX S a) (Dg a w) by rewrite htan; exact: (hk w).1 hw.
  have [u hu heq]:= hh.
  have huw:u= w:= hi _ _ heq.
  by rewrite -huw.
Qed.
