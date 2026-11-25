(** Federer (1969), 3.4.3, p. 317: the original
    joint coordinate change g(x)=(L f(x),q(x)). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Bilinear Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness RealNormUP InnerConvex
  NormDifferentialUP NormDifferentialLinear NormDifferentialArithmetic NormDifferentialFiniteCalculus NormDifferentialDirectional
  NormClassOneUP NormRegularity NormRegularityOperations NormRegularityLinearMaps
  NormFiniteLinearBound NormOpenDomainLaws NormClassZeroTopology NormLinearDomainLaws
  EuclideanBlockLinearMaps EuclideanBlockCoordinates NormCartesianRegularity
  NormDiffeomorphismUP NormDiffeomorphismRestriction FiniteLocalDiffeomorphism
  LinearRankUP CriticalTargetCoordinatesUP CriticalTargetCoordinateLaws
  CriticalKernelProjectionUP CriticalKernelProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_local_source_chart]: the joint map,
    nonsingular differential, local inverse, and convex image S
    in 3.4.3, p. 317. The actual orthogonal kernel
    projection is constructed from its independent laws. Restricting
    the inverse image to an open image ball gives the printed
    convexity without assuming a chart or inverse. *)
Theorem critical_local_source_chart (R:realType) nu l k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (A:set (R_n R (nu+l))) (f:R_n R (nu+l)->Y) a
    (D:Hom (R_n R (nu+l)) Y)
    (L:Hom Y (R_n R nu)) (J:Hom (R_n R nu) Y):
  (1<=k)%N ->norm_class (inner_norm_real_norm (@euclidean_inner_productP R (nu+l))) hNY A f k ->
  A a ->has_norm_differential (inner_norm (@euclidean_inner_productP R (nu+l))) NY A f a D ->
  is_critical_target_coordinates NY D L J ->
  exists (U S:set (R_n R (nu+l))) (g G:R_n R (nu+l)->R_n R (nu+l)),
    U a /\U `<=` A /\is_inner_convex S /\
    is_norm_diffeomorphism
      (inner_norm_real_norm (@euclidean_inner_productP R (nu+l)))
      (inner_norm_real_norm (@euclidean_inner_productP R (nu+l))) U S g G k /\
    forall x,euclidean_first_block (g x)=L (f x).
Proof.
move=>hk hf ha hD hCoordinates.
pose X:=R_n R (nu+l);pose V:=R_n R nu;pose W:=R_n R l.
pose NX:=inner_norm (@euclidean_inner_productP R (nu+l)).
pose NV:=inner_norm (@euclidean_inner_productP R nu).
pose NW:=inner_norm (@euclidean_inner_productP R l).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (nu+l)).
pose hNV:=inner_norm_real_norm (@euclidean_inner_productP R nu).
pose hNW:=inner_norm_real_norm (@euclidean_inner_productP R l).
pose alpha:=hom_comp L D.
have hSurj:forall u,exists x,alpha x=u:=critical_target_coordinate_epimorphism hCoordinates.
have [q [j hQ]]:=critical_kernel_projection_exists hSurj.
pose Q:=hom_of_linear q.
pose I:=@euclidean_first_injection_map R nu l.
pose H:=@euclidean_last_injection_map R nu l.
pose g:=fun x=>I (L (f x))+H (Q x).
pose T:=hom_comp I alpha+hom_comp H Q.
have hOpen x (hx:A x):norm_domain_interior NX A x:=(norm_class_continuous hf hx).1.
have hL:norm_bounded_linear NY NV L:=critical_target_coordinates_bounded hCoordinates.
have hI:=@norm_finite_linear_bounded R V X NV NX hNV hNX nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) I.
have hH:=@norm_finite_linear_bounded R W X NW NX hNW hNX l
  (@coordinate_basis R l) (@coordinate_basisP R l) H.
have hQBound:=@norm_finite_linear_bounded R X W NX NW hNX hNW (nu+l)
  (@coordinate_basis R (nu+l)) (@coordinate_basisP R (nu+l)) Q.
have hLf:=@norm_class_postcompose_linear R X Y V NX NY NV hNX hNY hNV A f L k hL hf.
have hFirst:=@norm_class_postcompose_linear R X V X NX NV NX hNX hNV hNX A
  (fun x=>L (f x)) I k hI hLf.
have hLast:=@norm_class_linear R X X NX NX hNX hNX A (hom_comp H Q) k hOpen
  (norm_bounded_linear_compose hQBound hH).
have hG:norm_class hNX hNX A g k:=norm_class_add hFirst hLast.
have hDLeft:=norm_differential_postcompose hNX hD hL.
have hDHead:=norm_differential_postcompose hNX hDLeft hI.
have hDTail:=@norm_differential_linear R X X NX NX hNX hNX A a (hom_comp H Q)
  (hOpen a ha) (norm_bounded_linear_compose hQBound hH).
have hActual:has_norm_differential NX NX A g a T:=norm_differential_add hNX hDHead hDTail.
have hKernel x (hZero:T x=0):x=0.
  pose P:=@euclidean_first_block_map R nu l.
  pose Q0:=@euclidean_last_block_map R nu l.
  have hHead:=congr1 P hZero.
  change (P (I (alpha x)+H (Q x))= P (0:X)) in hHead.
  rewrite linearD linear0 /= euclidean_first_block_injectionK
    euclidean_first_block_last_injection addr0 in hHead.
  have hTail:=congr1 Q0 hZero.
  change (Q0 (I (alpha x)+H (Q x))=Q0 (0:X)) in hTail.
  rewrite linearD linear0 /= euclidean_last_block_first_injection
    euclidean_last_block_injectionK add0r in hTail.
  exact:(critical_kernel_projection_kernel_intersection hQ hHead hTail).
have hInjective:injective T.
  move=>x y hEqual.
  have hZero:T (x-y)=0 by rewrite (Bilinear.linB (hom_linear T)) hEqual subrr.
  have hDifference:=hKernel (x-y) hZero.
  by apply/eqP;rewrite -subr_eq0 hDifference.
have [DG hDG]:=(norm_class_firstP hNX hNX A g).1 (norm_class_lower hk hG).
have hSame:DG a=T:=norm_differential_unique hNX hNX
  (norm_class_one_differential hDG ha) hActual.
have hInj:injective (DG a) by rewrite hSame.
have [r [hr [hInside [G hLocal]]]]:=@finite_local_diffeomorphism R X
  (@euclidean_inner_product R (nu+l)) (@euclidean_inner_productP R (nu+l)) hNX
  (nu+l) (@coordinate_basis R (nu+l)) (@coordinate_basisP R (nu+l)) A g DG a k hG hDG ha hInj.
pose O:=fun x=>NX (x-a)<r.
pose V0:=g @` O.
have haO:O a by rewrite /O subrr /NX inner_norm0.
have hga:V0 (g a):=norm_diffeomorphism_maps hLocal haO.
have hInterior:norm_domain_interior NX V0 (g a):=
  (norm_class_continuous (norm_diffeomorphism_inverse_class hLocal) hga).1.
have [e [he hBall]]:=hInterior.
pose S:=fun y=>NX (y-g a)<e.
have hSV:S `<=` V0.
  move=>y hy;have hh:=hBall (y-g a) hy;by rewrite addrC subrK in hh.
have hLocalRestricted:=norm_diffeomorphism_target_restriction hLocal hSV
  (fun y hy=>@norm_open_ball_domain_interior R X NX hNX (g a) e y hy).
exists (fun x=>O x /\S (g x)),S,g,G;split.
- split;first exact:haO.
  by rewrite /S subrr /NX inner_norm0.
split;first by move=>x hx;exact:hInside x hx.1.
split;first exact:(@norm_open_ball_convex R X NX hNX (g a) e).
split;first exact:hLocalRestricted.
move=>x.
change (@euclidean_first_block_map R nu l (I (L (f x))+H (Q x))=L (f x)).
rewrite linearD /= euclidean_first_block_injectionK
  euclidean_first_block_last_injection addr0;reflexivity.
Qed.
