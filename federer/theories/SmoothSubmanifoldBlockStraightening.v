(** Federer (1969), 3.1.19, p. 231: put the plane in a
    straightening chart into standard block coordinates. The finite
    basis change is auxiliary; the submanifold definition stays abstract. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialUP NormRegularity
  NormFiniteLinearBound NormDiffeomorphismUP NormDiffeomorphismComposition
  NormDiffeomorphismSourceRestriction NormOpenDomainLaws EuclideanBlockLinearMaps
  GrassmannSubspaces SubspaceBlockChartUP SubspaceBlockChart EuclideanSubmanifoldUP
 FiniteInnerSmoothSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_submanifold_standard_block_chart]: the elementary
    adapted-plane reduction behind (1) implies (2) and (4), Federer
    3.1.19, p. 231. The given mu-plane becomes the kernel of the
    last l coordinates of one diffeomorphism of every finite class.
    Supporting the smooth manifolds in Federer 3.2.28,
    pp. 263–267, the block basis is chosen only once. *)
Theorem smooth_submanifold_standard_block_chart (R:realType) mu l
    (B:set (R_n R (mu+l))) b : @is_euclidean_smooth_submanifold R (mu+l) mu B -> B b ->
  exists (T C:set (R_n R (mu+l))) (s t:R_n R (mu+l)->R_n R (mu+l)),
    norm_domain_interior (inner_norm (@euclidean_inner_productP R (mu+l))) T b /\
    (forall k,is_norm_diffeomorphism (inner_norm_real_norm (@euclidean_inner_productP R (mu+l)))
      (inner_norm_real_norm (@euclidean_inner_productP R (mu+l))) T C s t k) /\
    forall x, T x -> (B x <-> @euclidean_last_block_map R mu l (s x)=0).
Proof.
move=>hB hb.
have [T [C [s [t [Z hChart]]]]]:=hB b hb.
have hTb:=submanifold_straightening_neighbourhood (hChart 0%N).
have hD k:=submanifold_straightening_diffeomorphism (hChart k).
have him:=submanifold_straightening_image (hChart 0%N).
have [beta [gamma hZ]]:=subspace_block_chart_exists Z.
pose X:=R_n R (mu+l).
pose NX:=inner_norm (@euclidean_inner_productP R (mu+l)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (mu+l)).
have hbeta:=@norm_finite_linear_bounded R X X NX NX hNX hNX (mu+l)
  (@coordinate_basis R (mu+l)) (@coordinate_basisP R (mu+l)) beta.
have hgamma:=@norm_finite_linear_bounded R X X NX NX hNX hNX (mu+l)
  (@coordinate_basis R (mu+l)) (@coordinate_basisP R (mu+l)) gamma.
have hlin k:=@norm_linear_diffeomorphism R X X NX NX hNX hNX beta gamma k
  hbeta hgamma (subspace_chart_forward_inverse hZ) (subspace_chart_backward_inverse hZ).
have hCopen x (hx:C x):norm_domain_interior NX C x.
  have hc:=norm_class_continuous (norm_diffeomorphism_inverse_class (hD 0%N)).
  exact (@hc x hx).1.
have hlinC k:=@norm_diffeomorphism_source_restriction R X X NX NX hNX hNX
  (fun _=>True) C (fun _=>True) beta gamma k (hlin k) (fun _ _=>I) hCopen.
have hcomp k:=@norm_diffeomorphism_composition R X X X NX NX NX hNX hNX hNX
  T C (fun y=>True /\ C (gamma y)) s t beta gamma k (hD k) (hlinC k).
exists T,(fun y=>True /\ C (gamma y)),(fun x=>beta (s x)),(fun y=>t (gamma y)).
split; first exact hTb.
split; first exact hcomp.
move=>x hx.
rewrite -(subspace_chart_plane hZ (s x)).
split.
- move=>hBx; have hi:(s @` (B `&` T)) (s x) by exists x; split.
  rewrite him in hi; exact hi.1.
- move=>hsZ.
  have hsC:=@norm_diffeomorphism_maps R X X NX NX hNX hNX T C s t 0%N (hD 0%N) x hx.
  have hi:(s @` (B `&` T)) (s x) by rewrite him; split.
  have [y [hBy hTy] hyx]:=hi.
  have ht:=congr1 t hyx.
  rewrite (@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX T C s t 0%N (hD 0%N) y hTy)
    (@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX T C s t 0%N (hD 0%N) x hx) in ht.
  by rewrite -ht.
Qed.
