(** Federer (1969), 3.1.24, p. 240, referring to 3.1.19, p. 231: put the plane in a
    straightening chart into standard block coordinates. The finite
    basis change is auxiliary; the submanifold definition stays abstract. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialUP NormRegularity
  NormFiniteLinearBound NormDiffeomorphismUP NormDiffeomorphismComposition
  NormDiffeomorphismSourceRestriction NormOpenDomainLaws EuclideanBlockLinearMaps
  GrassmannSubspaces SubspaceBlockChartUP SubspaceBlockChart EuclideanSubmanifoldUP AnalyticSubmanifoldUP NormAnalyticUP NormAnalyticLinear NormAnalyticOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_submanifold_standard_block_chart]: 3.1.24, p. 240; the elementary
    adapted-plane reduction behind (1) implies (2) and (4), Federer
    3.1.19, p. 231. The given mu-plane becomes the kernel of the
    last l coordinates of a class-one diffeomorphism. *)
Theorem analytic_submanifold_standard_block_chart (R:realType) mu l
    (B:set (R_n R (mu+l))) b : @is_euclidean_analytic_submanifold R (mu+l) mu B -> B b ->
  exists (T C:set (R_n R (mu+l))) (s t:R_n R (mu+l)->R_n R (mu+l)),
    norm_domain_interior (inner_norm (@euclidean_inner_productP R (mu+l))) T b /\
    is_norm_diffeomorphism (inner_norm_real_norm (@euclidean_inner_productP R (mu+l)))
      (inner_norm_real_norm (@euclidean_inner_productP R (mu+l))) T C s t 1%N /\
    @norm_analytic R (R_n R (mu+l)) (R_n R (mu+l))
      (inner_norm (@euclidean_inner_productP R (mu+l))) (inner_norm (@euclidean_inner_productP R (mu+l)))
      (inner_norm_real_norm (@euclidean_inner_productP R (mu+l))) (inner_norm_real_norm (@euclidean_inner_productP R (mu+l))) T s /\
    @norm_analytic R (R_n R (mu+l)) (R_n R (mu+l))
      (inner_norm (@euclidean_inner_productP R (mu+l))) (inner_norm (@euclidean_inner_productP R (mu+l)))
      (inner_norm_real_norm (@euclidean_inner_productP R (mu+l))) (inner_norm_real_norm (@euclidean_inner_productP R (mu+l))) C t /\
    forall x, T x -> (B x <-> @euclidean_last_block_map R mu l (s x)=0).
Proof.
move=>hB hb.
have [T [C [s [t [Z [[hTb hD him] [hsA htA]]]]]]]:=hB b hb.
have [beta [gamma hZ]]:=subspace_block_chart_exists Z.
pose X:=R_n R (mu+l).
pose NX:=inner_norm (@euclidean_inner_productP R (mu+l)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (mu+l)).
have hbeta:=@norm_finite_linear_bounded R X X NX NX hNX hNX (mu+l)
  (@coordinate_basis R (mu+l)) (@coordinate_basisP R (mu+l)) beta.
have hgamma:=@norm_finite_linear_bounded R X X NX NX hNX hNX (mu+l)
  (@coordinate_basis R (mu+l)) (@coordinate_basisP R (mu+l)) gamma.
have hlin:=@norm_linear_diffeomorphism R X X NX NX hNX hNX beta gamma 1%N
  hbeta hgamma (subspace_chart_forward_inverse hZ) (subspace_chart_backward_inverse hZ).
have hCopen x (hx:C x):norm_domain_interior NX C x.
  have hc:=norm_class_continuous (norm_diffeomorphism_inverse_class hD).
  exact (@hc x hx).1.
have hlinC:=@norm_diffeomorphism_source_restriction R X X NX NX hNX hNX
  (fun _=>True) C (fun _=>True) beta gamma 1%N hlin (fun _ _=>I) hCopen.
have hcomp:=@norm_diffeomorphism_composition R X X X NX NX NX hNX hNX hNX
  T C (fun y=>True /\ C (gamma y)) s t beta gamma 1%N hD hlinC.
pose E:=fun y:X=>True /\ C (gamma y).
have hbA:=@norm_bounded_linear_analytic R X X NX NX hNX hNX (fun _=>True)
  (fun x _=>@norm_full_domain_interior R X NX x) beta hbeta.
have hsbA:=@norm_analytic_compose_on R X X X NX NX NX hNX hNX hNX T (fun _=>True)
  s beta (fun _ _=>Logic.I) hsA hbA.
have hEopen x (hx:E x):norm_domain_interior NX E x.
  have hc:=norm_class_continuous (norm_diffeomorphism_inverse_class hcomp).
  exact (@hc x hx).1.
have hgammaA:=@norm_bounded_linear_analytic R X X NX NX hNX hNX E hEopen gamma hgamma.
have htgA:=@norm_analytic_compose_on R X X X NX NX NX hNX hNX hNX E C gamma t
  (fun x hx=>hx.2) hgammaA htA.
exists T,E,(fun x=>beta (s x)),(fun y=>t (gamma y)).
split; first exact hTb.
split; first exact hcomp.
split; first exact hsbA.
split; first exact htgA.
move=>x hx.
rewrite -(subspace_chart_plane hZ (s x)).
split.
- move=>hBx; have hi:(s @` (B `&` T)) (s x) by exists x; split.
  rewrite him in hi; exact hi.1.
- move=>hsZ.
  have hsC:=@norm_diffeomorphism_maps R X X NX NX hNX hNX T C s t 1%N hD x hx.
  have hi:(s @` (B `&` T)) (s x) by rewrite him; split.
  have [y [hBy hTy] hyx]:=hi.
  have ht:=congr1 t hyx.
  rewrite (@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX T C s t 1%N hD y hTy)
    (@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX T C s t 1%N hD x hx) in ht.
  by rewrite -ht.
Qed.
