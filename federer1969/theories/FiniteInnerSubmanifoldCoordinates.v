(** Federer (1969), 3.1.19(4), p. 231, in the
    actual finite inner-product ambient spaces of 3.2.28,
    pp. 263–267. Supporting the actual isotropy coordinates
    used for the product parametrizations in 3.2.47, p. 283.
    Ambient orthonormal charts are local existence witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerConvex HilbertFormCompactness FiniteInnerChartUP FiniteInnerSubmanifoldUP
  NormDifferentialUP NormRegularity NormRegularityLinearMaps
  NormCoordinateSystemUP SubmanifoldStraighteningCoordinates SubmanifoldChartsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_submanifold_coordinates]: actual
    local parameter coordinates on a submanifold, by
    3.1.19(4), p. 231, supporting I in 3.2.47,
    p. 283. Exact original-set image and both inverse
    laws follow from the public ambient isometry laws. *)
Theorem finite_inner_submanifold_coordinates (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B) mu k (S:set V) (a:V):
  is_inner_submanifold B mu k S ->S a ->
  exists T U phi psi,
    norm_domain_interior (inner_norm hB) T a /\is_inner_convex U /\
    is_norm_coordinate_system (inner_norm_real_norm hB)
      (inner_norm_real_norm (@euclidean_inner_productP R mu)) S T U phi psi k.
Proof.
move=>[N [e [p [hChart hMan]]]] ha.
pose hV:=inner_norm_real_norm hB.
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R N).
pose hMu:=inner_norm_real_norm (@euclidean_inner_productP R mu).
have hPoint:(p @` S) (p a) by exists a.
have [T [U [phi [psi [hBase [hConv [hPhi [hPsi [hForward [_ [hImage hCancel]]]]]]]]]]]:=
  @submanifold_convex_coordinates R N mu k (p @` S) hMan (p a) hPoint.
have hP:norm_bounded_linear (inner_norm hB) (inner_norm (@euclidean_inner_productP R N)) p.
  exists 1; split; first exact:ler01.
  by move=>v; rewrite (finite_inner_chart_inverse_norm hB hChart) mul1r.
have hE:norm_bounded_linear (inner_norm (@euclidean_inner_productP R N)) (inner_norm hB) e.
  exists 1; split; first exact:ler01.
  by move=>v; rewrite (finite_inner_chart_norm hB hChart) mul1r.
pose A:=fun x:V=>T (p x).
pose Phi:=fun x:V=>phi (p x).
pose Psi:=fun u:R_n R mu=>e (psi u).
have hPhiClass:=@norm_class_precompose_linear R V (R_n R N) (R_n R mu)
  _ _ _ hV hN hMu T phi p k hP hPhi.
have hPsiClass:=@norm_class_postcompose_linear R (R_n R mu) (R_n R N) V
  _ _ _ hMu hN hV U psi e k hE hPsi.
exists A,U,Phi,Psi; split.
- have [r [hr hBall]]:=hBase; exists r; split; first exact hr.
  move=>v hv.
  have hSmall:inner_norm (@euclidean_inner_productP R N) (p v)<r.
    by rewrite (finite_inner_chart_inverse_norm hB hChart).
  have hResult:=hBall (p v) hSmall.
  change (T (p (a+v))); by rewrite linearD.
- split; first exact hConv.
  constructor.
  + exact hPhiClass.
  + exact hPsiClass.
  + move=>x hx; exact:hForward (p x) hx.
  + apply/seteqP; split=>x.
    * move=>[u hu <-].
      have hPsiImage:(psi @` U) (psi u) by exists u.
      rewrite hImage in hPsiImage.
      have [y hy hpy]:=hPsiImage.1.
      split.
      -- change (S (e (psi u))).
         by rewrite -hpy (finite_inner_chart_right_inverse hChart).
      -- change (T (p (e (psi u)))).
         rewrite (finite_inner_chart_left_inverse hChart); exact hPsiImage.2.
    * move=>[hx hxT].
      have hCoordinate:(psi @` U) (p x).
        rewrite hImage; split; last exact hxT.
        by exists x.
      have [u hu hValue]:=hCoordinate.
      exists u; first exact hu.
      change (e (psi u)=x).
      by rewrite hValue (finite_inner_chart_right_inverse hChart).
  + move=>u hu; change (phi (p (e (psi u)))=u).
    by rewrite (finite_inner_chart_left_inverse hChart) hCancel.
Qed.
