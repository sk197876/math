(** Federer (1969), 3.1.19(4) implies (1), p. 231,
    in actual finite inner-product ambient spaces. Supporting
    identification of the original Phi preimage in 3.2.47,
    p. 283, from its proved local product coordinates.
    The criterion contains genuine chart existence obligations. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerConvex HilbertFormCompactness FiniteInnerChartUP
  FiniteInnerSubmanifoldUP NormDifferentialUP NormRegularity NormRegularityLinearMaps
  NormCoordinateSystemUP EuclideanSubmanifoldUP SubmanifoldChartsUP
  SubmanifoldCoordinateParametrisation SubmanifoldParametrisationStraightening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_coordinates_euclidean_submanifold]: actual
    convex local coordinates imply the original submanifold
    predicate, by 3.1.19, p. 231, supporting the
    preimage geometry of 3.2.47, p. 283. Both
    derivative injectivity and straightening follow from the
    proved coordinate criterion, with no additional rank premise. *)
Theorem finite_inner_coordinates_euclidean_submanifold (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B) N (e:Hom (R_n R N) V) (p:Hom V (R_n R N))
    mu k (S:set V):
  (1<=k)%N ->is_finite_inner_chart B e p ->
  (forall a,S a ->exists T U phi psi,
    norm_domain_interior (inner_norm hB) T a /\is_inner_convex U /\
    is_norm_coordinate_system (inner_norm_real_norm hB)
      (inner_norm_real_norm (@euclidean_inner_productP R mu)) S T U phi psi k) ->
  @is_euclidean_submanifold R N mu k (p @` S).
Proof.
move=>hk hChart hCoordinates.
pose hV:=inner_norm_real_norm hB.
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R N).
pose hMu:=inner_norm_real_norm (@euclidean_inner_productP R mu).
have hP:norm_bounded_linear (inner_norm hB) (inner_norm (@euclidean_inner_productP R N)) p.
  exists 1; split; first exact:ler01.
  by move=>v; rewrite (finite_inner_chart_inverse_norm hB hChart) mul1r.
have hE:norm_bounded_linear (inner_norm (@euclidean_inner_productP R N)) (inner_norm hB) e.
  exists 1; split; first exact:ler01.
  by move=>v; rewrite (finite_inner_chart_norm hB hChart) mul1r.
have hConvex:@has_convex_coordinate_charts R N mu k (p @` S).
  move=>z [a ha <-].
  have [T [U [phi [psi [hTa [hU hC]]]]]]:=hCoordinates a ha.
  pose A:=fun x:R_n R N=>T (e x).
  pose Phi:=fun x:R_n R N=>phi (e x).
  pose Psi:=fun u:R_n R mu=>p (psi u).
  exists A,U,Phi,Psi; split.
  - have [r [hr hBall]]:=hTa; exists r; split; first exact hr.
    move=>v hv.
    have hSmall:inner_norm hB (e v)<r.
      by rewrite (finite_inner_chart_norm hB hChart).
    have hResult:=hBall (e v) hSmall.
    change (T (e (p a+v))).
    rewrite linearD.
    change (T (e (p a)+e v)).
    rewrite (finite_inner_chart_right_inverse hChart); exact hResult.
  - split; first exact hU.
    split.
    + exact (@norm_class_precompose_linear R (R_n R N) V (R_n R mu) _ _ _ hN hV hMu
        T phi e k hE (norm_coordinate_class_forward hC)).
    + split.
      * exact (@norm_class_postcompose_linear R (R_n R mu) V (R_n R N) _ _ _ hMu hV hN
          U psi p k hP (norm_coordinate_class_backward hC)).
      * split.
        -- move=>x hx; exact:(norm_coordinate_forward_range hC hx).
        -- split.
           ++ move=>u hu; change (T (e (p (psi u)))).
              rewrite (finite_inner_chart_right_inverse hChart).
              exact:(norm_coordinate_backward_membership hC hu).2.
           ++ split.
              ** apply/seteqP; split=>x.
                 --- move=>[u hu <-].
                     have hValue:=norm_coordinate_backward_membership hC hu.
                     split; first by exists (psi u); first exact hValue.1.
                     change (T (e (p (psi u)))).
                     rewrite (finite_inner_chart_right_inverse hChart); exact hValue.2.
                 --- move=>[[y hy hpy] hxA].
                     have hyT:T y.
                       change (T (e x)) in hxA.
                       by rewrite -hpy (finite_inner_chart_right_inverse hChart) in hxA.
                     have hImage:(psi @` U) y by rewrite (norm_coordinate_image hC); split.
                     have [u hu hValue]:=hImage; exists u; first exact hu.
                     change (p (psi u)=x); by rewrite hValue hpy.
              ** move=>u hu; change (phi (e (p (psi u)))=u).
                 by rewrite (finite_inner_chart_right_inverse hChart) (norm_coordinate_cancel hC).
exact:(open_parametrisations_submanifold hk (convex_coordinates_open_parametrisations hk hConvex)).
Qed.

(** Source for [finite_inner_coordinates_submanifold]: the
    same proved convex coordinate criterion in the original
    finite inner ambient space, 3.1.19, p. 231,
    supporting 3.2.47, p. 283. *)
Theorem finite_inner_coordinates_submanifold (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B) N (e:Hom (R_n R N) V) (p:Hom V (R_n R N))
    mu k (S:set V):
  (1<=k)%N ->is_finite_inner_chart B e p ->
  (forall a,S a ->exists T U phi psi,
    norm_domain_interior (inner_norm hB) T a /\is_inner_convex U /\
    is_norm_coordinate_system (inner_norm_real_norm hB)
      (inner_norm_real_norm (@euclidean_inner_productP R mu)) S T U phi psi k) ->
  is_inner_submanifold B mu k S.
Proof.
move=>hk hChart hC; exists N,e,p; split; first exact hChart.
exact (@finite_inner_coordinates_euclidean_submanifold R V B hB N e p mu k S hk hChart hC).
Qed.
