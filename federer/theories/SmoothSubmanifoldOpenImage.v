(** Federer (1969), 3.2.28(2),(4), pp. 264,267:
    an open constant-rank map on a smooth submanifold
    has a smooth submanifold image, by 3.1.19(3), p. 231.
    The derivatives and tangent ranges below are actual ones. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness InnerConvex
  NormMetric NormDifferentialUP NormClassOneUP NormClassOneComposition NormClassOneRestriction
  NormRegularity NormRegularityOperations NormOpenPreimage NormCoordinateSystemUP
  NormCoordinateTangent LinearRankUP TangentConeUP EuclideanSubmanifoldUP
  FiniteInnerSmoothSubmanifoldUP SmoothSubmanifoldCoordinates
  SmoothSubmanifoldParametrisationsUP SmoothParametrisationStraightening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_submanifold_open_constant_rank_image]:
    the image submanifolds in Federer 3.2.28(2),(4),
    pp. 264,267, using 3.1.19(3), p. 231.
    Relative openness is required for every open source piece.
    One inverse-coordinate map gives the tangent range, and
    the smooth rank theorem supplies charts fixed at all orders. *)
Theorem smooth_submanifold_open_constant_rank_image (R:realType) n p mu r
    (B:set (R_n R n)) (f:R_n R n->R_n R p)
    (D:R_n R n->Hom (R_n R n) (R_n R p)):
  @is_euclidean_smooth_submanifold R n mu B ->
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R p)) (fun _=>True) f ->
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R p)) (fun _=>True) f D ->
  (forall a,B a ->forall J:Hom (R_n R mu) (R_n R n),
    norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) B a=range J ->
    has_linear_rank (hom_comp (D a) J) r) ->
  (forall W,@relatively_open_set [the topologicalType of real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))] B W ->
    @relatively_open_set [the topologicalType of real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R p))] (f @` B) (f @` W)) ->
  @is_euclidean_smooth_submanifold R p r (f @` B).
Proof.
move=>hB hf hD hRank hOpen.
pose X:=R_n R n; pose Y:=R_n R p; pose Z:=R_n R mu.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R p).
pose NZ:=inner_norm (@euclidean_inner_productP R mu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R p).
pose hNZ:=inner_norm_real_norm (@euclidean_inner_productP R mu).
apply:smooth_open_parametrisations_submanifold=>b [a ha hab].
have [T [V [phi [psi [hTa [hConv [hPhi [hPsi [hPV [hPT [him hcan]]]]]]]]]]]:=
  smooth_submanifold_convex_coordinates hB ha.
have hc k:is_norm_coordinate_system hNX hNZ B T V phi psi k by constructor; [exact:hPhi|exact:hPsi|exact:hPV|exact:him|exact:hcan].
have [J hJ]:=(norm_class_firstP hNZ hNX V psi).1 (hPsi 1%N).
have [E hE]:=(norm_class_firstP hNX hNZ T phi).1 (hPhi 1%N).
pose F:=fun u:Z=>f (psi u).
pose L:=fun u:Z=>hom_comp (D (psi u)) (J u).
have hPsiB u (hu:V u):B (psi u).
  have hi:(psi @` V) (psi u) by exists u.
  rewrite him in hi; exact:hi.1.
have hF k:norm_class hNZ hNY V F k.
  exact:(@norm_class_compose_on R Z X Y NZ NX NY hNZ hNX hNY
    V (fun _=>True) psi f k (fun _ _=>I) (hPsi k) (hf k)).
have hL:is_norm_class_one_field NZ NY V F L.
  apply:(@norm_class_one_field_open_restriction R Z Y NZ NY
    (fun u=>V u /\True) V F L (fun u hu=>conj hu I)).
  - move=>u hu; exact:(@norm_class_one_zero R Z X NZ NX V psi J hJ u hu).1.
  - exact:(norm_class_one_composite_field hNZ hNX hNY hJ hD).
have hR u (hu:V u):has_linear_rank (L u) r.
  apply:(hRank (psi u) (hPsiB u hu) (J u)).
  have ht:=hPT u hu.
  have hBase:=norm_coordinate_base_inverse (hc 1%N) (hPsiB u hu) ht.
  have hDphi:=norm_class_one_differential hE ht.
  have hDpsi:=norm_class_one_differential hJ hu.
  have hAt:has_norm_differential NZ NX V psi (phi (psi u)) (J u).
    by rewrite hcan.
  exact:(norm_coordinate_tangent_inverse (hc 1%N) (hPsiB u hu) ht hDphi hAt).2.2.
have hIn:V (phi a).
  exact:hPV (norm_domain_interior_member hNX hTa).
have hrmu:(r<=mu)%N.
  exact:(linear_rank_domain_bound (@coordinate_basisP R mu) (hR _ hIn)).
exists mu,V,F,L; split; first exact hrmu.
split; first exact hF.
split; first exact hL.
split.
- move=>u hu; exists (psi u); first exact:hPsiB u hu.
  reflexivity.
split.
- exists (phi a); first exact hIn.
  rewrite /F (norm_coordinate_base_inverse (hc 1%N) ha
    (norm_domain_interior_member hNX hTa)); exact hab.
split; first exact hR.
move=>W hWV hW.
have hRelative:@relatively_open_set [the topologicalType of real_norm_metric_space hNX]
    B (psi @` W).
  exists [set x|T x /\W (phi x)]; split.
  - exact:(@norm_class_zero_open_preimage R X Z NX NZ hNX hNZ T W phi
      (norm_class_continuous (hPhi 0%N)) hW).
  - apply/seteqP; split=>x.
    + move=>[u hu <-]; split; first exact:hPsiB (hWV u hu).
      split; first exact:hPT (hWV u hu).
      by rewrite hcan //; exact:hWV.
    + move=>[hBx [hTx hWx]].
      have hi:(psi @` V) x by rewrite him; split.
      have [u hu hux]:=hi; exists u; last exact hux.
      by rewrite -hux hcan in hWx.
have hRel:=hOpen _ hRelative.
have hImg:F @` W=f @` (psi @` W).
  apply/seteqP; split=>y.
  - move=>[u hu <-]; exists (psi u); last reflexivity.
    by exists u.
  - move=>[x [u hu <-] <-]; by exists u.
by rewrite hImg.
Qed.
