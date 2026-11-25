(** Federer (1969), 3.2.48, p. 285: products of the actual local
    manifold coordinates are manifold coordinates. Supporting use of
    3.1.19(4), p. 231, in the original Cartesian inner metrics.
    All local inverse and regularity laws are proved. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP InnerProductUP InnerNorm HilbertFormCompactness
  ProductInner ProductInnerNormBounds RealNormUP NormDifferentialUP NormLinearDomainLaws
  NormRegularity NormRegularityOperations NormRegularityLinearMaps ProductInnerPairRegularity
  NormCoordinateSystemUP InnerConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_class_cartesian_blocks]: the class of the
    independent product coordinate maps, supporting the actual source
    manifold in 3.2.48, p. 285, by 3.1.11, pp. 218–221. *)
Theorem norm_class_cartesian_blocks (R:realType) (V W U Z:lmodType R)
    BV BW BU BZ (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    (hU:@is_inner_product R U BU) (hZ:@is_inner_product R Z BZ)
    (A:set V) (B:set W) (f:V->U) (g:W->Z) k:
  norm_class (inner_norm_real_norm hV) (inner_norm_real_norm hU) A f k ->
  norm_class (inner_norm_real_norm hW) (inner_norm_real_norm hZ) B g k ->
  norm_class (inner_norm_real_norm (product_inner_productP hV hW))
    (inner_norm_real_norm (product_inner_productP hU hZ))
    [set z:V*W|A z.1 /\B z.2] (fun z=>(f z.1,g z.2)) k.
Proof.
move=>hf hg.
pose P:lmodType R:=[the lmodType R of (V*W)%type].
pose hP:=product_inner_productP hV hW.
pose p:=@product_first_projection_hom R V W.
pose q:=@product_second_projection_hom R V W.
have hp:norm_bounded_linear (inner_norm hP) (inner_norm hV) p.
  exists 1; split; first exact:ler01.
  by move=>z; rewrite mul1r; exact (product_inner_first_norm_bound hV hW z).
have hq:norm_bounded_linear (inner_norm hP) (inner_norm hW) q.
  exists 1; split; first exact:ler01.
  by move=>z; rewrite mul1r; exact (product_inner_second_norm_bound hV hW z).
have hF:=@norm_class_precompose_linear R P V U _ _ _
  (inner_norm_real_norm hP) (inner_norm_real_norm hV) (inner_norm_real_norm hU) A f p k hp hf.
have hG:=@norm_class_precompose_linear R P W Z _ _ _
  (inner_norm_real_norm hP) (inner_norm_real_norm hW) (inner_norm_real_norm hZ) B g q k hq hg.
pose C:=fun z:P=>A z.1 /\B z.2.
have hOpen z (hz:C z):norm_domain_interior (inner_norm hP) C z.
  apply:norm_domain_intersection_interior.
  - exact ((norm_class_continuous hF hz.1).1).
  - exact ((norm_class_continuous hG hz.2).1).
have hFC:=@norm_class_open_restriction R P U _ _ (inner_norm_real_norm hP) (inner_norm_real_norm hU)
  (fun z=>A (p z)) C (fun z=>f (p z)) k (fun z hz=>hz.1) hOpen hF.
have hGC:=@norm_class_open_restriction R P Z _ _ (inner_norm_real_norm hP) (inner_norm_real_norm hZ)
  (fun z=>B (q z)) C (fun z=>g (q z)) k (fun z hz=>hz.2) hOpen hG.
exact (@norm_class_inner_pair R P U Z _ (inner_norm_real_norm hP) BU BZ hU hZ C
  (fun z=>f (p z)) (fun z=>g (q z)) k hFC hGC).
Qed.

(** Source for [inner_cartesian_coordinate_system]: local product
    coordinates supporting the manifold source of 3.2.48, p. 285.
    The exact original product image and inverse are retained, rather
    than replacing the original sets by their closures or Borel hulls. *)
Theorem inner_cartesian_coordinate_system (R:realType) (V W U Z:lmodType R)
    BV BW BU BZ (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    (hU:@is_inner_product R U BU) (hZ:@is_inner_product R Z BZ)
    (M A:set V) (N B:set W) (S:set U) (T:set Z)
    (phi:V->U) (psi:U->V) (xi:W->Z) (eta:Z->W) k:
  is_norm_coordinate_system (inner_norm_real_norm hV) (inner_norm_real_norm hU) M A S phi psi k ->
  is_norm_coordinate_system (inner_norm_real_norm hW) (inner_norm_real_norm hZ) N B T xi eta k ->
  is_norm_coordinate_system
    (inner_norm_real_norm (product_inner_productP hV hW))
    (inner_norm_real_norm (product_inner_productP hU hZ))
    [set z:V*W|M z.1 /\N z.2] [set z:V*W|A z.1 /\B z.2]
    [set z:U*Z|S z.1 /\T z.2]
    (fun z=>(phi z.1,xi z.2)) (fun z=>(psi z.1,eta z.2)) k.
Proof.
move=>hM hN; constructor.
- exact (@norm_class_cartesian_blocks R V W U Z BV BW BU BZ hV hW hU hZ A B phi xi k
    (norm_coordinate_class_forward hM) (norm_coordinate_class_forward hN)).
- exact (@norm_class_cartesian_blocks R U Z V W BU BZ BV BW hU hZ hV hW S T psi eta k
    (norm_coordinate_class_backward hM) (norm_coordinate_class_backward hN)).
- move=>z [hzA hzB]; split.
  + exact (norm_coordinate_forward_range hM hzA).
  + exact (norm_coordinate_forward_range hN hzB).
- apply/seteqP; split=>z.
  + move=>[u [huS huT] <-].
    have hLeft:=norm_coordinate_backward_membership hM huS.
    have hRight:=norm_coordinate_backward_membership hN huT.
    exact (conj (conj hLeft.1 hRight.1) (conj hLeft.2 hRight.2)).
  + move=>[[hzM hzN] [hzA hzB]].
    exists (phi z.1,xi z.2).
    * split; [exact (norm_coordinate_forward_range hM hzA)|exact (norm_coordinate_forward_range hN hzB)].
    * rewrite (norm_coordinate_base_inverse hM hzM hzA) (norm_coordinate_base_inverse hN hzN hzB).
      exact (esym (surjective_pairing z)).
- move=>z [hzS hzT].
  rewrite (norm_coordinate_cancel hM hzS) (norm_coordinate_cancel hN hzT).
  exact (esym (surjective_pairing z)).
Qed.

(** Source for [inner_cartesian_convex]: supporting convex parameter
    domains for the actual product charts in 3.2.48, p. 285, by
    the independent convexity definition of 1.7.13, p. 37. *)
Lemma inner_cartesian_convex (R:realType) (V W:lmodType R) (A:set V) (B:set W):
  is_inner_convex A ->is_inner_convex B ->is_inner_convex [set z:V*W|A z.1 /\B z.2].
Proof.
move=>hA hB x y [hxA hxB] [hyA hyB] t ht ht1.
exact (conj (hA x.1 y.1 hxA hyA t ht ht1) (hB x.2 y.2 hxB hyB t ht ht1)).
Qed.
