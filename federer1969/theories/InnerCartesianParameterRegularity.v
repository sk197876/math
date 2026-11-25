(** Federer (1969), 3.2.47, p. 283: the actual
    Cartesian product of local E and I parametrizations.
    Euclidean parameter blocks feed the original finite inner
    ambient spaces, with their sealed Cartesian inner metric.
    All regularity is derived on the exact original domains. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness ProductInner
  NormDifferentialUP NormRegularity NormRegularityOperations NormRegularityLinearMaps
  NormFiniteLinearBound NormCartesianRegularity ProductInnerPairRegularity
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_cartesian_parameter_norm_class]: the
    actual product parameter map is class k on the product
    parameter domain, supporting the product parametrization of
    Phi inverse(E) in 3.2.47, p. 283. Empty parameter
    blocks and original domains are retained. *)
Theorem inner_cartesian_parameter_norm_class (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) r mu
    (A:set (R_n R r)) (D:set (R_n R mu))
    (f:R_n R r->V) (g:R_n R mu->W) k:
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R r))
    (inner_norm_real_norm hB) A f k ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R mu))
    (inner_norm_real_norm hC) D g k ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R (r+mu)))
    (inner_norm_real_norm (product_inner_productP hB hC)) (euclidean_cartesian_set A D)
    (fun z=> (f (euclidean_block_split z).1,g (euclidean_block_split z).2)) k.
Proof.
move=>hf hg.
pose X:=R_n R (r+mu).
pose hX:=inner_norm_real_norm (@euclidean_inner_productP R (r+mu)).
pose hR:=inner_norm_real_norm (@euclidean_inner_productP R r).
pose hMu:=inner_norm_real_norm (@euclidean_inner_productP R mu).
pose hV:=inner_norm_real_norm hB.
pose hW:=inner_norm_real_norm hC.
pose P:=@euclidean_first_block_map R r mu.
pose Q:=@euclidean_last_block_map R r mu.
have hP:=@norm_finite_linear_bounded R X (R_n R r) _ _ hX hR
  (r+mu)%N (@coordinate_basis R (r+mu)) (@coordinate_basisP R (r+mu)) P.
have hQ:=@norm_finite_linear_bounded R X (R_n R mu) _ _ hX hMu
  (r+mu)%N (@coordinate_basis R (r+mu)) (@coordinate_basisP R (r+mu)) Q.
have hLeft:=@norm_class_precompose_linear R X (R_n R r) V _ _ _ hX hR hV A f P k hP hf.
have hRight:=@norm_class_precompose_linear R X (R_n R mu) W _ _ _ hX hMu hW D g Q k hQ hg.
pose K:=euclidean_cartesian_set A D.
have hOpen x (hx:K x):norm_domain_interior (inner_norm (@euclidean_inner_productP R (r+mu))) K x.
  exact (@norm_intersection_domain_interior R X _ (fun x=>A (P x)) (fun x=>D (Q x)) x
    ((@norm_class_continuous R X V _ _ hX hV _ _ k hLeft x hx.1).1)
    ((@norm_class_continuous R X W _ _ hX hW _ _ k hRight x hx.2).1)).
have hLeftK:=@norm_class_open_restriction R X V _ _ hX hV
  (fun x=>A (P x)) K (fun x=>f (P x)) k (fun x hx=>hx.1) hOpen hLeft.
have hRightK:=@norm_class_open_restriction R X W _ _ hX hW
  (fun x=>D (Q x)) K (fun x=>g (Q x)) k (fun x hx=>hx.2) hOpen hRight.
exact (@norm_class_inner_pair R X V W _ hX B C hB hC K (fun x=>f (P x)) (fun x=>g (Q x))
  k hLeftK hRightK).
Qed.
