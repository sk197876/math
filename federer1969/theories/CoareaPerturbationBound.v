(** Federer (1969), 3.2.11, p. 249: establish
    the two norm bounds for the prescribed perturbation.
    The critical-rank Jacobian estimate is derived from its
    actual adjoint and a unit annihilating covector. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerNormInequalities InnerProductUP EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanBlockNorms EuclideanMetricProduct MetricCartesianProductUP InnerMetric
  EuclideanRectangularAdjoint CoareaAdjointBound CoareaLinearDuality CoareaPerturbationLinear
  EuclideanLinearJacobian TopJacobianSmallDirection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coarea_block_projection_norms]: the block
    projection bounds used for ||Dg||<=Lip(f)+epsilon in
    Federer 3.2.11, p. 249. Supporting consequence of
    the existing nonexpanding coordinate projections, including empty blocks. *)
Lemma coarea_block_projection_norms (R:realType) m n (x:R_n R (m+n)):
  inner_norm (@euclidean_inner_productP R m) (@euclidean_first_block_map R m n x)<=
    inner_norm (@euclidean_inner_productP R (m+n)) x /\
  inner_norm (@euclidean_inner_productP R n) (@euclidean_last_block_map R m n x)<=
    inner_norm (@euclidean_inner_productP R (m+n)) x.
Proof.
pose hP:=@euclidean_blocks_are_metric_product R m n.
have hFirst:=(metric_product_first_nonexpanding hP).2 x 0 Logic.I Logic.I.
have hLast:=(metric_product_second_nonexpanding hP).2 x 0 Logic.I Logic.I.
change (is_true (inner_norm (@euclidean_inner_productP R m)
  (@euclidean_first_block_map R m n x-@euclidean_first_block_map R m n 0)<=
  1*inner_norm (@euclidean_inner_productP R (m+n)) (x-0))) in hFirst.
change (is_true (inner_norm (@euclidean_inner_productP R n)
  (@euclidean_last_block_map R m n x-@euclidean_last_block_map R m n 0)<=
  1*inner_norm (@euclidean_inner_productP R (m+n)) (x-0))) in hLast.
rewrite ?linear0 ?subr0 ?addr0 ?mul1r in hFirst hLast.
by split.
Qed.

(** Source for [coarea_perturbation_linear_bound]: ||Dg||
    is at most Lip(f)+epsilon in Federer 3.2.11,
    p. 249. Supporting homogeneous linear estimate, using
    any nonnegative bound L for D and nonnegative epsilon. *)
Lemma coarea_perturbation_linear_bound (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)) L e:
  0<=L ->0<=e ->
  (forall x,inner_norm (@euclidean_inner_productP R n) (D x)<=
    L*inner_norm (@euclidean_inner_productP R m) x) ->
  forall w,inner_norm (@euclidean_inner_productP R n) (coarea_perturbation_linear D e w)<=
    (L+e)*inner_norm (@euclidean_inner_productP R (m+n)) w.
Proof.
move=>hL he hBound w.
pose p:=@euclidean_first_block_map R m n.
pose q:=@euclidean_last_block_map R m n.
pose hN:=@euclidean_inner_productP R n.
change (is_true (inner_norm hN (D (p w)+e*:q w)<=
  (L+e)*inner_norm (@euclidean_inner_productP R (m+n)) w)).
apply:le_trans (inner_norm_triangle hN _ _) _.
rewrite inner_normZ (ger0_norm he).
apply:le_trans (lerD (hBound (p w)) (lexx _)) _.
have [hp hq]:=@coarea_block_projection_norms R m n w.
rewrite mulrDl.
exact (lerD (ler_wpM2l hL hp) (ler_wpM2l he hq)).
Qed.

(** Source for [coarea_critical_perturbation_jacobian_bound]:
    J_n g<=epsilon (Lip(f)+epsilon)^(n-1) in Federer
    3.2.11, p. 249. Here the target dimension is n+1.
    Criticality yields a proved unit annihilator; Dg* has
    length epsilon in that direction and uniform bound L+epsilon.
    Apply the source-top exterior estimate to the adjoint. *)
Theorem coarea_critical_perturbation_jacobian_bound (R:realType) m n
    (D:Hom (R_n R m) (R_n R n.+1)) L e:
  0<=L ->0<e ->euclidean_linear_jacobian n.+1 D=0 ->
  (forall x,inner_norm (@euclidean_inner_productP R n.+1) (D x)<=
    L*inner_norm (@euclidean_inner_productP R m) x) ->
  euclidean_linear_jacobian n.+1 (coarea_perturbation_linear D e)<=e*(L+e)^+n.
Proof.
move=>hL he hD hBound.
pose P:=coarea_perturbation_linear D e.
have hC:0<=L+e:=addr_ge0 hL (ltW he).
have hPBound:=coarea_perturbation_linear_bound hL (ltW he) hBound.
have hAdjBound:=euclidean_rectangular_adjoint_bound hC hPBound.
have [b [hUnit hKernel]]:=critical_differential_unit_annihilator hD.
have hNorm:inner_norm (@euclidean_inner_productP R n.+1) b= 1.
  apply:inner_norm_value; first exact:ler01.
  by rewrite expr1n hUnit.
have hSmall:inner_norm (@euclidean_inner_productP R (m+n.+1))
    (euclidean_rectangular_adjoint P b)<=e.
  rewrite /P coarea_perturbation_adjoint_pair hKernel.
  change (is_true (inner_norm (@euclidean_inner_productP R (m+n.+1))
    (@euclidean_last_injection R m n.+1 (e*:b))<=e)).
  by rewrite euclidean_last_injection_norm inner_normZ (ger0_norm (ltW he)) hNorm mulr1.
rewrite euclidean_target_jacobian_adjoint.
exact (@euclidean_top_jacobian_small_direction R n (m+n.+1)
  (euclidean_rectangular_adjoint P) b e (L+e) hUnit (ltW he) hC hSmall hAdjBound).
Qed.
