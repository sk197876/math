(** Federer (1969), 3.4.10, p. 338:
    obtain the original cited surface's auxiliary
    implicit solution from the project's analytic
    joint inverse theorem. Its first two
    coordinates remain exactly (x,z). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanBlockLinearMaps
  NormDifferentialUP NormOpenDomainLaws NormFiniteLinearBound NormDiffeomorphismUP
  NormAnalyticUP FiniteAnalyticJointInverse EuclideanThreeBlockCoordinates BruhatWhitneyAuxiliaryEquation
  BruhatWhitneyAuxiliaryDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_auxiliary_joint_inverse]: the
    implicit graph near an original nonzero
    axis coordinate in the example cited by
    3.4.10, p. 338. The actual
    derivative and prefix equations establish the
    inverse theorem's kernel hypothesis internally. *)
Theorem bruhat_whitney_auxiliary_joint_inverse (R:realType) (b:R):
  let X:=R_n R 3 in
  let Y:=R_n R 2 in
  let NX:=inner_norm (@euclidean_inner_productP R 3) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R 3) in
  let a:=@bruhat_whitney_auxiliary_point R b in
  b!=0 ->exists (H G:X->X) r,
    (forall x,@euclidean_first_block_map R 2 1 (H x)=@euclidean_first_block_map R 2 1 x) /\
    (forall x i,@euclidean_last_block_map R 2 1 (H x) i=
      @bruhat_whitney_auxiliary_equation R x) /\
    @norm_analytic R X X NX NX hNX hNX setT H /\0<r /\
    (forall x,NX (x-a)<r ->setT x) /\
    is_norm_diffeomorphism hNX hNX [set x|NX (x-a)<r]
      (H @` [set x|NX (x-a)<r]) H G 1%N /\
    @norm_analytic R X X NX NX hNX hNX (H @` [set x|NX (x-a)<r]) G.
Proof.
move=>X Y NX hNX a hb.
pose P:=@euclidean_first_block_map R 2 1.
pose j:=Ordinal (isT:(1<3)%N).
have hA0:a ord0=0:=(@bruhat_whitney_auxiliary_point_coordinates R b).1.
have hAb:a j=b:=(@bruhat_whitney_auxiliary_point_coordinates R b).2.1.
have [D [hD hDValue]]:=@bruhat_whitney_auxiliary_differential R a hA0.
have hBound:=@norm_finite_linear_bounded R X Y NX
  (inner_norm (@euclidean_inner_productP R 2)) hNX
  (inner_norm_real_norm (@euclidean_inner_productP R 2)) 3
  (@coordinate_basis R 3) (@coordinate_basisP R 3) P.
have hSeparate u:P u=0 ->(forall i:'I_1,D u=0) ->u=0.
  move=>hPu hDu.
  have hMid:u j=0.
    have h:=congr1 (fun y:Y=>y ord_max) hPu.
    by rewrite /P euclidean_three_prefix_second ffunE in h.
  have hProduct:b*u ord_max=0.
    rewrite -hAb -(hDValue u hMid);exact:hDu ord0.
  have hLast:u ord_max=0.
    apply:(mulfI hb);by rewrite hProduct mulr0.
  have hSuffix:@euclidean_last_block_map R 2 1 u=0.
    apply/ffunP=>i;rewrite (ord1 i).
    rewrite euclidean_three_suffix ffunE;exact:hLast.
  have hDecomposition:=@euclidean_block_linear_decomposition R 2 1 u.
  change (u=@euclidean_first_injection_map R 2 1 (P u)+
    @euclidean_last_injection_map R 2 1 (@euclidean_last_block_map R 2 1 u)) in hDecomposition.
  by rewrite hPu hSuffix !linear0 addr0 in hDecomposition.
exact:(@finite_analytic_joint_inverse R 2 1 setT
  (fun x _=>norm_full_domain_interior NX x) P hBound
  (fun _:'I_1=>@bruhat_whitney_auxiliary_equation R)
  (fun _=>@bruhat_whitney_auxiliary_analytic R) a Logic.I
  (fun _:'I_1=>D) (fun _=>hD) hSeparate).
Qed.
