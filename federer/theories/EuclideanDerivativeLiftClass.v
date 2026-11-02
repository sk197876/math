(** Federer (1969), 3.1.21, p. 234: the ambient tangent
    coordinate lift of a class-(k+1) map is of class k. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialUP NormDifferentialDirectional NormRegularity
  NormRegularityOperations NormRegularityLinearMaps NormRegularityDerivativeField NormFirstEvaluationBilinear
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne ContinuousMultilinearSealed
  NormFiniteLinearBound NormOpenDomainLaws EuclideanBlockLinearMaps EuclideanBundleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_derivative_lift_class]: the regularity
    loss from k to k-1 in the tangent-bundle assertion of
    Federer 3.1.21, p. 234. Written with original class
    k+1 to include the boundary class k=0 of the lift. The
    supplied derivative field is proved equal to the actual
    derivative; no regularity premise about that field is added. *)
Theorem euclidean_derivative_lift_class (R:realType) n k
    (A:R_n R n->Prop) (f:R_n R n->R_n R n)
    (D:R_n R n->Hom (R_n R n) (R_n R n)) :
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) A f k.+1 ->
  (forall x,A x -> has_norm_differential (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R n)) A f x (D x)) ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R (n+n)))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+n)))
    (fun z=>A (@euclidean_first_block_map R n n z)) (@euclidean_derivative_lift R n f D) k.
Proof.
move=>hf hD.
pose X:=R_n R n.
pose P:=R_n R (n+n).
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NP:=inner_norm (@euclidean_inner_productP R (n+n)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNP:=inner_norm_real_norm (@euclidean_inner_productP R (n+n)).
pose p:=@euclidean_first_block_map R n n.
pose q:=@euclidean_last_block_map R n n.
pose i:=@euclidean_first_injection_map R n n.
pose j:=@euclidean_last_injection_map R n n.
have hp:=@norm_finite_linear_bounded R P X NP NX hNP hNX (n+n)
  (@coordinate_basis R (n+n)) (@coordinate_basisP R (n+n)) p.
have hq:=@norm_finite_linear_bounded R P X NP NX hNP hNX (n+n)
  (@coordinate_basis R (n+n)) (@coordinate_basisP R (n+n)) q.
have hi:=@norm_finite_linear_bounded R X P NX NP hNX hNP n
  (@coordinate_basis R n) (@coordinate_basisP R n) i.
have hj:=@norm_finite_linear_bounded R X P NX NP hNX hNP n
  (@coordinate_basis R n) (@coordinate_basisP R n) j.
have hf0:=norm_class_lower (leqnSn k) hf.
have hfp:=@norm_class_precompose_linear R P X X NP NX NX hNP hNX hNX A f p k hp hf0.
have hopen z (hz:A (p z)):norm_domain_interior NP (fun z=>A (p z)) z.
  exact ((@norm_class_continuous R P X NP NX hNP hNX (fun z=>A (p z))
    (fun z=>f (p z)) k hfp z hz).1).
have hqg:=@norm_class_linear R P X NP NX hNP hNX (fun _=>True) q k
  (fun z _=>norm_full_domain_interior NP z) hq.
have hqr:=@norm_class_open_restriction R P X NP NX hNP hNX (fun _=>True)
  (fun z=>A (p z)) q k (fun _ _=>I) hopen hqg.
have [G [hGc hGd]]:=@norm_class_derivative_field R X X NX NX hNX hNX A f k hf.
pose Z:=@ContinuousMultilinear.space R 1%N X X NX NX hNX hNX.
pose ZN:=@ContinuousMultilinear.norm R 1%N X X NX NX hNX hNX.
pose ev:=@ContinuousMultilinear.evaluation R 1%N X X NX NX hNX hNX.
pose hZ:=@ContinuousMultilinear.laws R 1%N X X NX NX hNX hNX.
pose hZN:=continuous_multilinear_norm_is_norm hNX hZ.
pose op:=@continuous_multilinear_one_operator R X X Z NX NX ev ZN hZ.
have hGp:=@norm_class_precompose_linear R P X Z NP NX ZN hNP hNX hZN A G p k hp hGc.
have hEval:=@norm_class_first_evaluation R X X Z NX NX ev ZN hZ P NP hNP hNX hNX
  (fun z=>A (p z)) (fun z=>G (p z)) q k hGp hqr.
have hDE x (hx:A x):D x=op (G x).
  exact (@norm_differential_unique R X X NX NX hNX hNX A f x (D x) (op (G x))
    (hD x hx) (hGd x hx)).
have hfirst:=@norm_class_postcompose_linear R P X P NP NX NP hNP hNX hNP
  (fun z=>A (p z)) (fun z=>f (p z)) i k hi hfp.
have hlast:=@norm_class_postcompose_linear R P X P NP NX NP hNP hNX hNP
  (fun z=>A (p z)) (fun z=>op (G (p z)) (q z)) j k hj hEval.
have hsum:=norm_class_add hfirst hlast.
apply: (norm_class_domain_agreement _ hsum)=>z hz.
by rewrite /euclidean_derivative_lift -hDE.
Qed.
