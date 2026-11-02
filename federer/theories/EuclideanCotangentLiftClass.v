(** Federer (1969), 3.1.21, p. 234: one derivative of
    regularity is lost in the ambient normal coordinate lift. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDifferentialUP NormDifferentialDirectional NormRegularity NormRegularityOperations
  NormRegularityLinearMaps NormRegularityDerivativeField NormFirstAdjointEvaluation EuclideanAdjoint
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne ContinuousMultilinearSealed
  NormFiniteLinearBound NormOpenDomainLaws EuclideanBlockLinearMaps EuclideanCotangentLiftUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_cotangent_lift_class]: supporting
    regularity of the normal-bundle charts of Federer 3.1.21,
    p. 234. A class-k base map composed with the
    derivative of a class-(k+1) inverse map gives a class-k
    inverse-adjoint lift, also for k=0. *)
Theorem euclidean_cotangent_lift_class (R:realType) n k
    (A C:R_n R n->Prop) (f g:R_n R n->R_n R n)
    (E:R_n R n->Hom (R_n R n) (R_n R n)) :
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) A f k ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) C g k.+1 ->
  (forall x,A x -> C (f x)) ->
  (forall y,C y -> has_norm_differential (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R n)) C g y (E y)) ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R (n+n)))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+n)))
    (fun z=>A (@euclidean_first_block_map R n n z)) (@euclidean_cotangent_lift R n f E) k.
Proof.
move=>hf hg hfC hE.
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
have hfp:=@norm_class_precompose_linear R P X X NP NX NX hNP hNX hNX A f p k hp hf.
have hopen z (hz:A (p z)):norm_domain_interior NP (fun z=>A (p z)) z.
  exact ((@norm_class_continuous R P X NP NX hNP hNX (fun z=>A (p z))
    (fun z=>f (p z)) k hfp z hz).1).
have hqg:=@norm_class_linear R P X NP NX hNP hNX (fun _=>True) q k
  (fun z _=>norm_full_domain_interior NP z) hq.
have hqr:=@norm_class_open_restriction R P X NP NX hNP hNX (fun _=>True)
  (fun z=>A (p z)) q k (fun _ _=>I) hopen hqg.
have [G [hGc hGd]]:=@norm_class_derivative_field R X X NX NX hNX hNX C g k hg.
pose Z:=@ContinuousMultilinear.space R 1%N X X NX NX hNX hNX.
pose ZN:=@ContinuousMultilinear.norm R 1%N X X NX NX hNX hNX.
pose ev:=@ContinuousMultilinear.evaluation R 1%N X X NX NX hNX hNX.
pose hZ:=@ContinuousMultilinear.laws R 1%N X X NX NX hNX hNX.
pose hZN:=continuous_multilinear_norm_is_norm hNX hZ.
pose op:=@continuous_multilinear_one_operator R X X Z NX NX ev ZN hZ.
have hGfp:=@norm_class_compose_on R P X Z NP NX ZN hNP hNX hZN
  (fun z=>A (p z)) C (fun z=>f (p z)) G k (fun z hz=>hfC _ hz) hfp hGc.
have hEval:=@norm_class_first_adjoint_evaluation R n Z ev ZN hZ P NP hNP
  (fun z=>A (p z)) (fun z=>G (f (p z))) q k hGfp hqr.
have hEG y (hy:C y):E y=op (G y).
  exact (@norm_differential_unique R X X NX NX hNX hNX C g y (E y) (op (G y))
    (hE y hy) (hGd y hy)).
have hfirst:=@norm_class_postcompose_linear R P X P NP NX NP hNP hNX hNP
  (fun z=>A (p z)) (fun z=>f (p z)) i k hi hfp.
have hlast:=@norm_class_postcompose_linear R P X P NP NX NP hNP hNX hNP
  (fun z=>A (p z)) (fun z=>@euclidean_adjoint R n (op (G (f (p z)))) (q z)) j k hj hEval.
have hsum:=norm_class_add hfirst hlast.
apply: (norm_class_domain_agreement _ hsum)=>z hz.
by rewrite /euclidean_cotangent_lift hEG //; exact: hfC.
Qed.
