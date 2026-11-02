(** Federer (1969), 3.2.28(3), p. 266:
    the actual forgetful tangent differential has
    exterior norm 2^((1-m)/2), with no
    adapted basis or coefficient hypotheses remaining. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier GrassmannAbbreviations EuclideanInnerProduct
  InnerProductRestriction OrthogonalMaps EuclideanHomInnerCharts EuclideanStiefelSubspaces
  EuclideanFrameComplementUP EuclideanFrameComplementExistence EuclideanHyperplaneNormalUP
  EuclideanHyperplaneNormalExistence EuclideanHyperplaneAdaptedFrame EuclideanForgetfulNormalFrame
  EuclideanStiefelRestrictionHom EuclideanForgetfulAdaptedJacobian InnerExteriorPositivity ExteriorMaps OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_forgetful_tangent_jacobian]: the
    actual tangent Jacobian J S=2^((1-m)/2),
    Federer 3.2.28(3), p. 266, with m=k+1.
    The source and target adapted frames are proved
    to exist locally. The conclusion retains only the
    printed dimension bound and orthogonality hypotheses,
    and includes the m=1 constant-map boundary. *)
Theorem euclidean_forgetful_tangent_jacobian (R:realType) k n
    (alpha:Hom (R_n R k) (R_n R k.+1))
    (g:Hom (R_n R k.+1) (R_n R n)):
  (k.+1<=n)%N ->
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->
  is_orthogonal_map (@euclidean_inner_product R k.+1) (@euclidean_inner_product R n)
    (hom_as_linear g) ->
  exists S:Hom (subspace_space (euclidean_stiefel_tangent_subspace g))
    (subspace_space (euclidean_stiefel_tangent_subspace (hom_comp g alpha))),
    (forall h,subspace_val (S h)=hom_comp (subspace_val h) alpha) /\
    let TS:=euclidean_stiefel_tangent_subspace g in
    let TT:=euclidean_stiefel_tangent_subspace (hom_comp g alpha) in
    let hTS:=restricted_inner_productP (@euclidean_hom_inner_productP R k.+1 n) TS in
    let hTT:=restricted_inner_productP (@euclidean_hom_inner_productP R k n) TT in
    let q:=(k*(2*n-k-1)%/2)%N in
    is_operator_norm (exterior_inner_productP (EuclideanLinearMaps.euclidean_two_nonzero R) hTS q)
      (exterior_inner_productP (EuclideanLinearMaps.euclidean_two_nonzero R) hTT q)
      (exterior_power_map (hom_as_linear S) q) ((Num.sqrt (2:R))^-k).
Proof.
move=>hkn hAlpha hG.
pose r:=(n-k.+1)%N.
have hPositive:(0<n-k)%N by rewrite subn_gt0; exact hkn.
have hRT:r.+1=(n-k)%N by rewrite /r subnS (prednK hPositive).
have [w hW]:=@euclidean_hyperplane_normal_exists R k alpha hAlpha.
have [e [hE [hEP hEL]]]:=@euclidean_hyperplane_adapted_frame_exists R k alpha w hAlpha hW.
have [a [p hComp]]:=@euclidean_frame_complement_exists R k.+1 n g hkn hG.
have [b [hB [hBN [hBP hBL]]]]:=@euclidean_forgetful_normal_frame_exists R k n r alpha w g a
  hAlpha hW hG (frame_complement_orthogonal hComp) (frame_complement_normal hComp).
have [S hS]:=@euclidean_stiefel_restriction_hom_exists R k k.+1 n alpha g hAlpha hG.
exists S; split; first exact hS.
exact:(@euclidean_forgetful_adapted_tangent_jacobian R k n r alpha w g e a b S
  hkn (erefl r) hRT hAlpha hW hG hE hEP hEL (frame_complement_orthogonal hComp)
  (frame_complement_normal hComp) hB hBN hBP hBL hS).
Qed.
