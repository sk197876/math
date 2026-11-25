(** Federer (1969), 3.2.28(3), p. 266:
    the actual restricted tangent differential has
    exterior norm 2^((1-m)/2). The proof uses
    the displayed adapted bases and actual map values;
    the scalar is not a Jacobian hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerProductRestriction OrthogonalMaps OrthonormalFamilies
  EuclideanRectangularAdjoint EuclideanHyperplaneNormalUP EuclideanHomInnerCharts EuclideanStiefelSubspaces
  EuclideanFrameRestriction EuclideanSkewIndexCardinality EuclideanStiefelTangentIndexDimension
  EuclideanStiefelAdaptedBasis EuclideanStiefelHalfNormalization EuclideanStiefelInnerSplitting
  EuclideanForgetfulTangentIndices EuclideanForgetfulJacobianCoefficients EuclideanForgetfulAdaptedImages
  LinearBasis FiniteOrdinalBasis InnerExterior InnerExteriorPositivity ExteriorMaps ExteriorGrading
  ExteriorOperatorNorm OperatorNormUP OrthonormalRectangularJacobian EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_forgetful_adapted_tangent_jacobian]:
    the displayed actual tangent Jacobian of S,
    Federer 3.2.28(3), p. 266. All adapted
    frame laws are explicit; their local existence is
    proved separately. The normal index dimensions are
    equalities, not assumptions about the Jacobian. *)
Theorem euclidean_forgetful_adapted_tangent_jacobian (R:realType) k n r
    (alpha:Hom (R_n R k) (R_n R k.+1)) w
    (g:Hom (R_n R k.+1) (R_n R n)) (e:'I_k.+1->R_n R k.+1)
    (a:Hom (R_n R r) (R_n R n)) (b:Hom (R_n R r.+1) (R_n R n))
    (S:Hom (subspace_space (euclidean_stiefel_tangent_subspace g))
      (subspace_space (euclidean_stiefel_tangent_subspace (hom_comp g alpha)))):
  (k.+1<=n)%N ->r=(n-k.+1)%N ->r.+1=(n-k)%N ->
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->is_euclidean_hyperplane_normal alpha w ->
  is_orthogonal_map (@euclidean_inner_product R k.+1) (@euclidean_inner_product R n)
    (hom_as_linear g) ->orthonormal_family (@euclidean_inner_product R k.+1) e ->
  (forall i,e (lift ord_max i)=alpha (@coordinate_basis R k i)) ->e ord_max=w ->
  is_orthogonal_map (@euclidean_inner_product R r) (@euclidean_inner_product R n)
    (hom_as_linear a) ->(forall z,euclidean_rectangular_adjoint g (a z)=0) ->
  is_orthogonal_map (@euclidean_inner_product R r.+1) (@euclidean_inner_product R n)
    (hom_as_linear b) ->(forall z,euclidean_rectangular_adjoint (hom_comp g alpha) (b z)=0) ->
  (forall j,b (@coordinate_basis R r.+1 (lift ord_max j))=a (@coordinate_basis R r j)) ->
    b (@coordinate_basis R r.+1 ord_max)=g w ->
  (forall h,subspace_val (S h)=hom_comp (subspace_val h) alpha) ->
  let TS:=euclidean_stiefel_tangent_subspace g in
  let TT:=euclidean_stiefel_tangent_subspace (hom_comp g alpha) in
  let hTS:=restricted_inner_productP (@euclidean_hom_inner_productP R k.+1 n) TS in
  let hTT:=restricted_inner_productP (@euclidean_hom_inner_productP R k n) TT in
  let q:=(k*(2*n-k-1)%/2)%N in
  is_operator_norm (exterior_inner_productP (euclidean_two_nonzero R) hTS q)
    (exterior_inner_productP (euclidean_two_nonzero R) hTT q)
    (exterior_power_map (hom_as_linear S) q) ((Num.sqrt (2:R))^-k).
Proof.
move=>hkn hR hRT hAlpha hW hG hE hEP hEL hA hAN hB hBN hBP hBL hS TS TT hTS hTT q.
pose I:=Finite.clone ((euclidean_skew_indices k.+1)+('I_k.+1*'I_r))%type _.
pose J:=Finite.clone ((euclidean_skew_indices k)+('I_k*'I_r.+1))%type _.
pose FS:=@euclidean_stiefel_adapted_direction R k.+1 n r g e a.
pose FT:=@euclidean_stiefel_adapted_direction R k n r.+1 (hom_comp g alpha) (@coordinate_basis R k) b.
have hGA:is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R n)
    (hom_as_linear (hom_comp g alpha)).
  move=>x y; change (euclidean_inner_product (g (alpha x)) (g (alpha y))=euclidean_inner_product x y).
  rewrite hG; exact:hAlpha.
pose source:=fun i:I=>@subspace_lift R (Hom (R_n R k.+1) (R_n R n)) TS (FS i)
  (@euclidean_stiefel_adapted_direction_member R k.+1 n r g e a hG hAN i).
pose target:=fun j:J=>@subspace_lift R (Hom (R_n R k) (R_n R n)) TT (FT j)
  (@euclidean_stiefel_adapted_direction_member R k n r.+1 (hom_comp g alpha)
    (@coordinate_basis R k) b hGA hBN j).
have hSource:is_basis source:=@euclidean_stiefel_adapted_tangent_basis R k.+1 n r g e a
  hG hE hA hAN hkn hR.
have hTarget:is_basis target:=@euclidean_stiefel_adapted_tangent_basis R k n r.+1
  (hom_comp g alpha) (@coordinate_basis R k) b hGA
  (@euclidean_coordinate_orthonormal_family R k) hB hBN (leq_trans (leqnSn k) hkn) hRT.
have hOS:orthonormal_family (@restricted_inner_product R _ (@euclidean_hom_inner_product R k.+1 n) TS) source:=
  @euclidean_stiefel_adapted_directions_orthonormal R k.+1 n r g e a hG hE hA hAN.
have hOT:orthonormal_family (@restricted_inner_product R _ (@euclidean_hom_inner_product R k n) TT) target:=
  @euclidean_stiefel_adapted_directions_orthonormal R k n r.+1 (hom_comp g alpha) (@coordinate_basis R k)
    b hGA (@euclidean_coordinate_orthonormal_family R k) hB hBN.
pose lambda:=@euclidean_forgetful_tangent_coefficient R k r ((Num.sqrt (2:R))^-1).
have hPair i j:@restricted_inner_product R _ (@euclidean_hom_inner_product R k n) TT
    (S (source i)) (target j)=if i==euclidean_forgetful_tangent_index j then lambda j else 0.
  change (euclidean_hom_inner_product (subspace_val (S (source i))) (FT j)=
    if i==euclidean_forgetful_tangent_index j then lambda j else 0).
  rewrite hS /source subspace_liftE.
  exact:(@euclidean_forgetful_adapted_pairing R k n r alpha w g e a b
    hAlpha hW hEP hEL hBP hBL hOT i j).
have hLambda j:0<=lambda j.
  apply:euclidean_forgetful_tangent_coefficient_nonnegative.
  exact:ltW (euclidean_stiefel_half_normalization R).1.
have hVal:=@orthonormal_rectangular_finite_exterior_jacobian R (euclidean_two_nonzero R)
  (subspace_space TS) (subspace_space TT) _ _ hTS hTT I J source hSource hOS target hTarget hOT
  (@euclidean_forgetful_tangent_index k r) lambda (hom_as_linear S)
  (@euclidean_forgetful_tangent_index_injective k r) hLambda hPair.
have hNorm:=@exterior_operator_normP R (euclidean_two_nonzero R) (subspace_space TS)
  (subspace_space TT) _ _ hTS hTT #|I| _ (finite_ordinal_basis hSource) (hom_as_linear S) #|J|.
rewrite hVal /lambda euclidean_forgetful_half_coefficient_product in hNorm.
have hQ:#|J|=q.
  have hCard:=euclidean_stiefel_tangent_index_cardinality (leq_trans (leqnSn k) hkn).
  by rewrite /euclidean_stiefel_tangent_indices -hRT in hCard.
by rewrite hQ in hNorm.
Qed.
