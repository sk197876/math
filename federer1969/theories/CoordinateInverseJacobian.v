(** Federer (1969), 3.2.10, p. 248: supporting linear
    Jacobian identity for the inverse-coordinate diagram. The
    proof expands the diagram with contraction naturality from
    1.6.5 and the unit duality of 1.7.8. No analytic or
    measure-theoretic hypothesis is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom HomogeneousHom TensorUP GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps CoordinateProjection
  CoordinateProjectionVolume EuclideanCoordinateVolumes ExteriorGrading ExteriorMaps
  ExteriorMapScaling ExteriorDeterminant FiniteExteriorPowers ExteriorFrameUnitNorm
  ExteriorOperatorNorm ExteriorOperatorEstimate ExteriorNorm ExteriorCovectorInner
  AlternatingCoordinates AlternatingDual AlternatingPairing CovectorProducts
  DualityMaps DualityBasis LeftInterior InteriorNaturality UpperDualityNorm
  TopTargetExteriorNorm TopExteriorNorm InitialIndices TopComplements
  EuclideanLinearJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [coordinate_inverse_jacobian]: the Jacobian
    calculation in Federer 3.2.10, p. 248. If T and M
    are mutually inverse and D composed with M is the first
    coordinate projection, then J_n D equals the complementary
    Jacobian of M times J_m T. This is a supporting linear
    statement, including both zero-dimensional blocks. *)
Theorem coordinate_inverse_jacobian (R:realType) m n (hn:(n<=m)%N)
    (T M:Hom (R_n R m) (R_n R m)) (D:Hom (R_n R m) (R_n R n)):
  cancel T M ->
  (forall x,D (M x)=coordinate_projection (Lambda_initial hn) x) ->
  euclidean_linear_jacobian n D=
    euclidean_linear_jacobian (m-n)
      (hom_comp M (hom_of_linear (@coordinate_injection R m (m-n)
        (top_complement (Lambda_initial hn))))) *
    euclidean_linear_jacobian m T.
Proof.
move=>hTM hD.
pose h2:=euclidean_two_nonzero R.
pose hB:=@euclidean_inner_productP R m.
pose hC:=@euclidean_inner_productP R n.
pose E:=e_lambda (@coordinate_basis R m) (ord_tuple m).
pose phi:=euclidean_volume_covector R n.
pose a:=A_m_dual (hom_as_linear D) phi.
pose q:=GRing.Linear.clone _ _ _ _ (@coordinate_projection R m n (Lambda_initial hn)) _.
pose j:=@coordinate_injection R m (m-n) (top_complement (Lambda_initial hn)).
pose w:=e_lambda (@coordinate_basis R m) (val (top_complement (Lambda_initial hn))).
have hE:exterior_norm h2 hB E= 1:=euclidean_top_product_unit_norm h2 m.
have hPhi:exterior_covector_norm h2 hC (@coordinate_basisP R n) phi= 1.
  exact:euclidean_volume_covector_unit.
have hNorm:exterior_norm h2 hB (D_upper h2 E hn a)=euclidean_linear_jacobian n D.
  rewrite (upper_duality_norm (@coordinate_basisP R m) hE).
  symmetry; exact (@top_target_operator_unit_value R h2 (R_n R m) (R_n R n)
    (@euclidean_inner_product R m) (@euclidean_inner_product R n) hB hC m n
    (@coordinate_basis R m) (@coordinate_basis R n)
    (@coordinate_basisP R m) (@coordinate_basisP R n) (hom_as_linear D) phi hPhi).
have hPull:A_m_dual (hom_as_linear M) a=A_m_dual q phi.
  apply:form_ext=>t; rewrite /a !A_m_dualE.
  congr (phi _); apply:eq_from_tnth=>i.
  rewrite !tnth_map; exact:hD.
have hCoord:D_upper h2 E hn (A_m_dual q phi)=w.
  rewrite /q /phi coordinate_projection_volume_pullback.
  have hDual i l:(@euclidean_coordinate_covector R m i)
      [tuple @coordinate_basis R m l]=if i==l then 1 else 0.
    by rewrite euclidean_coordinate_covectorE /coordinate_basis ffunE eq_sym.
  rewrite (@D_upper_basis R h2 (R_n R m) m (@coordinate_basis R m)
    (@euclidean_coordinate_covector R m) (@coordinate_basisP R m)
    hDual n hn (Lambda_initial hn)) /top_complement initial_complement_N expr0 scale1r.
  by [].
have hNatural:exterior_power_map (hom_as_linear M) (m-n) w=
    euclidean_det (hom_as_linear M)*:D_upper h2 E hn a.
  rewrite -hCoord -hPull /D_upper left_interior_natural.
  rewrite (@detE R h2 m (R_n R m) (@coordinate_basis R m)
    (@coordinate_basisP R m) (hom_as_linear M) E).
  exact (bilZl (@left_interior_bilinear R h2 (R_n R m) n m hn) _ _ _).
have hNormM:exterior_norm h2 hB (exterior_power_map (hom_as_linear M) (m-n) w)=
    `|euclidean_det (hom_as_linear M)|*euclidean_linear_jacobian n D.
  by rewrite hNatural exterior_norm_scale hNorm.
have hJL:euclidean_linear_jacobian (m-n) (hom_comp M (hom_of_linear j))=
    `|euclidean_det (hom_as_linear M)|*euclidean_linear_jacobian n D.
  rewrite /euclidean_linear_jacobian.
  rewrite (@top_exterior_operator_unit_value R h2 (R_n R (m-n)) (R_n R m)
    (@euclidean_inner_product R (m-n)) (@euclidean_inner_product R m)
    (@euclidean_inner_productP R (m-n)) hB (m-n) (@coordinate_basis R (m-n))
    (@coordinate_basisP R (m-n)) (hom_as_linear (hom_comp M (hom_of_linear j)))
    (e_lambda (@coordinate_basis R (m-n)) (ord_tuple (m-n)))
    (euclidean_top_product_unit_norm h2 (m-n))).
  have hComp:hom_as_linear (hom_comp M (hom_of_linear j))=1
      linear_comp (hom_as_linear M) j by move=>x.
  rewrite (exterior_power_map_ext hComp _) -exterior_power_map_composition
    /j coordinate_injection_top_product.
  exact:hNormM.
have hDet:`|euclidean_det (hom_as_linear M)|*`|euclidean_det (hom_as_linear T)|= 1.
  rewrite -normrM (euclidean_det_inverse hTM) normr1.
  by [].
rewrite hJL euclidean_linear_jacobian_determinant mulrAC hDet mul1r.
by [].
Qed.
