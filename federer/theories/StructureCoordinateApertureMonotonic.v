(** Federer (1969), 3.3.4, p. 289: enlarge the strict coordinate
    cones by any larger positive aperture. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  StructureCoordinateCones StructureCone StructureProjectionKernel StructureApertureEnlargement
  StructureApertureBounds OrthogonalMaps EuclideanProjectionSpace SignedSquareRootSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_coordinate_cone_aperture_mono]: supporting
    the cone inclusions in Federer 3.3.4, p. 289: increasing a positive
    aperture increases the original strict coordinate cone, without any
    condition on the original source or orthogonality of its coordinates. *)
Lemma structure_coordinate_cone_aperture_mono (R:realType) m k
    (A:set (inner_metric_space (@euclidean_inner_productP R (m+k)))) a
    (f:{linear R_n R (m+k)->R_n R (m+k)}) (j:'I_k) (r: \bar R) (s t:R):
  0<s ->s<=t ->structure_coordinate_cone A a f j r s `<=`
    structure_coordinate_cone A a f j r t.
Proof.
move=>hs hst x [hA [hR hAngle]]; split=>//; split=>//.
have ht:0<t:=lt_le_trans hs hst.
have hInv:t^-1<=s^-1 by rewrite lef_pV2 ?posrE.
have hS:0<=s^-1 by rewrite invr_ge0 ltW.
have hT:0<=t^-1 by rewrite invr_ge0 ltW.
have hSquares:t^-1^+2<=s^-1^+2 by nra.
have hN:0<=(inner_norm (@euclidean_inner_productP R m)
  (@EuclideanBlockLinearMaps.euclidean_first_block R m k (f (x-a))))^+2:=sqr_ge0 _.
apply:le_lt_trans _ hAngle.
have hCoefficient:t^-1^+2-1<=s^-1^+2-1 by nra.
exact:(@ler_wpM2r R _ hN _ _ hCoefficient).
Qed.

(** Source for [structure_frame_cone_linear_enlargement]: the upper
    finite-coordinate cone inclusion in Federer 3.3.4, p. 289, followed
    by u(s)<=sqrt(k)s. This fixed linear upper enlargement is only a
    bound for the limit proof; the exact original u(s) equation and
    ratio limit are retained separately. No aperture function is chosen. *)
Theorem structure_frame_cone_linear_enlargement (R:realType) m k
    (hmn:(m<=m+k)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R (m+k)))) a
    (f:{linear R_n R (m+k)->R_n R (m+k)})
    (p:euclidean_projection_space R (m+k) m) (r: \bar R) (s:R):
  is_orthogonal_map (@euclidean_inner_product R (m+k)) (@euclidean_inner_product R (m+k)) f ->
  (forall y,euclidean_projection_linear p y=@EuclideanBlockLinearMaps.euclidean_first_block R m k (f y)) ->
  (0<k)%N ->0<s<1 ->
  A `&` structure_cone (structure_projection_kernel hmn p) a r s `<=`
    (\bigcup_j structure_coordinate_cone A a f j r ((@SignedSquareRoot.value R (k%:R))*s)).
Proof.
move=>hF hP hk hs.
have [u hU]:=structure_enlarged_aperture_exists hk hs.
have hUpper:=(structure_frame_cone_union_squeeze hmn A a r hF hP hk hs hU).2.
move=>x hx; have [j _ hj]:=hUpper x hx.
exists j=>//; apply:structure_coordinate_cone_aperture_mono hj.
- exact:(andP hU.1).1.
- exact:structure_enlarged_aperture_linear_bound hk (andP hs).1 hU.
Qed.
