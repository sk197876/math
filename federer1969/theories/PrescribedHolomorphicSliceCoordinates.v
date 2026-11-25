(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 331–332:
    restrict the actual joint inverse to
    its zero-equation slice, retaining the
    prescribed original prefix coordinates. The
    general chart theorem of 3.1.24 does
    not expose this prescribed-map equation;
    use its existing product-box and inverse-restriction laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases
  HolomorphicCoordinateNorm HolomorphicUP HolomorphicLinear HolomorphicRestriction HolomorphicFiniteCalculus
  NormDifferentialUP NormClassOneUP NormRegularity NormRegularityOperations
  NormOpenDomainLaws NormFiniteLinearBound NormLinearDomainLaws NormDiffeomorphismUP NormDiffeomorphismRestriction
  FiniteCoordinates InnerNorm InnerConvex FieldBlockLinearMaps ComplexProductBox NormAnalyticLocal NormCoordinateSystemUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrescribedSlice.
Variable R:realType.
Variables m l:nat.
Local Notation K:=(ComplexScalars.C R).
Local Notation X:=(coordinate_space K (m+l)).
Local Notation Y:=(coordinate_space K m).
Local Notation NX:=(@holomorphic_coordinate_norm R (m+l)).
Local Notation NY:=(@holomorphic_coordinate_norm R m).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R (m+l))).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R m)).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation p:=(@field_first_block_map K m l).
Local Notation q:=(@field_last_block_map K m l).
Local Notation i:=(@field_first_injection_map K m l).
Variables B T C:set X.
Variables H G:X->X.
Variable P:Hom X Y.
Variable a:X.
Hypothesis ha:B a.
Hypothesis hTa:@norm_domain_interior R XR NX T a.
Hypothesis hInverse:is_norm_diffeomorphism hNX hNX T C H G 1%N.
Hypothesis hG:@is_holomorphic R X X NX NX hNX hNX C G.
Hypothesis hPlane:forall x,T x ->(B x <->q (H x) = 0).
Hypothesis hPrefix:forall x,T x ->P x = p (H x).

(** Source for [prescribed_holomorphic_slice_coordinates]:
    p_m restricted to Z is the
    original analytic coordinate system near
    each original point, 3.4.12, p. 339, extending 3.4.8(10), pp. 331–332.
    Both the actual inverse and its
    prescribed forward map are retained. No
    local chart is assumed as a premise. *)
Theorem prescribed_holomorphic_slice_coordinates:
  exists (U:set X) (V:set Y) (psi:Y->X),
    U a /\U `<=` T /\@is_inner_convex R YR V /\
    @is_holomorphic R X Y NX NY hNX hNY U P /\
    @is_holomorphic R Y X NY NX hNY hNX V psi /\
    is_norm_coordinate_system hNX hNY B U V P psi 1%N.
Proof.
have hAt:T a:=norm_domain_interior_member hNX hTa.
have hImage:C (H a):=norm_diffeomorphism_maps hInverse hAt.
have hZero:q (H a) = 0:=(@hPlane a hAt).1 ha.
have hContinuous:=norm_class_continuous (norm_diffeomorphism_inverse_class hInverse).
have [r [hR hBox]]:=@complex_product_box_fits R m l C (H a) (@hContinuous (H a) hImage).1.
pose W:=@complex_product_box R m l (H a) r.
pose U:set X:=fun x=>T x /\W (H x).
pose V:set Y:=fun y=>NY (y-p (H a))<r.
pose psi:=fun y:Y=>G (i y).
have hW x (hx:W x):@norm_domain_interior R XR NX W x:=complex_product_box_open hx.
have hRestricted:=@norm_diffeomorphism_target_restriction R XR XR NX NX hNX hNX T C W H G 1%N
  hInverse hBox hW.
have hU x (hx:U x):@norm_domain_interior R XR NX U x.
  have hContinuousU:=norm_class_continuous (norm_diffeomorphism_forward_class hRestricted).
  exact:(@hContinuousU x hx).1.
have hV y (hy:V y):@norm_domain_interior R YR NY V y.
  exact:(@norm_open_ball_domain_interior R YR NY hNY (p (H a)) r y hy).
have hIInto y (hy:V y):W (i y).
  change (is_true (NY (p (i y)-p (H a))<r) /\
    is_true (@holomorphic_coordinate_norm R l (q (i y)-q (H a))<r)).
  have hPI:p (i y) = y:=@field_first_block_injectionK K m l y.
  have hQI:q (i y) = 0:=@field_last_block_first_injection K m l y.
  rewrite hPI hQI hZero subrr (real_seminorm_zero (complex_norm_real (@holomorphic_coordinate_norm_laws R l)).1).
  by split.
have hPsiU y (hy:V y):U (psi y).
  exact:(@norm_diffeomorphism_inverse_maps R XR XR NX NX hNX hNX U W H G 1%N hRestricted
    (i y) (hIInto y hy)).
have hCancelH y (hy:V y):H (psi y) = i y.
  exact:(@norm_diffeomorphism_right_inverse R XR XR NX NX hNX hNX U W H G 1%N hRestricted
    (i y) (hIInto y hy)).
have hPBound:=@norm_finite_linear_bounded R XR YR NX NY hNX hNY (m+l+(m+l))
  (ordered_real_basis (@coordinate_basis K (m+l))) (ordered_real_basisP (@coordinate_basisP K (m+l))) (complex_hom_real P).
have hIBound:=@norm_finite_linear_bounded R YR XR NY NX hNY hNX (m+m)
  (ordered_real_basis (@coordinate_basis K m)) (ordered_real_basisP (@coordinate_basisP K m)) (complex_hom_real i).
have hForward:=@holomorphic_bounded_linear R X Y NX NY hNX hNY U P hU hPBound.
have hGRestricted:=holomorphic_open_restriction hBox hW hG.
have hBackward:=@holomorphic_compose_on R Y X X NY NX NX hNY hNX hNX V W i G hIInto
  (@holomorphic_bounded_linear R Y X NY NX hNY hNX V i hV hIBound) hGRestricted.
have hForwardRange x (hx:U x):V (P x).
  rewrite (@hPrefix x hx.1);exact:hx.2.1.
have hCancel y (hy:V y):P (psi y) = y.
  rewrite (@hPrefix (psi y) (hPsiU y hy).1) (hCancelH y hy).
  exact:field_first_block_injectionK.
have hSet:psi @` V = B `&` U.
  apply/seteqP;split=>x.
  - move=>[y hy <-];split;last exact:hPsiU y hy.
    apply:(@hPlane _ (hPsiU y hy).1).2.
    rewrite hCancelH //;exact:field_last_block_first_injection.
  - move=>[hB hUx].
    have hZ:q (H x) = 0:=(@hPlane x hUx.1).1 hB.
    exists (P x);first exact:hForwardRange x hUx.
    have hEmbed:i (P x) = H x.
      rewrite (@hPrefix x hUx.1).
      have h:=@field_block_linear_decomposition K m l (H x).
      change (H x = i (p (H x))+@field_last_injection_map K m l (q (H x))) in h.
      by rewrite hZ linear0 addr0 in h;exact:esym h.
    rewrite /psi hEmbed.
    exact:(@norm_diffeomorphism_left_inverse R XR XR NX NX hNX hNX U W H G 1%N hRestricted x hUx).
exists U,V,psi;split.
- split;first exact:hAt.
  exact:complex_product_box_center hR.
split;first by move=>x hx;exact:hx.1.
split;first exact:(@norm_open_ball_convex R YR NY hNY (p (H a)) r).
split;first exact:hForward.
split;first exact:hBackward.
constructor.
- exact:norm_analytic_class_all_orders hForward.1 1%N.
- exact:norm_analytic_class_all_orders hBackward.1 1%N.
- exact:hForwardRange.
- exact:hSet.
- exact:hCancel.
Qed.
End PrescribedSlice.
