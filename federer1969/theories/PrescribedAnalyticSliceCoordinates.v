(** Federer (1969), 3.4.8(10), pp. 331–332:
    restrict the actual joint inverse to
    its zero-equation slice, retaining the
    prescribed original prefix coordinates. The
    general chart theorem of 3.1.24 does
    not expose this prescribed-map equation;
    use its existing product-box and inverse-restriction laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP NormRegularity NormRegularityOperations
  NormOpenDomainLaws NormFiniteLinearBound NormLinearDomainLaws NormDiffeomorphismUP NormDiffeomorphismRestriction
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness InnerConvex
  EuclideanBlockLinearMaps EuclideanProductBox NormAnalyticUP NormAnalyticLocal NormAnalyticLinear NormAnalyticOperations
  NormCoordinateSystemUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrescribedSlice.
Variable R:realType.
Variables m l:nat.
Local Notation X:=(R_n R (m+l)).
Local Notation Y:=(R_n R m).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R (m+l))).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R (m+l))).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation p:=(@euclidean_first_block_map R m l).
Local Notation q:=(@euclidean_last_block_map R m l).
Local Notation i:=(@euclidean_first_injection_map R m l).
Variables B T C:set X.
Variables H G:X->X.
Variable P:Hom X Y.
Variable a:X.
Hypothesis ha:B a.
Hypothesis hTa:norm_domain_interior NX T a.
Hypothesis hInverse:is_norm_diffeomorphism hNX hNX T C H G 1%N.
Hypothesis hG:@norm_analytic R X X NX NX hNX hNX C G.
Hypothesis hPlane:forall x,T x ->(B x <->q (H x) = 0).
Hypothesis hPrefix:forall x,T x ->P x = p (H x).

(** Source for [prescribed_analytic_slice_coordinates]:
    p_m restricted to Z is the
    original analytic coordinate system near
    each original point, 3.4.8(10), pp. 331–332.
    Both the actual inverse and its
    prescribed forward map are retained. No
    local chart is assumed as a premise. *)
Theorem prescribed_analytic_slice_coordinates:
  exists (U:set X) (V:set Y) (psi:Y->X),
    U a /\U `<=` T /\is_inner_convex V /\
    @norm_analytic R X Y NX NY hNX hNY U P /\
    @norm_analytic R Y X NY NX hNY hNX V psi /\
    is_norm_coordinate_system hNX hNY B U V P psi 1%N.
Proof.
have hAt:T a:=norm_domain_interior_member hNX hTa.
have hImage:C (H a):=norm_diffeomorphism_maps hInverse hAt.
have hZero:q (H a) = 0:=(@hPlane a hAt).1 ha.
have hContinuous:=norm_class_continuous (norm_diffeomorphism_inverse_class hInverse).
have [r [hR hBox]]:=@euclidean_product_box_fits R m l C (H a) (@hContinuous (H a) hImage).1.
pose W:=@euclidean_product_box R m l (H a) r.
pose U:set X:=fun x=>T x /\W (H x).
pose V:set Y:=fun y=>NY (y-p (H a))<r.
pose psi:=fun y:Y=>G (i y).
have hW x (hx:W x):norm_domain_interior NX W x:=euclidean_product_box_open hx.
have hRestricted:=@norm_diffeomorphism_target_restriction R X X NX NX hNX hNX T C W H G 1%N
  hInverse hBox hW.
have hU x (hx:U x):norm_domain_interior NX U x.
  have hContinuousU:=norm_class_continuous (norm_diffeomorphism_forward_class hRestricted).
  exact:(@hContinuousU x hx).1.
have hV y (hy:V y):norm_domain_interior NY V y.
  exact:(@norm_open_ball_domain_interior R Y NY hNY (p (H a)) r y hy).
have hIInto y (hy:V y):W (i y).
  change (is_true (NY (p (i y)-p (H a))<r) /\
    is_true (inner_norm (@euclidean_inner_productP R l) (q (i y)-q (H a))<r)).
  have hPI:p (i y) = y:=@euclidean_first_block_injectionK R m l y.
  have hQI:q (i y) = 0:=@euclidean_last_block_first_injection R m l y.
  rewrite hPI hQI hZero subrr inner_norm0.
  by split.
have hPsiU y (hy:V y):U (psi y).
  exact:(@norm_diffeomorphism_inverse_maps R X X NX NX hNX hNX U W H G 1%N hRestricted
    (i y) (hIInto y hy)).
have hCancelH y (hy:V y):H (psi y) = i y.
  exact:(@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX U W H G 1%N hRestricted
    (i y) (hIInto y hy)).
have hPBound:=@norm_finite_linear_bounded R X Y NX NY hNX hNY (m+l)
  (@coordinate_basis R (m+l)) (@coordinate_basisP R (m+l)) P.
have hIBound:=@norm_finite_linear_bounded R Y X NY NX hNY hNX m
  (@coordinate_basis R m) (@coordinate_basisP R m) i.
have hForward:=@norm_bounded_linear_analytic R X Y NX NY hNX hNY U hU P hPBound.
have hGRestricted:=norm_analytic_open_restriction hBox hW hG.
have hBackward:=@norm_analytic_compose_on R Y X X NY NX NX hNY hNX hNX V W i G hIInto
  (@norm_bounded_linear_analytic R Y X NY NX hNY hNX V hV i hIBound) hGRestricted.
have hForwardRange x (hx:U x):V (P x).
  rewrite (@hPrefix x hx.1);exact:hx.2.1.
have hCancel y (hy:V y):P (psi y) = y.
  rewrite (@hPrefix (psi y) (hPsiU y hy).1) (hCancelH y hy).
  exact:euclidean_first_block_injectionK.
have hSet:psi @` V = B `&` U.
  apply/seteqP;split=>x.
  - move=>[y hy <-];split;last exact:hPsiU y hy.
    apply:(@hPlane _ (hPsiU y hy).1).2.
    rewrite hCancelH //;exact:euclidean_last_block_first_injection.
  - move=>[hB hUx].
    have hZ:q (H x) = 0:=(@hPlane x hUx.1).1 hB.
    exists (P x);first exact:hForwardRange x hUx.
    have hEmbed:i (P x) = H x.
      rewrite (@hPrefix x hUx.1).
      have h:=@euclidean_block_linear_decomposition R m l (H x).
      change (H x = i (p (H x))+@euclidean_last_injection_map R m l (q (H x))) in h.
      by rewrite hZ linear0 addr0 in h;exact:esym h.
    rewrite /psi hEmbed.
    exact:(@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX U W H G 1%N hRestricted x hUx).
exists U,V,psi;split.
- split;first exact:hAt.
  exact:euclidean_product_box_center hR.
split;first by move=>x hx;exact:hx.1.
split;first exact:(@norm_open_ball_convex R Y NY hNY (p (H a)) r).
split;first exact:hForward.
split;first exact:hBackward.
constructor.
- exact:norm_analytic_class_all_orders hForward 1%N.
- exact:norm_analytic_class_all_orders hBackward 1%N.
- exact:hForwardRange.
- exact:hSet.
- exact:hCancel.
Qed.
End PrescribedSlice.
