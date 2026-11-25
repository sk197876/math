(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 331–332:
    the prescribed p_m is an analytic
    coordinate map on the original regular
    zero system outside delta=0. Restrict
    the joint inverse to that open
    nonzero locus before taking its zero slice. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import HolomorphicLinear Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm HolomorphicCoordinateNorm HolomorphicUP HolomorphicRestriction
  NormMetric NormDifferentialUP NormDifferentialLocal NormClassOneUP NormRegularity
  NormClassZeroNonzeroLocus NormBoundedLinearTopology NormOpenDomainLaws NormAnalyticLocal
  NormCoordinateSystemUP FiniteCoordinates InnerConvex FieldBlockLinearMaps
  FiniteHolomorphicJointInverse PrescribedHolomorphicSliceCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ProjectionChart.
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
Local Notation CR:=(restricted_space (ComplexScalars.embed R) K^o).
Variables A Z:set X.
Variable P:Hom X Y.
Hypothesis hP:@norm_bounded_linear R XR YR NX NY (complex_hom_real P).
Variable f:'I_l->X->K.
Variable delta:X->K.
Hypothesis hF:forall j,@is_holomorphic R X K^o NX (@complex_modulus R) hNX
  (@complex_modulus_real_norm R) A (f j).
Hypothesis hDelta:@is_holomorphic R X K^o NX (@complex_modulus R) hNX
  (@complex_modulus_real_norm R) A delta.
Hypothesis hZ:forall x,Z x <->A x /\(forall j,f j x = 0) /\delta x<>0.
Hypothesis hJoint:forall a,Z a ->exists D:'I_l->Hom XR CR,
  (forall j,@has_norm_differential R XR CR NX (@complex_modulus R) A (f j) a (D j)) /\
  forall u,P u = 0 ->(forall j,D j u = 0) ->u=0.

(** Source for [holomorphic_equation_projection_chart]:
    each x in Z has a
    neighbourhood on which p_m restricted
    to Z is an analytic coordinate
    system, 3.4.12, p. 339, extending 3.4.8(10), pp. 331–332.
    The actual equations supply the differential;
    the existing analytic inverse theorem supplies
    the inverse. No local chart is assumed. *)
Theorem holomorphic_equation_projection_chart a:
  Z a ->exists (U:set X) (V:set Y) (psi:Y->X),
    U a /\(forall x,U x ->A x /\delta x<>0) /\@is_inner_convex R YR V /\
    @is_holomorphic R X Y NX NY hNX hNY U P /\
    @is_holomorphic R Y X NY NX hNY hNX V psi /\
    is_norm_coordinate_system hNX hNY Z U V P psi 1%N.
Proof.
move=>ha.
pose O:set X:=fun x=>A x /\delta x!=0.
have hOOpen:=@norm_class_zero_nonzero_locus_open R XR CR NX (@complex_modulus R) hNX
  (@complex_modulus_real_norm R) A delta
  (norm_class_continuous (norm_analytic_class_all_orders hDelta.1 0%N)).
have hO x (hx:O x):@norm_domain_interior R XR NX O x.
  have hNeighbourhood:=hOOpen;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R XR NX hNX O x).2 (hNeighbourhood x hx)).
have hOA:O `<=` A by move=>x hx;exact:hx.1.
have haO:O a.
  have h:=(@hZ a).1 ha;split;first exact:h.1.
  by apply/eqP;exact:h.2.2.
have hFRestricted j:=@holomorphic_open_restriction R X K^o NX (@complex_modulus R) hNX
  (@complex_modulus_real_norm R) A O (f j) hOA hO (hF j).
have [D [hD hSeparate]]:=@hJoint a ha.
have hDRestricted j:@has_norm_differential R XR CR NX (@complex_modulus R) O (f j) a (D j).
  exact:(@norm_differential_restrict R XR CR NX (@complex_modulus R) A O (f j) a (D j)
    hOA (hO a haO) (hD j)).
have [H [G [r [hFirst [hLast [hH [hR [hInto [hInverse hG]]]]]]]]]:=
  @finite_holomorphic_joint_inverse R m l O hO P hP f hFRestricted a haO D hDRestricted hSeparate.
pose T:set X:=fun x=>NX (x-a)<r.
have haT:T a by rewrite /T subrr (real_seminorm_zero hNX.1).
have hTa:@norm_domain_interior R XR NX T a:=@norm_open_ball_domain_interior R XR NX hNX a r a haT.
have hPlane x (hx:T x):Z x <->@field_last_block_map K m l (H x) = 0.
  split.
  - move=>hz;apply/ffunP=>j.
    rewrite hLast ffunE;exact:((@hZ x).1 hz).2.1 j.
  - move=>hZero;apply:(@hZ x).2;split;first exact:(@hInto x hx).1.
    split.
    + move=>j;have h:=congr1 (fun y:coordinate_space K l=>y j) hZero.
      by rewrite hLast ffunE in h.
    + apply/eqP;exact:(@hInto x hx).2.
have hPrefix x (hx:T x):P x = @field_first_block_map K m l (H x).
  exact:esym (hFirst x).
have [U [V [psi [hUa [hUT [hConvex [hForward [hBackward hChart]]]]]]]]:=
  @prescribed_holomorphic_slice_coordinates R m l Z T (H @` T) H G P a ha hTa hInverse hG hPlane hPrefix.
exists U,V,psi;split;first exact:hUa.
split.
- move=>x hx;have h:=@hInto x (hUT x hx);split;first exact:h.1.
  by apply/eqP;exact:h.2.
by split;first exact:hConvex.
Qed.
End ProjectionChart.
