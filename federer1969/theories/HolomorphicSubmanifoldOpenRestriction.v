(** Federer (1969), 3.4.12, p. 339: open restrictions
    of original holomorphic manifolds preserve their complex dimension.
    Restrict the existing chart and retain its original complex plane. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import NormBoundedLinearTopology RealNormUP ScalarRestriction ComplexScalarSealed NormMetric NormDifferentialUP
  NormAnalyticLocal NormAnalyticUP HolomorphicUP HolomorphicDiffeomorphismUP
  HolomorphicDiffeomorphismRestriction HolomorphicSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_submanifold_open_restriction]: the
    holomorphic version of the open chart restriction used in
    3.4.10, p. 337, as extended by 3.4.12, p. 339.
    All original chart maps and the complex vector plane remain. *)
Theorem holomorphic_submanifold_open_restriction (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    m (S U:set X):
  is_holomorphic_submanifold hNX m S ->@open (real_norm_metric_space hNX) U ->
  is_holomorphic_submanifold hNX m (S `&` U).
Proof.
move=>hS hU b [hbS hbU].
have [T [C [f [g [Z [hTb [hD hImage]]]]]]]:=hS b hbS.
pose W:=T `&` U.
pose V:=fun y=>C y /\W (g y).
have hT:=norm_analytic_domain_open (holomorphic_diffeomorphism_forward hD).1.
have hWOpen:@open (real_norm_metric_space hNX) W:=openI hT hU.
have hWInterior x (hx:W x):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX W x.
  apply:(@norm_domain_interior_neighbourhood R (restricted_space (ComplexScalars.embed R) X) NX hNX W x).2.
  have h:=hWOpen;rewrite openE in h;exact:h x hx.
have hbT:T b:=norm_domain_interior_member hNX hTb.
exists W,V,f,g,Z;split;first exact:hWInterior b (conj hbT hbU).
split;first exact:(@holomorphic_diffeomorphism_source_restriction R X NX hNX T C W f g hD
  (fun x hx=>hx.1) hWInterior).
apply/seteqP;split.
- move=>y [x [[hxS hxU] [hxT _]] <-].
  have hOld:=hImage;have hMember:(f @` (S `&` T)) (f x) by exists x;first split.
  rewrite hOld in hMember;split;first exact:hMember.1.
  split;first exact:hMember.2.
  by rewrite (@holomorphic_diffeomorphism_left_inverse R X NX hNX T C f g hD x hxT);split.
- move=>y [hyZ [hyC hyW]].
  have hMember:(f @` (S `&` T)) y by rewrite hImage;split.
  have [x [hxS hxT] hXY]:=hMember.
  have hGX:g y=x by rewrite -hXY;exact:(@holomorphic_diffeomorphism_left_inverse R X NX hNX T C f g hD x hxT).
  exists x;last exact:hXY.
  split;last by split=>//;rewrite -hGX;exact:hyW.2.
  split;first exact:hxS.
  by rewrite -hGX;exact:hyW.2.
Qed.
