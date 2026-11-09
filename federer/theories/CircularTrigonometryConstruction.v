(** Federer (1969), 3.3.19, p. 302: private existence of
    elementary circular trigonometry. The narrow trigo import
    supplies scalar power-series trigonometry and replaces none
    of the book's geometric or measure arguments. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  topology normedtype derive trigo.
From Federer Require Import RealCurveDerivativeUP RealTrigonometryUP CircularTrigonometryUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [circular_scalar_curve_derivative]: elementary
    epsilon-limit adapter supporting circular trigonometry
    in 3.3.19, p. 302; no unchecked derivative is used. *)
Lemma circular_scalar_curve_derivative (R:realType) (f:R->R) (a d:R):
  is_derive a 1 f d -> has_real_curve_derivative f a d.
Proof.
move=>[hEx hValue] e he.
have hC:((fun h:R=>h^-1 *: ((f \o shift a) (h *: (1:R)) - f a)) @ (0:R)^') --> d.
  by rewrite -hValue; exact hEx.
have hNear:=hC _ (nbhsx_ballx d e he).
move:hNear; rewrite !near_simpl near_withinE=>/nbhs_ballP[r hr hLimit].
exists r; split=>// h /andP[hh hhr].
have hn:h!= 0 by rewrite -normr_gt0.
have hB:ball (0:R) r h by rewrite /ball /= sub0r normrN.
have hv:=hLimit h hB hn.
move:hv; rewrite /ball /= /shift /= /GRing.scale /= mulr1.
rewrite mulrC addrC distrC.
by rewrite [h+a]addrC addrC.
Qed.

(** Source for [circular_trigonometry_exists]: existence of
    all independently specified elementary laws for the actual
    circular centres in 3.3.19, p. 302. *)
Theorem circular_trigonometry_exists (R:realType):
  exists S C A D:R->R,exists p:R,is_circular_trigonometry S C A D p.
Proof.
exists (@sin R),(@cos R),(@asin R),(@acos R),(@pi R);constructor.
- constructor.
  + exact:pi_gt0.
  + exact:sin0.
  + exact:cos0.
  + exact:sin_max.
  + exact:cos_max.
  + exact:sinN.
  + exact:sinDpi.
  + exact:cosDpi.
  + exact:sin_pihalf.
  + move=>x;exact:(circular_scalar_curve_derivative (is_derive_sin x)).
  + move=>x;exact:(circular_scalar_curve_derivative (is_derive_cos x)).
  + move=>x y hxl hxu hyl hyu hxy;apply:sin_inj hxy;by rewrite in_itv /=;apply/andP;split.
  + move=>y hyl hyu;have hh: -1<=y<= 1 by apply/andP;split.
    split;[exact:asin_geNpi2 hh|exact:asin_lepi2 hh].
  + move=>y hyl hyu;apply:asinK;by rewrite in_itv /= hyl hyu.
- move=>x;exact:cos2Dsin2.
- move=>x y;exact:sinD.
- move=>x y;exact:cosD.
- move=>x;exact:cosN.
- exact:sinpi.
- exact:cospi.
- move=>x hx hxpi;apply:sin_gt0_pi;by apply/andP;split.
- move=>x y hx hxp hy hyp hxy;rewrite ltr_cos // in_itv /=;by apply/andP;split.
- move=>y hyl hyu;have hh: -1<=y<= 1 by apply/andP;split.
  split;[exact:acos_ge0 hh|exact:acos_lepi hh].
- move=>y hyl hyu;apply:acosK;by rewrite in_itv /= hyl hyu.
Qed.
