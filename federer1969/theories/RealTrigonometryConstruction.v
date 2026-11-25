(** Federer (1969), 3.2.7, p. 246:
    existence of the elementary scalar trigonometric system.
    The narrow trigo import provides numeric sine, cosine
    and their elementary power-series calculus; it replaces
    none of Federer's measure-theoretic arguments. This
    witness is private to the sealing module and audit. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  topology normedtype derive trigo.
From Federer Require Import RealCurveDerivativeUP RealTrigonometryUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_derive_actual_curve_derivative]: supporting
    background adapter for the elementary sine derivative in
    Federer 3.2.7, p. 246. Extract the actual punctured
    epsilon limit; no value outside a derivative domain is used. *)
Lemma scalar_derive_actual_curve_derivative (R:realType) (f:R->R) (a d:R):
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

(** Source for [real_trigonometric_system_exists]: supporting
    scalar background existence for the first and third
    examples of Federer 3.2.7, p. 246. Later
    proofs use the abstract laws through an opaque seal. *)
Theorem real_trigonometric_system_exists (R:realType):
  exists S C A:R->R,exists p:R,is_real_trigonometric_system S C A p.
Proof.
exists (@sin R),(@cos R),(@asin R),(@pi R); constructor.
- exact:pi_gt0.
- exact:sin0.
- exact:cos0.
- exact:sin_max.
- exact:cos_max.
- exact:sinN.
- exact:sinDpi.
- exact:cosDpi.
- exact:sin_pihalf.
- move=>x; exact (scalar_derive_actual_curve_derivative (is_derive_sin x)).
- move=>x; exact (scalar_derive_actual_curve_derivative (is_derive_cos x)).
- move=>x y hxl hxu hyl hyu hxy; apply:sin_inj hxy; by rewrite in_itv /=; apply/andP; split.
- move=>y hyl hyu; have hh: -1<=y<= 1 by apply/andP; split.
  split; [exact (asin_geNpi2 hh)|exact (asin_lepi2 hh)].
- move=>y hyl hyu; apply:asinK; by rewrite in_itv /= hyl hyu.
Qed.
