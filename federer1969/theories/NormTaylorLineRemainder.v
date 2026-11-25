(** Federer (1969), 3.1.11, p. 221:
    the Taylor remainder is little-o of |t|^k
    on each fixed line through the base point. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP ContinuousMultilinearUP ContinuousMultilinearZero
  NormHigherDifferentialUP NormTaylorRemainderBound NormTaylorCompactRemainder
  NormTaylorLineValues NormLittleOPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_taylor_line_little_o_fields]:
    the Taylor remainder along a+t v is
    negligible relative to |t|^k, Federer
    3.1.11, p. 221. The
    positive-order case follows from the stronger
    compact-uniform estimate; degree zero follows
    directly from continuity on the open domain. *)
Theorem norm_taylor_line_little_o_fields (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : set X) (f : X->Y) (D : forall i, X->Z i) k a v :
  A a ->
  norm_class_zero NX NY A f ->
  (forall i, (i<=k)%N -> forall x, A x ->
    has_norm_higher_differential NX ev ZN A f i x (D i x)) ->
  norm_class_zero NX (@ZN k) A (D k) ->
  norm_little_o_power NY
    (fun t=>f (a+t*:v)-norm_taylor_value ev D a (t*:v) k) k.
Proof.
move=>ha hf; case:k=>[|k] hD hc e he.
- have he0 t : norm_taylor_value ev D a (t*:v) 0%N=f a.
    rewrite /norm_taylor_value big_ord1 /= invr1 scale1r.
    rewrite (zero_arity_arguments_unique [ffun _ : 'I_0=>t*:v]
      [ffun _ : 'I_0=>(0 : X)]).
    exact: (hD 0%N (leqnn _) a ha).2.
  have [r [hr hA]] := (hf a ha).1.
  have [s [hs hb]] := (hf a ha).2 e he.
  have hm : 0<Num.min r s by rewrite lt_min hr hs.
  have [d [hd hsmall]] := norm_scalar_line_small_increments hNX v hm.
  exists d; split=> // t /andP [ht0 ht].
  have hh := hsmall t ht.
  have /andP [hhr hhs] : (NX (t*:v)<r)&&(NX (t*:v)<s) by rewrite -lt_min.
  rewrite he0 expr0 mulr1; exact: ltW (hb (t*:v) (hA _ hhr) hhs).
- pose C := (NX v)^+k.+1.
  have hC : 0<=C := exprn_ge0 _ (real_seminorm_nonnegative hNX.1 v).
  have hCp : 0<C+1 by lra.
  have he0 : 0<e/(C+1) by rewrite divr_gt0.
  have hK : compact [set x : real_norm_metric_space hNX | x=a].
    exact: compact_set1.
  have hKA : [set a] `<=` A by move=>x ->; exact ha.
  have [r [hr hb]] := @norm_taylor_remainder_compact_uniform_fields R X Y NX NY
    hNX hNY Z ev ZN hZ A [set a] f D k hD hc hK hKA (e/(C+1)) he0.
  have [d [hd hsmall]] := norm_scalar_line_small_increments hNX v hr.
  exists d; split=> // t /andP [ht0 ht].
  have [_ hraw] := hb a (t*:v) (erefl a) (hsmall t ht).
  have hcoef : (e/(C+1))*C<=e.
    have hCC : C<=C+1 by lra.
    have hh := ler_wpM2l (ltW he0) hCC.
    by rewrite divfK ?gt_eqF // in hh.
  have hfac : (1:R)<=((k.+1)`!)%:R by rewrite ler1n fact_gt0.
  have hnonneg := real_seminorm_nonnegative hNY.1
    (f (a+t*:v)-norm_taylor_value ev D a (t*:v) k.+1).
  have hfactor := ler_wpM2l hnonneg hfac; rewrite mulr1 in hfactor.
  apply: le_trans (le_trans hfactor hraw) _.
  rewrite (real_seminorm_scale hNX.1) exprMn.
  have halg : e/(C+1)*(`|t|^+k.+1*(NX v)^+k.+1)=
      (e/(C+1)*C)*`|t|^+k.+1 by rewrite /C; ring.
  rewrite halg; apply: ler_wpM2r; first exact: exprn_ge0 _ (normr_ge0 t).
  exact hcoef.
Qed.
