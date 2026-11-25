(** Federer (1969), 3.1.1(4), p. 210: a continuous multilinear
    map admits a bound by the product of the factor norms. This is
    a supporting estimate for the displayed differential formula,
    proved from continuity and multilinearity, without compactness
    or finite dimension of the factors. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP RealNormNormalization TensorFamilyUP
  MultilinearFamilyAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_multilinear_normalized_bound]: independent
    normalization of the arguments supporting 3.1.1(4), p. 210.
    A bound on products of unit balls gives a homogeneous bound.
    Zero factors and the empty product are included. *)
Lemma norm_multilinear_normalized_bound (R : realType) m
    (V : 'I_m -> lmodType R) (Y : lmodType R)
    (N : forall i, V i -> R) (NY : Y -> R)
    (hN : forall i, is_real_norm (N i)) (hNY : is_real_norm NY)
    (f : {dffun forall i, V i} -> Y) (hf : multilinear f) (C : R) :
  (forall x : {dffun forall i, V i}, (forall i, N i (x i) <= 1) -> NY (f x) <= C) ->
  forall x, NY (f x) <= C * \prod_(i<m) N i (x i).
Proof.
move=> hb x.
pose u := [ffun i : 'I_m => real_norm_normalize (N i) (x i)].
have hu : forall i, N i (u i) <= 1.
  move=> i; rewrite /u ffunE; exact: (@real_norm_normalize_unit R (V i) (N i) (hN i).1 (x i)).
have hx : x=[ffun i : 'I_m => N i (x i) *: u i].
  apply/ffunP=> i; rewrite /u !ffunE.
  symmetry; exact: (@real_norm_normalize_reconstruct R (V i) (N i) (hN i).2 (x i)).
have hp : 0 <= \prod_(i<m) N i (x i).
  apply: prodr_ge0=> i _; exact: real_seminorm_nonnegative (hN i).1 _.
rewrite {1}hx (multilinear_family_scale_all hf) (real_seminorm_scale hNY.1)
  (ger0_norm hp) mulrC.
apply: ler_wpM2r; first exact hp.
exact: hb u hu.
Qed.

(** Source for [norm_multilinear_continuous_unit_bound]: continuity
    at the zero tuple gives a finite bound on the product of unit
    balls, supporting 3.1.1(4), p. 210. Continuity is expressed by
    the sum of the factor distances, an equivalent finite-product
    norm. No boundedness of a unit sphere is assumed. *)
Lemma norm_multilinear_continuous_unit_bound (R : realType) m
    (V : 'I_m -> lmodType R) (Y : lmodType R)
    (N : forall i, V i -> R) (NY : Y -> R)
    (hN : forall i, is_real_norm (N i)) (hNY : is_real_norm NY)
    (f : {dffun forall i, V i} -> Y) (hf : multilinear f) :
  (forall e : R, 0 < e -> exists d : R, 0 < d /\
    forall x : {dffun forall i, V i}, (\sum_(i<m) N i (x i)) < d ->
      NY (f x-f [ffun i : 'I_m => 0 : V i]) < e) ->
  exists C : R, 0 <= C /\ forall x : {dffun forall i, V i},
    (forall i, N i (x i) <= 1) -> NY (f x) <= C.
Proof.
move=> hc; have [d [hd hb]] := hc 1 ltr01.
pose t := d/((m%:R : R)+1).
have hm : 0 <= (m%:R : R) := ler0n _ _.
have hden : 0 < (m%:R : R)+1 by lra.
have ht : 0 < t by rewrite /t divr_gt0.
have htd : t*((m%:R : R)+1)=d by rewrite /t divfK // gt_eqF.
have hsmall : (m%:R : R)*t < d by nra.
pose z := [ffun i : 'I_m => 0 : V i].
pose B := NY (f z)+1.
have hB : 0 < B.
  have hn := real_seminorm_nonnegative hNY.1 (f z); rewrite /B; lra.
have htp : 0 < t^+m := exprn_gt0 m ht.
exists (B/(t^+m)); split; first by apply: ltW; rewrite divr_gt0.
move=> x hx.
pose u := [ffun i : 'I_m => t *: x i].
have hu : (\sum_(i<m) N i (u i)) <= (m%:R : R)*t.
  have hs : (\sum_(i<m) N i (u i)) <= \sum_(i<m) t.
    apply: ler_sum=> i _; rewrite /u ffunE (real_seminorm_scale (hN i).1)
      (ger0_norm (ltW ht)).
    rewrite -{2}(mulr1 t); apply: ler_wpM2l; first exact: ltW ht.
    exact: hx.
  by rewrite sumr_const card_ord -mulr_natl in hs.
have hb' := hb u (le_lt_trans hu hsmall).
have htri : NY (f u) <= NY (f u-f z)+NY (f z).
  have h := real_seminorm_triangle hNY.1 (f u-f z) (f z).
  by rewrite subrK in h.
have hfu : NY (f u) <= B by rewrite /B; lra.
have hscale : f u = (t^+m) *: f x.
  rewrite /u (multilinear_family_scale_all hf) prodr_const card_ord.
  by [].
rewrite hscale (real_seminorm_scale hNY.1) (ger0_norm (ltW htp)) in hfu.
by rewrite ler_pdivlMr // mulrC.
Qed.

(** Source for [norm_multilinear_continuous_bound]: continuity
    yields the product-of-norms estimate used to prove Federer's
    multilinear derivative formula, 3.1.1(4), p. 210. *)
Theorem norm_multilinear_continuous_bound (R : realType) m
    (V : 'I_m -> lmodType R) (Y : lmodType R)
    (N : forall i, V i -> R) (NY : Y -> R)
    (hN : forall i, is_real_norm (N i)) (hNY : is_real_norm NY)
    (f : {dffun forall i, V i} -> Y) (hf : multilinear f) :
  (forall e : R, 0 < e -> exists d : R, 0 < d /\
    forall x : {dffun forall i, V i}, (\sum_(i<m) N i (x i)) < d ->
      NY (f x-f [ffun i : 'I_m => 0 : V i]) < e) ->
  exists C : R, 0 <= C /\ forall x : {dffun forall i, V i},
    NY (f x) <= C * \prod_(i<m) N i (x i).
Proof.
move=> hc.
have [C [hC hb]] := @norm_multilinear_continuous_unit_bound R m V Y N NY hN hNY f hf hc.
exists C; split=> //.
exact: (@norm_multilinear_normalized_bound R m V Y N NY hN hNY f hf C hb).
Qed.
