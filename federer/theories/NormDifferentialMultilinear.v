(** Federer (1969), 3.1.1(4), p. 210: the differential of a
    continuous multilinear map on a finite product of arbitrary
    normed vector spaces. The product is abstract and its existence
    is supplied separately by NormedFamilySealed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring.
From Federer Require Import Hom RealNormUP TensorFamilyUP FamilyUpdate
  NormedFamilyUP NormedFamilyLaws NormDifferentialUP NormClassOneUP
  NormMultilinearBound NormMultilinearRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_multilinear_bound]: translate the
    printed continuity hypothesis of 3.1.1(4), p. 210, into the
    homogeneous product bound. Only the abstract product laws are used. *)
Lemma norm_class_zero_multilinear_bound (R : realType) m
    (V : 'I_m -> lmodType R) (Y P : lmodType R)
    (N : forall i, V i -> R) (NY : Y -> R)
    (hN : forall i, is_real_norm (N i)) (hNY : is_real_norm NY)
    (coordinate : forall i, Hom P (V i)) (PN : P -> R)
    (hP : is_normed_family N coordinate PN)
    (f : {dffun forall i, V i} -> Y) (hf : multilinear f) :
  norm_class_zero PN NY (fun _ => True)
    (fun x => f [ffun i : 'I_m => coordinate i x]) ->
  exists C : R, 0 <= C /\ forall x,
    NY (f x) <= C*\prod_(i<m) N i (x i).
Proof.
move=> hc; apply: (@norm_multilinear_continuous_bound R m V Y N NY hN hNY f hf).
move=> e he; have [d [hd hb]] := (hc 0 I).2 e he.
exists d; split=> // x hx.
have [u hu] := normed_family_surjective hP x.
have heq : [ffun i : 'I_m => coordinate i u]=x.
  by apply/ffunP=> i; rewrite ffunE hu.
have hz : [ffun i : 'I_m => coordinate i (0:P)]=[ffun i : 'I_m => 0 : V i].
  by apply/ffunP=> i; rewrite !ffunE linear0.
have hpu : PN u < d by rewrite (normed_family_norm hP); under eq_bigr do rewrite hu.
have hh := hb u I hpu.
by rewrite add0r heq hz in hh.
Qed.

(** Source for [norm_differential_multilinear_candidate]: formula
    (4) in Federer 3.1.1, p. 210. A linear map whose value is the
    sum of the m single-factor replacements is the differential.
    Boundedness of this candidate and the vanishing remainder are
    proved, not added as hypotheses. The empty product is included. *)
Theorem norm_differential_multilinear_candidate (R : realType) m
    (V : 'I_m -> lmodType R) (Y P : lmodType R)
    (N : forall i, V i -> R) (NY : Y -> R)
    (hN : forall i, is_real_norm (N i)) (hNY : is_real_norm NY)
    (coordinate : forall i, Hom P (V i)) (PN : P -> R)
    (hP : is_normed_family N coordinate PN)
    (f : {dffun forall i, V i} -> Y) (hf : multilinear f)
    (a : P) (L : Hom P Y) :
  norm_class_zero PN NY (fun _ => True)
    (fun x => f [ffun i : 'I_m => coordinate i x]) ->
  (forall v, L v=\sum_(i<m)
    f (family_with [ffun k : 'I_m => coordinate k a] (coordinate i v))) ->
  has_norm_differential PN NY (fun _ => True)
    (fun x => f [ffun i : 'I_m => coordinate i x]) a L.
Proof.
move=> hc hL.
have hPN := @normed_family_is_norm R m V N hN P coordinate PN hP.
have [C [hC hb]] := @norm_class_zero_multilinear_bound R m V Y P N NY hN hNY
  coordinate PN hP f hf hc.
pose B := PN a+1.
have ha0 := real_seminorm_nonnegative hPN.1 a.
have hB : 1 <= B by rewrite /B; lra.
have hB0 : 0 <= B := le_trans ler01 hB.
have hBp : 0 <= B^+m := exprn_ge0 m hB0.
have hm : 0 <= (m%:R : R) := ler0n _ _.
have hcoord x i : N i (coordinate i x) <= PN x.
  exact: (@normed_family_coordinate_bound R m V N hN P coordinate PN hP x i).
have hbase i : N i (coordinate i a) <= B.
  have hi := hcoord a i; rewrite /B; lra.
constructor.
- exists 1; split; first exact: ltr01.
  by move=> h _.
- exists ((m%:R : R)*C*(B^+m)); split.
  + exact: (mulr_ge0 (mulr_ge0 hm hC) hBp).
  + move=> v; rewrite hL; apply: le_trans (real_seminorm_sum hNY.1 _) _.
    have hs : (\sum_(i<m) NY (f
        (family_with [ffun k : 'I_m => coordinate k a] (coordinate i v))))
        <= \sum_(i<m) C*(PN v*(B^+m)).
      apply: ler_sum=> i _.
      apply: (@norm_multilinear_single_slot_bound R m V Y N NY hN f C hC hb
        [ffun k : 'I_m => coordinate k a] i (coordinate i v) B (PN v) hB).
      * exact: real_seminorm_nonnegative hPN.1 v.
      * exact: hcoord.
      * move=> k _; rewrite ffunE; exact: hbase.
    rewrite sumr_const card_ord -mulr_natl in hs.
    have heq : m%:R*(C*(PN v*(B^+m)))=(m%:R*C*(B^+m))*PN v by ring.
    by rewrite heq in hs.
- move=> e he.
  pose K := (m%:R : R)*(m%:R*C*(B^+m)).
  have hK : 0 <= K by apply: mulr_ge0=> //; exact: (mulr_ge0 (mulr_ge0 hm hC) hBp).
  have hden : 0 < K+1 by lra.
  have hed : 0 < e/(K+1) by rewrite divr_gt0.
  exists (Num.min 1 (e/(K+1))); split; first by rewrite lt_min ltr01 hed.
  move=> h _; rewrite lt_min=> /andP [hh1 hhe].
  have hH := real_seminorm_nonnegative hPN.1 h.
  pose aa := [ffun i : 'I_m => coordinate i a].
  pose hh := [ffun i : 'I_m => coordinate i h].
  have hsmall i : N i (hh i) <= PN h by rewrite /hh ffunE; exact: hcoord.
  have hab i : N i (aa i)+N i (hh i) <= B.
    rewrite /aa /hh !ffunE /B; have hi := hcoord a i; have hj := hcoord h i; lra.
  have hr := @norm_multilinear_quadratic_remainder R m V Y N NY hN hNY f hf C hC hb
    aa hh B (PN h) hB hH hsmall hab.
  have heq : [ffun i : 'I_m => coordinate i (a+h)]=
      [ffun i : 'I_m => aa i+hh i].
    by apply/ffunP=> i; rewrite /aa /hh !ffunE linearD.
  have hsum : L h=\sum_(i<m) f (family_with aa (hh i)).
    rewrite hL; apply: eq_bigr=> i _; by rewrite /aa /hh ffunE.
  rewrite heq hsum.
  change (NY (f [ffun i : 'I_m => aa i+hh i]-f aa-
    \sum_(i<m) f (family_with aa (hh i))) <= e*PN h).
  apply: le_trans hr _.
  have heprod : (e/(K+1))*(K+1)=e by rewrite divfK // gt_eqF.
  have hcoeff : K*PN h <= e by nra.
  change (K*(PN h*PN h) <= e*PN h).
  rewrite mulrA; apply: ler_wpM2r=> //.
Qed.

(** Source for [norm_differential_multilinear]: existence form of
    the continuous multilinear differential formula (4) in Federer
    3.1.1, p. 210. The candidate is built only as an existence proof;
    all assertions about the product use its abstract specification. *)
Theorem norm_differential_multilinear (R : realType) m
    (V : 'I_m -> lmodType R) (Y P : lmodType R)
    (N : forall i, V i -> R) (NY : Y -> R)
    (hN : forall i, is_real_norm (N i)) (hNY : is_real_norm NY)
    (coordinate : forall i, Hom P (V i)) (PN : P -> R)
    (hP : is_normed_family N coordinate PN)
    (f : {dffun forall i, V i} -> Y) (hf : multilinear f) :
  norm_class_zero PN NY (fun _ => True)
    (fun x => f [ffun i : 'I_m => coordinate i x]) ->
  forall a, exists L : Hom P Y,
    has_norm_differential PN NY (fun _ => True)
      (fun x => f [ffun i : 'I_m => coordinate i x]) a L /\
    forall v, L v=\sum_(i<m)
      f (family_with [ffun k : 'I_m => coordinate k a] (coordinate i v)).
Proof.
move=> hc a.
pose D v := \sum_(i<m)
  f (family_with [ffun k : 'I_m => coordinate k a] (coordinate i v)).
have hD : linear D.
  move=> c v w; rewrite /D scaler_sumr -big_split /=.
  apply: eq_bigr=> i _; rewrite (hom_linear (coordinate i)).
  exact: (@hf [ffun k : 'I_m => coordinate k a] i c (coordinate i v) (coordinate i w)).
pose L := @HomMap R P Y D (introT (asboolP _) hD).
exists L; split; last by move=> v.
apply: (@norm_differential_multilinear_candidate R m V Y P N NY hN hNY
  coordinate PN hP f hf a L hc).
by move=> v.
Qed.
