(** Federer (1969), 3.1.11, p. 219:
    the homogeneous finite bound used to specify multilinear
    maps is equivalent to continuity. The proof uses the
    abstract finite-product norm and the telescoping argument
    already developed for 3.1.1(4), p. 210. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP TensorFamilyUP FamilyUpdate
  MultilinearFamilyAlgebra NormedFamilyUP NormedFamilyLaws
  NormMultilinearRemainder NormDifferentialMultilinear NormClassOneUP
  ContinuousMultilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_bounded_multilinear_continuous]:
    every bounded multilinear form is continuous on the
    product, as required for the space of Federer 3.1.11,
    p. 219. The empty product is included, with no
    finite-dimensional or completeness assumption on the factors. *)
Theorem norm_bounded_multilinear_continuous (R : realType) k
    (X Y P : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (coordinate : forall i : 'I_k, Hom P X) (PN : P->R)
    (hP : is_normed_family (fun _ : 'I_k=>NX) coordinate PN)
    (f : {ffun 'I_k->X}->Y) :
  norm_bounded_multilinear NX NY f ->
  norm_class_zero PN NY (fun _=>True)
    (fun x=>f [ffun i : 'I_k=>coordinate i x]).
Proof.
move=> [hf [C [hC hb]]].
have hPN := @normed_family_is_norm R k (fun _ : 'I_k=>X)
  (fun _=>NX) (fun _=>hNX) P coordinate PN hP.
have hc x i : NX (coordinate i x)<=PN x.
  exact: (@normed_family_coordinate_bound R k (fun _ : 'I_k=>X)
    (fun _=>NX) (fun _=>hNX) P coordinate PN hP x i).
move=> a _; split.
- exists 1; split; first exact: ltr01; by move=> h hh.
- move=> e he.
  pose B := PN a+1.
  pose K := (k%:R : R)*C*(B^+k).
  have ha0 := real_seminorm_nonnegative hPN.1 a.
  have hB : 1<=B by rewrite /B; lra.
  have hK : 0<=K.
    rewrite /K; apply: mulr_ge0; first exact: mulr_ge0 (ler0n _ _) hC.
    exact (exprn_ge0 k (le_trans ler01 hB)).
  have hden : 0<K+1 by lra.
  have hep : 0<e/(K+1) by rewrite divr_gt0.
  exists (Num.min 1 (e/(K+1))); split; first by rewrite lt_min ltr01 hep.
  move=> h _; rewrite lt_min=> /andP [hh1 hhe].
  pose aa := [ffun i : 'I_k=>coordinate i a].
  pose bb := [ffun i : 'I_k=>coordinate i (a+h)].
  have hH : 0<=PN h := real_seminorm_nonnegative hPN.1 h.
  have hbase i : NX (aa i)<=B.
    rewrite /aa ffunE /B; have hi := hc a i; lra.
  have hnext i : NX (bb i)<=B.
    rewrite /bb ffunE.
    have hi := hc (a+h) i.
    have ht := real_seminorm_triangle hPN.1 a h.
    rewrite /B; lra.
  have hslot (i : 'I_k) :
      NY (f (family_with (i:=i) (family_prefix_mix aa bb i) (bb i-aa i)))<=
        C*(PN h*(B^+k)).
    apply: (@norm_multilinear_single_slot_bound R k (fun _ : 'I_k=>X) Y
      (fun _=>NX) NY (fun _=>hNX) f C hC hb
      (family_prefix_mix aa bb i) i (bb i-aa i) B (PN h) hB hH).
    + rewrite /aa /bb !ffunE linearD /= addrAC subrr add0r; exact: hc.
    + move=> j _; rewrite /family_prefix_mix ffunE.
      case: ifP=> _; [exact: hnext|exact: hbase].
  have hdiff : NY (f bb-f aa)<=K*PN h.
    rewrite (multilinear_family_difference hf).
    apply: le_trans (real_seminorm_sum hNY.1 _) _.
    have hs : (\sum_(i<k) NY (f (family_with (i:=i) (family_prefix_mix aa bb i) (bb i-aa i))))
        <=\sum_(i<k) C*(PN h*(B^+k)).
      apply: ler_sum=> i _; exact: hslot.
    rewrite sumr_const card_ord -mulr_natl in hs.
    have heq : k%:R*(C*(PN h*(B^+k)))=K*PN h by rewrite /K; ring.
    by rewrite heq in hs.
  apply: le_lt_trans hdiff _.
  have heq : e/(K+1)*(K+1)=e by rewrite divfK // gt_eqF.
  have hh : PN h*(K+1)<e by rewrite -heq ltr_pM2r.
  nra.
Qed.

(** Source for [norm_bounded_multilinear_continuity_equivalence]:
    the exact continuous-map interpretation of the intrinsic
    finite-bound specification for Federer 3.1.11, p. 219.
    The converse uses the continuity-to-bound result already
    proved for 3.1.1(4), p. 210. *)
Theorem norm_bounded_multilinear_continuity_equivalence (R : realType) k
    (X Y P : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (coordinate : forall i : 'I_k, Hom P X) (PN : P->R)
    (hP : is_normed_family (fun _ : 'I_k=>NX) coordinate PN)
    (f : {ffun 'I_k->X}->Y) :
  norm_bounded_multilinear NX NY f <->
  multilinear f /\ norm_class_zero PN NY (fun _=>True)
    (fun x=>f [ffun i : 'I_k=>coordinate i x]).
Proof.
split.
- move=> hf; split; first exact: hf.1.
  exact (@norm_bounded_multilinear_continuous R k X Y P NX NY hNX hNY coordinate PN hP f hf).
- move=> [hf hc]; split=> //.
  exact: (@norm_class_zero_multilinear_bound R k (fun _ : 'I_k=>X) Y P
    (fun _=>NX) NY (fun _=>hNX) hNY coordinate PN hP f hf hc).
Qed.
