(** Federer (1969), 3.1.24, pp. 237–238: the
    operator bound implies the diagonal bound on the unit ball. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_multilinear_unit_bound]: the immediate
    implication (1) to (2) of Federer 3.1.24,
    pp. 237–238, before factorial normalization. The
    product of the argument norms is at most one. *)
Lemma norm_multilinear_unit_bound (R:realType) m (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX)
    (ev:{ffun 'I_m->X}->Hom Z Y) (ZN:Z->R)
    (hZ:is_continuous_multilinear_space NX NY ev ZN) z (u:{ffun 'I_m->X}) :
  (forall i,NX (u i)<=1) -> NY (ev u z)<=ZN z.
Proof.
move=>hu.
have hterms i (_:predT i):0<=NX (u i)<=1.
  apply/andP; split; first exact (real_seminorm_nonnegative hNX.1 (u i)).
  exact (hu i).
have hp:=@ler_prod R 'I_m (Finite.enum 'I_m) predT (fun i=>NX (u i)) (fun _=>1) hterms.
have hone:(\prod_(i<m) (1:R))= 1 by apply: big1.
change (is_true (\prod_(i<m) NX (u i)<=\prod_(i<m) (1:R))) in hp.
rewrite hone in hp.
have hb:=multilinear_operator_bound (continuous_multilinear_norm_laws hZ z) u.
have hs:=ler_wpM2l (multilinear_operator_nonnegative (continuous_multilinear_norm_laws hZ z)) hp.
rewrite mulr1 in hs; exact (le_trans hb hs).
Qed.

(** Source for [norm_multilinear_normalized_unit_bound]: the
    factorial-normalized diagonal estimate in Federer 3.1.24,
    p. 238, condition (2), from a bound C m!
    for the operator norm. Degree zero is also valid. *)
Lemma norm_multilinear_normalized_unit_bound (R:realType) m (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (ev:{ffun 'I_m->X}->Hom Z Y) (ZN:Z->R)
    (hZ:is_continuous_multilinear_space NX NY ev ZN) z (u:{ffun 'I_m->X}) C :
  (forall i,NX (u i)<=1) -> ZN z<=C*(m`!)%:R ->
  NY ((m`!)%:R^-1 *: ev u z)<=C.
Proof.
move=>hu hc.
have hfac:0<((m`!)%:R:R) by rewrite ltr0n fact_gt0.
have hinv:0<=((m`!)%:R:R)^-1 by rewrite invr_ge0; exact: ltW hfac.
rewrite (real_seminorm_scale hNY.1) (ger0_norm hinv).
have hb:=@norm_multilinear_unit_bound R m X Y Z NX NY hNX ev ZN hZ z u hu.
apply: le_trans (ler_wpM2l hinv (le_trans hb hc)) _.
rewrite mulrCA mulVf ?mulr1 //; exact: lt0r_neq0 hfac.
Qed.
