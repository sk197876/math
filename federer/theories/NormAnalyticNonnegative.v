(** Federer (1969), 3.1.24, pp. 237–238:
    the finite analytic bound is necessarily nonnegative. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormRegularity NormHigherDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_diagonal_witness_nonnegative]: supporting
    the radius choice in Federer 3.1.24, p. 238,
    implication (2) to (3). At the centre the
    first differential exists, and evaluating its diagonal bound
    at zero gives a nonnegative norm below c. Nonnegativity
    of c is therefore a consequence, not an added hypothesis. *)
Lemma norm_diagonal_witness_nonnegative (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (f:X->Y) a c :
  U a -> norm_class_all_orders hNX hNY U f ->
  (forall m,(1<=m)%N -> forall x,U x ->
    forall z:@ContinuousMultilinear.space R m X Y NX NY hNX hNY,
      has_norm_higher_differential NX
        (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
        (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY) U f m x z ->
      forall v,NX v<=1 ->
        NY ((m`!)%:R^-1 *: @ContinuousMultilinear.evaluation R m X Y NX NY hNX hNY
          [ffun i=>v] z)<=c^+m) -> 0<=c.
Proof.
move=>ha hf hb.
have [_ [D [hD hc]]]:=hf 1%N.
have hz:=hD a ha.
have hv:NX (0:X)<=1 by rewrite (real_seminorm_zero hNX.1) ler01.
have hh:=hb 1%N (leqnn 1%N) a ha (D a) hz 0 hv.
rewrite expr1 in hh.
exact (le_trans (real_seminorm_nonnegative hNY.1 _) hh).
Qed.
