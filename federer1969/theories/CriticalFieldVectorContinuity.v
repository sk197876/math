(** Federer (1969), 3.4.2(7), pp. 312–313: continuity of fixed
    vector evaluations of the derivative field. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_derivative_vector_class_zero]: the
    continuous derivative tests that make B relatively closed in
    the proof of 3.4.2(7), p. 312. Operator continuity implies
    continuity of each fixed-vector evaluation. The vector and
    target remain arbitrary; no finite target coordinates are used. *)
Lemma critical_derivative_vector_class_zero (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (A:X->Prop)
    (f:X->Y) (D:X->Hom X Y) z:
  is_norm_class_one_field NX NY A f D ->
  norm_class_zero NX NY A (fun x=>D x z).
Proof.
move=>hD a ha;split;first exact:(norm_class_one_zero hD ha).1.
move=>epsilon hEpsilon.
have hNorm:0<=NX z:=real_seminorm_nonnegative hNX.1 z.
have hDen:0<NX z+1 by lra.
pose e:=epsilon/(NX z+1).
have he:0<e by rewrite /e divr_gt0.
have [d [hd hNear]]:=@norm_class_one_continuity R X Y NX NY A f D hD a ha e he.
exists d;split;first exact:hd.
move=>h hah hSmall.
have hBound:=hNear h hah hSmall z.
change (is_true (NY (D (a+h) z-D a z)<=e*NX z)) in hBound.
have hCancel:e*(NX z+1)=epsilon by rewrite /e divfK // gt_eqF.
have hStrict:e*NX z<epsilon by nra.
exact:(le_lt_trans hBound hStrict).
Qed.
