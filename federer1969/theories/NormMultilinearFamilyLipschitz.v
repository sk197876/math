(** Federer (1969), 3.1.1(4), p. 210, used
    for the exterior map in 3.2.28(2), p. 265:
    a multilinear difference telescopes into single-slot
    changes. Its product bound gives a uniform
    Lipschitz estimate on bounded families. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP TensorFamilyUP FamilyUpdate MultilinearFamilyAlgebra NormMultilinearRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_multilinear_bounded_family_difference]:
    the Lipschitz prerequisite for Q in Federer
    3.2.28(2), p. 265, from multilinearity
    3.1.1(4), p. 210. The actual two
    families and their coordinate differences determine
    the bound, including degree zero. *)
Theorem norm_multilinear_bounded_family_difference (R:realType) m
    (V:'I_m->lmodType R) (Y:lmodType R) (N:forall i,V i->R) (NY:Y->R)
    (hN:forall i,is_real_norm (N i)) (hNY:is_real_norm NY)
    (f:{dffun forall i,V i}->Y) C B H
    (a b:{dffun forall i,V i}):
  multilinear f ->0<=C ->(forall u,NY (f u)<=C*\prod_i N i (u i)) ->
  1<=B ->0<=H ->(forall i,N i (a i)<=B) ->(forall i,N i (b i)<=B) ->
  (forall i,N i (b i-a i)<=H) ->
  NY (f b-f a)<=m%:R*(C*(H*B^+m)).
Proof.
move=>hf hC hBound hB hH hA hD hDelta.
rewrite (multilinear_family_difference hf).
apply:le_trans (real_seminorm_sum hNY.1 _) _.
have hEach (i:'I_m):NY (f (family_with (family_prefix_mix a b i) (b i-a i)))<=C*(H*B^+m).
  apply:(@norm_multilinear_single_slot_bound R m V Y N NY hN f C hC hBound
    (family_prefix_mix a b i) i (b i-a i) B H hB hH (hDelta i)).
  move=>j _; rewrite /family_prefix_mix ffunE; case:ifP=>_; [exact:hD|exact:hA].
have hSum:(\sum_(i:'I_m) NY (f (family_with (family_prefix_mix a b i) (b i-a i))))<=
    \sum_(i:'I_m) C*(H*B^+m).
  by apply:ler_sum=>i _; exact:hEach.
by rewrite sumr_const card_ord -mulr_natl in hSum.
Qed.
