(** Federer (1969), 4.1.1, p. 344: smooth
    partial sums have exactly the original pointwise
    values. This supporting lemma uses only evaluation
    linearity, not a function-space implementation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP SmoothFunctionSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [smooth_finite_sum_evaluation]: evaluating
    any finite smooth sum commutes with summation,
    supporting the locally finite sum argument in
    Federer 4.1.1, p. 344. *)
Lemma smooth_finite_sum_evaluation (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev)
    (J:Type) (s:seq J) (f:J->E) x:
  ev (\sum_(j<-s) f j) x=\sum_(j<-s) ev (f j) x.
Proof.
have hLinear:linear (fun g:E=>ev g x).
  exact:(fun c g h=>@smooth_function_evaluation_linear R X Y NX NY hNX hNY U E ev hE c g h x).
pose Lx:=@HomMap R E Y (fun g=>ev g x) (introT (asboolP _) hLinear).
change (Lx (\sum_(j<-s) f j)=\sum_(j<-s) Lx (f j)).
by rewrite linear_sum.
Qed.
