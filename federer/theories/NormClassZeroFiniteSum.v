(** Federer (1969), 4.1.7, p. 356: finite
    coordinate sums of continuous derivative fields
    remain continuous. This supporting consequence
    instantiates the finite-sum theorem already
    proved in 3.1.11, p. 221, at class zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP ContinuousMultilinearSealed
  NormClassHigherUP NormClassHigherLaws NormClassHigherFiniteSums.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_finite_sum]: the
    finite-sum continuity used in the class-one
    divergence formula of Federer 4.1.7,
    p. 356. This is precisely the
    previous class-k finite-sum theorem with k=0;
    the empty index family is retained. *)
Theorem norm_class_zero_finite_sum (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY) (U:X->Prop)
    (I:finType) (F:I->X->Y):
  (forall x,U x->norm_domain_interior NX U x) ->
  (forall i,norm_class_zero NX NY U (F i)) ->
  norm_class_zero NX NY U (fun x=>\sum_i F i x).
Proof.
move=>hU hF.
pose Z j:=@ContinuousMultilinear.space R j X Y NX NY hNX hNY.
pose e j:=@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY.
pose N j:=@ContinuousMultilinear.norm R j X Y NX NY hNX hNY.
pose hZ j:=@ContinuousMultilinear.laws R j X Y NX NY hNX hNY.
apply:(@norm_class_higher_zero R X Y NX NY hNY Z e N hZ U (fun x=>\sum_i F i x)).1.
apply:(@norm_class_higher_finite_sum R X Y NX NY hNX hNY Z e N hZ U hU I F 0%N)=>i.
exact:(@norm_class_higher_zero R X Y NX NY hNY Z e N hZ U (F i)).2 (hF i).
Qed.
