(** Federer (1969), 4.1.1, p. 343: the finite supremum defining
    nu^i_K exists. The supporting construction reuses the opaque
    bounded-function supremum from 3.1.13 rather than building a
    second supremum or an arbitrary selected upper bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP UniformFunctionNormUP BoundedFunctionNormSealed
  LinearObservationSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [linear_observation_seminorm_exists]: proved
    existence of the exact norm supremum, supporting nu^i_K in
    Federer 4.1.1, p. 343. Boundedness must be proved in each
    application; the target norms need not be definite. *)
Theorem linear_observation_seminorm_exists (R:realType) (E:lmodType R)
    (I:Type) (W:I->lmodType R) (N:forall i,W i->R)
    (L:forall i,Hom E (W i)) :
  (forall i,is_real_seminorm (@N i)) ->
  (forall f,exists C:R,0<=C /\ forall i,@N i (@L i f)<=C) ->
  exists p,is_linear_observation_seminorm N L p.
Proof.
move=>hN hBound.
have hb f:exists C:R,0<=C /\ forall i,`|@N i (@L i f)|<=C.
  have [C [hC hB]]:=hBound f; exists C; split=>// i.
  rewrite (ger0_norm (real_seminorm_nonnegative (hN i) (@L i f))).
  exact:hB.
exists (fun f=>BoundedFunctionNorm.value (hb f)); move=>f.
exact:BoundedFunctionNorm.laws.
Qed.
