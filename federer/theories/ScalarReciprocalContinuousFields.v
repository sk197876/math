(** Federer (1969), 3.1.24, p. 239: the
    reciprocal differential fields used in the scalar rational
    functions computing the analytic composition sum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  NormClassOneUP NormClassHigherUP NormHigherDifferentialUP NormHigherDifferentialUnique
  ScalarReciprocalHigherDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_reciprocal_continuous_fields]: supporting
    the scalar special case in Federer 3.1.24, p. 239.
    The smooth reciprocal has continuous actual differential
    fields on the nonzero reals, with the already proved
    scalar formula at every order. Field selection uses only
    class witnesses; equality with the formula follows from
    uniqueness of the actual higher differential. *)
Theorem scalar_reciprocal_continuous_fields (R:realType)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->R^o}->Hom (Z i) R^o)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space (fun x:R^o=>`|x|) (fun x:R^o=>`|x|)
      (@ev i) (@ZN i)) :
  exists D:forall i,R->Z i,
    (forall i x,x!=0 -> has_norm_higher_differential (fun x:R^o=>`|x|) ev ZN
      (fun x=>x!=0) (fun x=>x^-1) i x (D i x)) /\
    (forall i,norm_class_zero (fun x:R^o=>`|x|) (@ZN i) (fun x=>x!=0) (D i)) /\
    forall i x,x!=0 -> forall u,@ev i u (D i x)=
      (\prod_(j<i) u j)*scalar_reciprocal_derivative_coefficient i x.
Proof.
have hf:=scalar_reciprocal_class_infinity hZ.
have hex i:= (hf i).2.
pose D i:=projT1 (cid (hex i)).
have hD i:=projT2 (cid (hex i)).
exists D; split; first by move=>i; exact (hD i).1.
split; first by move=>i; exact (hD i).2.
move=>i x hx u.
have [z [hz he]]:=scalar_reciprocal_higher_differentials hZ i hx.
have hN:=scalar_absolute_value_norm R.
have heq:D i x= z:=@norm_higher_differential_unique R R^o R^o
  (fun x=>`|x|) (fun x=>`|x|) hN hN Z ev ZN hZ (fun x=>x!=0) (fun x=>x^-1)
  i x (D i x) z ((hD i).1 x hx) hz.
by rewrite heq; exact (he u).
Qed.
