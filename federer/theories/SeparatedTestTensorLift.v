(** Federer (1969), 4.1.3, p. 348: the canonical map from
    [tensor_n D(R,R)] tensor Y follows from the universal
    properties of 1.1.1, p. 9. This supporting lift records only
    the algebra needed here; it assumes neither topology nor
    a construction of any tensor space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom TensorUP TensorFamilyUP TensorFamilySpan.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [separated_test_tensor_lift_exists]: the iterated
    tensor map used in Federer 4.1.3, p. 348, exists for every
    independently specified family and binary tensor product. *)
Theorem separated_test_tensor_lift_exists (K:fieldType) n (V:'I_n->lmodType K)
    (T Y W Z:lmodType K) (mu:{dffun forall i,V i}->T) (nu:T->Y->W)
    (hT:is_tensor_product_family mu) (hW:is_tensor_product nu)
    (beta:{dffun forall i,V i}->Y->Z):
  (forall y,multilinear (fun x=>beta x y)) ->
  (forall x,linear (beta x)) ->
  exists F:{linear W->Z},forall x y,F (nu (mu x) y)=beta x y.
Proof.
move=>hFirst hSecond.
have hFor y:exists L:{linear T->Z},forall x,L (mu x)=beta x y.
  have[L [hL _]]:=tensor_family_universal hT (hFirst y).
  by exists L.
have[L hL]:=choice hFor.
have hLinearY (t:T):linear (fun y=>L y t).
  move=>c y z.
  pose M:Hom T Z:=c*:hom_of_linear (L y)+hom_of_linear (L z).
  have hEq:forall t:T,L (c*:y+z) t=hom_as_linear M t.
    apply:(tensor_family_ext hT (L (c*:y+z)) (hom_as_linear M))=>x.
    rewrite hL hom_as_linearE /M hom_addE hom_scaleE !hom_of_linearE !hL.
    exact:(hSecond x c y z).
  have h:=hEq t.
  by rewrite hom_as_linearE /M hom_addE hom_scaleE !hom_of_linearE in h.
have hB:bilinear (fun t:T=>fun y:Y=>L y t).
  split; first by move=>y; exact:linearP.
  exact hLinearY.
have[F [hF _]]:=tensor_universal hW hB.
exists F=>x y; by rewrite hF hL.
Qed.
