(** Federer (1969), 4.1.3, p. 348: finite linear sums of
    pure tensor images remain in the actual canonical image.
    This is the algebraic step for the original Borel partition
    sums in 4.1.2, p. 348. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_tensor_image_sum]: the actual finite
    partition sum stays in the canonical linear image,
    Federer 4.1.3, p. 348. *)
Lemma finite_tensor_image_sum (K:fieldType) (U V:lmodType K)
    (F:Hom U V) (I:finType) (c:I->K) (f:I->V):
  (forall i,exists u:U,F u=f i) ->
  exists u:U,F u=\sum_i c i*:f i.
Proof.
move=>hFor; have[u hu]:=choice hFor.
exists (\sum_i c i*:u i).
rewrite linear_sum; apply:eq_bigr=>i _.
have hZ:F (c i*:u i)=c i*:F (u i) by rewrite linearZ.
change (F (c i*:u i)=c i*:f i).
by rewrite hZ hu.
Qed.
