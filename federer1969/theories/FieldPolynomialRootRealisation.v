(** Federer (1969), 3.4.12, p. 339: each root of the
    original first polynomial gives one actual point in its fibre.
    Retain the original basis, prefix projection and numerator
    equations. Apply the checked coordinate realisation and cancel
    the original nonzero denominator. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import Hom FiniteCoordinates FieldPrefixCoordinatesUP
  FieldPrefixSuffixRealisation OrdinalCoordinateTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Roots.
Variable K:fieldType.
Variable X:lmodType K.
Variables n m:nat.
Variable hMN:(m<=n)%N.
Variable e:'I_n->X.
Variable omega:'I_n->Hom X K^o.
Hypothesis hDual:forall i j,omega i (e j)=if i==j then 1 else 0.
Local Notation Y:=(coordinate_space K m).
Variable P:Hom X Y.
Hypothesis hP:is_field_prefix_projection omega hMN P.
Local Notation index:=[the finType of 'I_(n-m)].
Local Notation xi:=(fun j:index=>omega (ordinal_coordinate_tail_index hMN j)).
Variable first:index.
Variable k:nat.
Variable U:set Y.
Variable delta:Y->K.
Variable b0:'I_k->Y->K.
Variable b:index->'I_k->Y->K.
Variable Z:set X.
Hypothesis hZ:forall x,Z x <->U (P x) /\
  ((xi first x)^+k+\sum_(i<k) b0 i (P x)*(xi first x)^+(i:nat)=0) /\
  (forall j,j!=first ->delta (P x)*xi j x=\sum_(i<k) b j i (P x)*(xi first x)^+(i:nat)) /\
  delta (P x)!=0.
(** Source for [field_polynomial_root_realisation]: the first
    transverse coordinate maps each original fibre onto the roots
    of its original monic equation, supporting the literal degree-k
    fibre count in 3.4.12, p. 339. The constructed source vector
    remains a local existence witness. *)
Theorem field_polynomial_root_realisation (y:Y):
  U y ->delta y!=0 ->forall z:K,
    (z^+k+\sum_(i<k) b0 i y*z^+(i:nat)=0) <->
    exists x:X,Z x /\P x=y /\xi first x=z.
Proof.
move=>hy hDelta z;split.
- move=>hRoot.
  pose t:=fun j:index=>if j==first then z else (delta y)^-1*\sum_(i<k) b j i y*z^+(i:nat).
  have [x [hPrefix hSuffix]]:=@field_prefix_suffix_realisation K X n m e omega hMN P hDual hP y t.
  have hFirst:xi first x=z by rewrite hSuffix /t eqxx.
  have hRelations j (hj:j!=first):delta y*xi j x=\sum_(i<k) b j i y*z^+(i:nat).
    by rewrite hSuffix /t (negbTE hj) mulrA mulfV // mul1r.
  exists x;split.
  + apply:(hZ x).2;rewrite hPrefix hFirst.
    split;first exact:hy.
    split;first exact:hRoot.
    split;first exact:hRelations;exact:hDelta.
  + by split.
- move=>[x [hx [hPrefix hFirst]]].
  have hRoot:=((hZ x).1 hx).2.1.
  by rewrite hPrefix hFirst in hRoot.
Qed.
End Roots.
