(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: the
    three printed identities for finite analytic equations.
    The set identities require only scalar ring laws;
    regularity of the equations is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FiniteAnalyticVarietyUP FiniteZeroSetSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Sets.
Variable K:fieldType.
Variable X:Type.
Variable U:set X.
Local Notation var I f:=(@FiniteZeroSet.value [the zmodType of K^o] X U I f).

(** Source for [field_finite_zero_set_union]: union is given
    by all pairwise products of original equations,
    3.4.5, p. 320. The empty families are retained. *)
Lemma field_finite_zero_set_union (I J:finType) (f:I->X->K) (g:J->X->K):
  var I f `|` var J g=var (Finite.clone (I*J)%type _) (fun ij x=>f ij.1 x*g ij.2 x).
Proof.
apply/seteqP;split.
- move=>x [hF|hG].
  + have [hx hZero]:=(original_zero_set_membership (FiniteZeroSet.laws _ f) x).1 hF.
    apply/(original_zero_set_membership (FiniteZeroSet.laws _ _) x);split;first exact:hx.
    by move=>[i j];rewrite /= (hZero i) mul0r.
  + have [hx hZero]:=(original_zero_set_membership (FiniteZeroSet.laws _ g) x).1 hG.
    apply/(original_zero_set_membership (FiniteZeroSet.laws _ _) x);split;first exact:hx.
    by move=>[i j];rewrite /= (hZero j) mulr0.
- move=>x hValue;have [hx hProducts]:=(original_zero_set_membership (FiniteZeroSet.laws _ _) x).1 hValue.
  case:(pselect (forall i,f i x=0))=>[hF|hF].
  + left;apply/(original_zero_set_membership (FiniteZeroSet.laws _ f) x);by split.
  + right;apply/(original_zero_set_membership (FiniteZeroSet.laws _ g) x);split;first exact:hx.
    move=>j;apply:contrapT=>hNonzero;apply:hF=>i.
    have hProduct:=hProducts (i,j).
    have /orP [hFirst|hSecond]:(f i x==0)||(g j x==0) by rewrite -mulf_eq0 hProduct eqxx.
    * exact:(eqP hFirst).
    * exfalso;apply:hNonzero;exact:(eqP hSecond).
Qed.

(** Source for [field_finite_zero_set_intersection]: joining
    the two finite lists of original equations gives the
    intersection, 3.4.5, p. 320. *)
Lemma field_finite_zero_set_intersection (I J:finType) (f:I->X->K) (g:J->X->K):
  var I f `&` var J g=var (Finite.clone (I+J)%type _)
    (fun ij=>match ij with inl i=>f i|inr j=>g j end).
Proof.
apply/seteqP;split.
- move=>x [hF hG].
  have [hx hFZero]:=(original_zero_set_membership (FiniteZeroSet.laws _ f) x).1 hF.
  have [_ hGZero]:=(original_zero_set_membership (FiniteZeroSet.laws _ g) x).1 hG.
  apply/(original_zero_set_membership (FiniteZeroSet.laws _ _) x);split;first exact:hx.
  by move=>[i|j];[exact:hFZero i|exact:hGZero j].
- move=>x hValue;have [hx hZero]:=(original_zero_set_membership (FiniteZeroSet.laws _ _) x).1 hValue.
  split;apply/(original_zero_set_membership (FiniteZeroSet.laws _ _) x);split;first exact:hx.
  + move=>i;exact:hZero (inl i).
  + exact:hx.
  + move=>j;exact:hZero (inr j).
Qed.

End Sets.
