(** Federer (1969), 2.2.1, p. 59: the smallest Borel family consists of the
    empty set and X. The largest family is proved in
    BorelFamilyIntersection.v. Source context: BorelFamilyUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import BorelFamilyUP BorelFamilyBasic BorelFamilyRedundancy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_family_trivial]: Federer 2.2.1,
    p. 59, the family consisting of the empty set and X is
    Borel, including the case X itself is empty. *)
Lemma borel_family_trivial (I : choiceType) (X : set I) :
  is_borel_family X [set A | A = set0 \/ A = X].
Proof.
apply: borel_family_of_union.
- by left.
- by move=> A [->|->] x hx.
- move=> A [->|->]; [right|left]; by rewrite ?setD0 ?setDv.
- move=> G hG _; case: (pselect (exists A, G A /\ A = X))=> [[A [hA heA]]|hn].
  + rewrite heA in hA; right; apply/seteqP; split.
    * move=> x [B hB hx]; have [he|he] := hG B hB; by rewrite he in hx.
    * move=> x hx; by exists X.
  + left; apply/seteqP; split=> [x [A hA hx]|x []].
    have [he|he] := hG A hA; first by rewrite he in hx.
    exfalso; apply: hn; exists A; by split.
Qed.

(** Source for [borel_family_trivial_least]: Federer 2.2.1,
    p. 59, every Borel family contains the smallest family
    consisting of the empty and whole sets. *)
Lemma borel_family_trivial_least (I : choiceType) (X : set I) (F : set (set I)) :
  is_borel_family X F -> [set A | A = set0 \/ A = X] `<=` F.
Proof.
move=> hF A [->|->]; [exact: borel_family_empty hF|exact: borel_family_whole hF].
Qed.
