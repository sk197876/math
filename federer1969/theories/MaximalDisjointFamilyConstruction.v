(** Private existence proof for the maximal family in Federer (1969),
    2.5.10, p. 101. General set-theoretic Zorn is the background already
    used in this project; no maximal measure-family theorem is imported.
    Source context: MaximalDisjointFamilyUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import CountablyClosedFamilyUP MaximalDisjointFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [maximal_disjoint_family_exists]: the maximal-family choice
    in Federer 2.5.10, p. 101, with the chain proof. Empty eligibility is
    allowed. *)
Theorem maximal_disjoint_family_exists (X : choiceType) (P : set (set X)) :
  exists G, is_maximal_disjoint_family P G.
Proof.
pose Q G := G `<=` P /\ set_family_disjoint G.
pose T := {G : set (set X) | Q G}.
pose inc (a b : T) := sval a `<=` sval b.
pose rel (a b : T) := `[< inc a b >].
have hrefl a : rel a a by apply/asboolP.
have htrans a b c : rel a b -> rel b c -> rel a c.
  move=> /asboolP hab /asboolP hbc; apply/asboolP=> K hK; exact: hbc (hab K hK).
have hanti a b : rel a b -> rel b a -> a=b.
  move=> /asboolP hab /asboolP hba; case: a hab hba=> a ha; case: b=> b hb hab hba.
  apply: eq_exist; apply/seteqP; by split.
have hchain (F : set T) : total_on F rel -> exists b, forall a, F a -> rel a b.
  move=> hF; pose U := \bigcup_(a in F) sval a.
  have hUP : U `<=` P by move=> K [a ha hK]; exact: (svalP a).1 K hK.
  have hdis : set_family_disjoint U.
    move=> K L [a ha hK] [b hb hL] hKL.
    have [/asboolP hab|/asboolP hba] := hF a b ha hb.
    - exact: (svalP b).2 K L (hab K hK) hL hKL.
    - exact: (svalP a).2 K L hK (hba L hL) hKL.
  exists (exist Q U (conj hUP hdis))=> a ha; apply/asboolP=> K hK; by exists a.
have [a hmax] := @Zorn T rel hrefl htrans hanti hchain.
exists (sval a); constructor.
- exact: (svalP a).1.
- exact: (svalP a).2.
- move=> F hFP hF hin; pose b : T := exist Q F (conj hFP hF).
  have hab : rel a b by apply/asboolP.
  have hba := hmax b hab; change (sval b `<=` sval a); by rewrite hba.
Qed.
