(** Federer (1969), 3.4.8(10), p. 332:
    relate the finite branch laws to
    the actual fibre cardinality. The
    comparison uses finite enumerations and does
    not assign cardinalities to infinite fibres. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals.
From Federer Require Import FiniteFibreEnumerationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_fibre_enumeration_cardinality]:
    the nu locally continued points give
    card(Z intersect p_m inverse{y})=nu,
    3.4.8(10), p. 332. The
    membership, coverage and injectivity laws
    imply finiteness and the exact finite cardinal. *)
Theorem finite_fibre_enumeration_cardinality (I:finType) (X:choiceType) (Y:Type)
    (P:X->Y) (Z:set X) (y:Y) (v:I->X):
  is_finite_fibre_enumeration P Z y v ->
  finite_set [set x|Z x /\P x = y] /\
    #|` fset_set [set x|Z x /\P x = y]| = #|I|.
Proof.
move=>[hPoints [hCover hInjective]].
pose F:set X:=fun x=>Z x /\P x = y.
have hImage:v @` setT = F.
  apply/seteqP;split.
  - move=>x [i _ <-];exact:hPoints i.
  - move=>x [hx hPx];have [i hi]:=hCover x hx hPx;by exists i.
have hFinite:finite_set F.
  rewrite -hImage;exact:finite_image (@finite_finset I setT).
split;first exact:hFinite.
pose s:=map v (enum I).
have hUniq:uniq s by rewrite /s map_inj_uniq // enum_uniq.
have hMember x:(x \in s) = (x \in fset_set F).
  rewrite in_fset_set //;apply/idP/asboolP.
  - move=>/mapP[i _ ->];exact:hPoints i.
  - move=>[hx hPx];have [i hi]:=hCover x hx hPx.
    apply/mapP;exists i;first by rewrite mem_enum.
    exact:esym hi.
have hPermutation:=uniq_perm hUniq (fset_uniq (fset_set F)) hMember.
have hCard:=perm_size hPermutation.
by rewrite /s size_map -cardE in hCard;exact:esym hCard.
Qed.
