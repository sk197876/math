(** Federer (1969), 3.3.20, p. 308:
    the finite missing-square inference in the class Omega. *)
From mathcomp Require Import all_boot all_order finmap boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.

(** Source for [finite_paired_missing_pigeonhole]: the
    original Omega rule in 3.3.20, p. 308.
    If fewer than card(K)+card(I) cells are missed,
    and disjoint pairs avoid the already missed K,
    some pair has both endpoints actually hit. The
    endpoints and K remain local finite witnesses. *)
Theorem finite_paired_missing_pigeonhole (X:choiceType) (I:finType)
    (F M K:{fset X}) (e:I*bool->X):
  {subset M<=F} ->{subset K<=M} ->injective e ->
  (forall i b,e (i,b) \in F /\e (i,b) \notin K) ->
  (#|` M|<#|` K|+#|I|)%N ->
  exists i:I,e (i,false) \notin M /\e (i,true) \notin M.
Proof.
move=>hMF hKM hInjective hEndpoints hCount.
apply:contrapT=>hNone.
have hSome i:(e (i,false) \in M)||(e (i,true) \in M).
  apply/orP;case:(boolP (e (i,false) \in M))=>hLeft;first by left.
  right;apply/negPn/negP=>hRight;apply:hNone;exists i;by split.
pose f (i:I):=e (i,if e (i,false) \in M then false else true).
have hFInjective:injective f.
  move=>i j hEqual;have hPair:=hInjective _ _ hEqual;exact:(congr1 fst hPair).
have hMember i:f i \in M `\` K.
  rewrite in_fsetD;apply/andP;split.
  - exact:(hEndpoints i _).2.
  - rewrite /f;case:(boolP (e (i,false) \in M))=>hLeft;first exact:hLeft.
    have /orP[hBad|hRight]:=hSome i;last exact:hRight.
    by move:hLeft;rewrite hBad.
pose G:=[fset f i|i:I].
have hSubset:{subset G<=M `\` K}.
  move=>x /imfsetP[i _ ->];exact:hMember.
have hCard:#|` G|=#|I| by rewrite /G card_imfset //= -cardE.
have hGSubset:G `<=` M `\` K by apply/fsubsetP.
have hBudget:=fsubset_leq_card hGSubset.
rewrite hCard in hBudget.
have hKSubset:K `<=` M by apply/fsubsetP.
have hDifference : #|` (M `\` K)| = (#|` M| - #|` K|)%N.
  by rewrite cardfsDS.
have hKCard:(#|` K|<=#|` M|)%N:=fsubset_leq_card hKSubset.
rewrite hDifference in hBudget.
have hTotal:(#|` K|+#|I|<=#|` M|)%N.
  apply:(leq_trans (leq_add (leqnn _) hBudget)).
  by rewrite subnKC.
by have hFalse:=leq_ltn_trans hTotal hCount;rewrite ltnn in hFalse.
Qed.
