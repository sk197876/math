(** Federer (1969), 3.3.20, p. 308: finite first-split alternatives. *)
From mathcomp Require Import all_boot finmap boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.

(** Source for [finite_family_no_two_singleton]: supporting first-split
    reduction in 3.3.20, p. 308. A nonempty actual finite family
    without two distinct members is a singleton. *)
Lemma finite_family_no_two_singleton (I:choiceType) (F:{fset I}):
  F!=fset0 ->~(exists i j,i \in F /\j \in F /\i!=j) ->
  exists i,F=[fset i].
Proof.
move=>/fset0Pn[i hi] hNo.
exists i;apply/fsetP=>j;rewrite in_fset1.
case:(eqVneq j i)=>[->|hDifferent].
- by rewrite ?eqxx ?hi.
- have hNot:j \notin F.
    apply/negP=>hj;apply:hNo;exists j,i;split;first exact:hj.
    split;[exact:hi|exact:hDifferent].
  by rewrite (negPf hNot).
Qed.
