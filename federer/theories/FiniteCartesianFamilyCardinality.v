(** Federer (1969), 3.3.20, pp. 306–308:
    finite Cartesian family cardinality for actual square levels. *)
From mathcomp Require Import all_boot finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.

(** Source for [finite_cartesian_family_cardinality]: the
    product of the two actual finite interval counts
    is the original square count, supporting 3.3.20,
    pp. 306–308. A proved finite subtype bijection
    gives the identity, including empty families. *)
Lemma finite_cartesian_family_cardinality (X Y:choiceType) (F:{fset X}) (G:{fset Y}):
  #|` (F `*` G)|=(#|` F| * #|` G|)%N.
Proof.
pose T:=[the finType of (F * G)%type].
pose f (p:T):X*Y:=(val p.1,val p.2).
have hInjective:injective f.
  move=>[a b] [c d] hEqual.
  have h1:=congr1 fst hEqual.
  have h2:=congr1 snd hEqual.
  have hAC:a=c:=val_inj h1.
  have hBD:b=d:=val_inj h2.
  by rewrite hAC hBD.
have hImage:[fset f p|p:T]=(F `*` G)%fset.
  apply/fsetP=>p;apply/idP/idP.
  - move=>/imfsetP[q _ ->];rewrite in_fsetM /f /=.
    apply/andP;split;exact:valP.
  - rewrite in_fsetM=>/andP[hFirst hSecond].
    apply/imfsetP;exists (Sub p.1 hFirst,Sub p.2 hSecond);first by [].
    by case:p hFirst hSecond.
rewrite -hImage card_imfset //= -cardE /T card_prod -!cardfE.
by [].
Qed.
