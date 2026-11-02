(** Federer (1969), 3.2.38, p. 274: split the finite parent
    family into cells meeting the good core and those missing it. *)
From mathcomp Require Import all_boot boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_core_family_split_exists]: supporting G and
    F minus G in Federer 3.2.38, p. 274. Finite subtypes keep
    the original parent cells through injective inclusions. Their
    union is exactly the original family union; each good cell has
    an actual core point and each bad cell is disjoint from the
    core. Either subfamily may be empty. No dummy point is selected. *)
Lemma finite_core_family_split_exists (X:Type) (I:finType) (Q:I->set X) (E:set X):
  exists (G B:finType) (good:G->I) (bad:B->I),
    [ /\injective good,injective bad,
      forall i,(Q (good i) `&` E)!=set0,
      forall i,(Q (bad i) `&` E)=set0 &
      (\bigcup_i Q i)=(\bigcup_i Q (good i)) `|` (\bigcup_i Q (bad i))].
Proof.
pose P:set I:=[set i|(Q i `&` E)!=set0].
pose G:=[the finType of set_type P].
pose B:=[the finType of set_type (~` P)].
exists G,B,(fun i:G=>val i),(fun i:B=>val i); split.
- exact:val_inj.
- exact:val_inj.
- move=>i; exact:set_valP i.
- move=>i; apply/seteqP; split=>[x hx|x []].
  exfalso; apply:(set_valP i); by exists x.
- apply/seteqP; split=>x.
  + move=>[i _ hx]; case:(pselect (P i))=>hP.
    * left; exists (exist _ i (mem_set hP):G)=>//.
    * right; exists (exist _ i (mem_set hP):B)=>//.
  + move=>[[i _ hx]|[i _ hx]]; by exists (val i).
Qed.
