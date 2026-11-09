(** Federer (1969), 3.4.2(7), pp. 312–314: assemble compact
    pieces without changing their source or function class. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import GrassmannSubspaces GrassmannAbbreviations RealNormUP
  CountableDefaultEnumeration CriticalFlatPiecesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [critical_double_flat_cover]: the double sequence
    at the end of the proof of 3.4.2(7), p. 314, and the
    compact reduction on p. 312. Enumerate the pairs of natural
    indices. Every compact set and its associated manifold remain
    paired, and every original term occurs. *)
Lemma critical_double_flat_cover (R:realType) m d
    (Z:G (R_n R m) d) mu (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (S C A:set (R_n R m)) k (T G:nat->nat->set (R_n R m)):
  (forall i j,is_critical_flat_piece hNY Z mu S C k (T i j) (G i j)) ->
  A=\bigcup_i \bigcup_j G i j ->
  exists U K:nat->set (R_n R m),
    (forall n,is_critical_flat_piece hNY Z mu S C k (U n) (K n)) /\A=\bigcup_n K n.
Proof.
move=>hPieces hUnion.
have [u [_ hOnto]]:=@countable_default_enumeration
  [the choiceType of ((nat*nat)%type:Type)] setT (0%N,0%N) (countableP setT).
exists (fun n=>T (u n).1 (u n).2),(fun n=>G (u n).1 (u n).2).
split;first by move=>n;exact:hPieces.
apply/seteqP;split.
- move=>x hx;rewrite hUnion in hx;have [i _ [j _ hij]]:=hx.
  have [n hn]:=hOnto (i,j) I.
  exists n;first exact:I.
  by rewrite hn.
- move=>x [n _ hn];rewrite hUnion.
  exists (u n).1;first exact:I.
  by exists (u n).2.
Qed.

(** Source for [critical_two_flat_covers]: combine the common-set
    pieces and the pieces outside that set in 3.4.2(7),
    pp. 313–314. A sequence enumeration of the two tagged
    families preserves every original compact-manifold pair. *)
Lemma critical_two_flat_covers (R:realType) m d
    (Z:G (R_n R m) d) mu (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (S C A B:set (R_n R m)) k (TA GA TB GB:nat->set (R_n R m)):
  (forall n,is_critical_flat_piece hNY Z mu S C k (TA n) (GA n)) ->A=\bigcup_n GA n ->
  (forall n,is_critical_flat_piece hNY Z mu S C k (TB n) (GB n)) ->B=\bigcup_n GB n ->
  exists U K:nat->set (R_n R m),
    (forall n,is_critical_flat_piece hNY Z mu S C k (U n) (K n)) /\
    A `|` B=\bigcup_n K n.
Proof.
move=>hA hUnionA hB hUnionB.
have [u [_ hOnto]]:=@countable_default_enumeration
  [the choiceType of ((bool*nat)%type:Type)] setT (false,0%N) (countableP setT).
exists (fun n=>if (u n).1 then TA (u n).2 else TB (u n).2),
  (fun n=>if (u n).1 then GA (u n).2 else GB (u n).2).
split.
- move=>n;case:((u n).1);[exact:hA|exact:hB].
- apply/seteqP;split.
  + move=>x [hx|hx].
    * rewrite hUnionA in hx;have [i _ hi]:=hx.
      have [n hn]:=hOnto (true,i) I;exists n;first exact:I.
      by rewrite hn.
    * rewrite hUnionB in hx;have [i _ hi]:=hx.
      have [n hn]:=hOnto (false,i) I;exists n;first exact:I.
      by rewrite hn.
  + move=>x [n _ hn];case he:((u n).1) in hn.
    * left;rewrite hUnionA;by exists (u n).2.
    * right;rewrite hUnionB;by exists (u n).2.
Qed.
