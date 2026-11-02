(** Federer (1969), 3.2.3, p. 243: construct a
    Borel partition of A subordinate to its countable Borel
    cover. The proof expands the disjointification already
    established in 2.2.1, p. 60. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import TopologicalBorel BorelFamilyBasic BorelPartition
  CountablyClosedFamilyUP SetSequenceDisjointification CountableFamilyEnumeration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_countable_cover_subordinate_partition]:
    the partition H in Federer 3.2.3, p. 243.
    Empty covers and empty A are included; every partition
    member is contained in an actual original cover member. *)
Theorem borel_countable_cover_subordinate_partition (X:topologicalType)
    (A:set X) (G:set (set X)):
  borel_set A -> countable G -> (forall E,G E -> borel_set E) ->
  A `<=` \bigcup_(E in G) E -> exists H,is_borel_partition A H /\
    forall B,H B -> B `<=` A /\ exists E,G E /\ B `<=` E.
Proof.
move=>hA hG hB hCover.
case:(pselect (exists E,G E))=>[hNonempty|hEmpty].
- have [E hE]:=countable_nonempty_family_enumeration (fun E:set X=>E) hG hNonempty.
  have hMember n:G (E n).
    have hn:(E @` setT) (E n) by exists n.
    rewrite hE in hn; by have [B hB' <-]:=hn.
  have hEb n:borel_set (E n):=hB (E n) (hMember n).
  pose P n:=A `&` set_sequence_disjointify E n.
  pose H:=P @` setT.
  have hPb n:borel_set (P n).
    apply:(borel_family_binary_intersection (borel_sets_family X) hA).
    apply:borel_set_difference; first exact (hEb n).
    apply:borel_set_countable_union; first exact:countableP.
    by move=>j _; exact (hEb j).
  have hPunion:(\bigcup_n P n)=A.
    apply/seteqP; split=>x.
    + by move=>[n _ [hx _]].
    + move=>hx.
      have hEx:(\bigcup_n E n) x.
        have [B hBG hBx]:=hCover x hx.
        have hb:((fun C:set X=>C) @` G) B by exists B.
        rewrite -hE in hb; have [n _ hn]:=hb; exists n=>//; by rewrite hn.
      rewrite -set_sequence_disjointify_union in hEx.
      have [n _ hn]:=hEx; exists n=>//; by split.
  exists H; split.
  + constructor.
    * exact (sub_countable (card_image_le P setT) (countableP _)).
    * move=>B C [i _ <-] [j _ <-] hNe.
      apply/seteqP; split=>x; last by case.
      move=>[[ha hi] [ha' hj]]; exfalso.
      have hij:i!=j.
        apply/negP=>/eqP he; subst j; exact (hNe (erefl _)).
      exact (@set_sequence_disjointify_disjoint X E i j hij x hi hj).
    * by move=>B [i _ <-]; exact (hPb i).
    * have he:(\bigcup_(B in H) B)=\bigcup_n P n.
        apply/seteqP; split=>x.
        - by move=>[B [i _ <-] hx]; exists i.
        - by move=>[i _ hx]; exists (P i); first by exists i.
      by rewrite he.
  + move=>B [i _ <-]; split; first by move=>x [hx _].
    exists (E i); split; first exact (hMember i).
    by move=>x [_ [hx _]].
- have hAz:A=set0.
    apply/seteqP; split=>x; last by case.
    move=>hx; have [E hEG _]:=hCover x hx; exfalso; apply:hEmpty; by exists E.
  rewrite hAz; exists set0; split; first exact:borel_partition_empty.
  by move=>B hB0; case:hB0.
Qed.
