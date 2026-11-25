(** Federer (1969), 3.2.18, p. 255:
    turn a countable disjoint family of
    compact chart images into the printed
    sequence. Use the proved unique partial
    enumeration, with empty compact slots for
    finite or empty families. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  CountablyClosedFamilyUP CountablePartialEnumeration RectifiableCompactChartsUP
  RectifiableCompactChartLaws HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_chart_family_enumeration]:
    the sequence K_i,psi_i in Federer
    3.2.18, p. 255. Each active
    compact image occurs once, so the
    enumerated images remain pairwise disjoint.
    Empty slots have empty parameter domain. *)
Theorem rectifiable_chart_family_enumeration (R : realType) m n (lambda : R)
    (W : set (R_n R n)) (G : set (set (R_n R n))) :
  0<=lambda -> countable G -> set_family_disjoint G ->
  (forall C, G C -> @is_rectifiable_chart_piece R m n lambda W C) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
    (W `\` (\bigcup_(C in G) C))=0%E ->
  exists (K : nat -> set (R_n R m)) (psi : nat -> R_n R m -> R_n R n),
    is_rectifiable_compact_chart_cover lambda W K psi.
Proof.
move=> hLam hCount hDis hPiece hNull.
have [eta hEta] := countable_partial_enumeration_exists hCount.
pose C i := if eta i is Some A then A else set0.
have hex i : exists (K : set (R_n R m)) (psi : R_n R m -> R_n R n),
    is_uniform_compact_rectifiable_chart lambda K psi /\ C i=psi @` K /\ psi @` K `<=` W.
  case he : (eta i)=> [A|].
  - have hA := @partial_enumeration_members [the choiceType of set (R_n R n)] G eta hEta i A he.
    have [hAW [K [psi [hChart hImage]]]] := hPiece A hA.
    exists K,psi; split=> //; split; first by rewrite /C he.
    by rewrite -hImage.
  - exists set0,(fun _ : R_n R m=>(0 : R_n R n)); split.
    + exact: empty_uniform_compact_chart hLam.
    + have hImage : ((fun _ : R_n R m=>(0 : R_n R n)) @` set0)=set0.
        apply/seteqP; split=> y; [by move=> [x []]|by move=> []].
      rewrite hImage /C he; split=> //; by move=> y [].
have [K hK] := choice hex.
have [psi hPsi] := choice hK.
have hImage i : psi i @` K i=C i := esym (hPsi i).2.1.
have hUnion : (\bigcup_i psi i @` K i)=(\bigcup_(A in G) A).
  apply/seteqP; split=> y.
  - move=> [i _ hy]; rewrite hImage /C in hy.
    case he : (eta i) hy=> [A|] hy; last by case: hy.
    exists A=> //; exact: (@partial_enumeration_members [the choiceType of set (R_n R n)] G eta hEta i A he).
  - move=> [A hA hy].
    have [i hi] := @partial_enumeration_cover [the choiceType of set (R_n R n)] G eta hEta A hA.
    exists i=> //; by rewrite hImage /C hi.
exists K,psi; split; first by move=> i; split; [exact (hPsi i).1|exact (hPsi i).2.2].
split; last by rewrite hUnion.
move=> i j hNe y hyi hyj.
rewrite !hImage /C in hyi hyj.
case hi : (eta i) hyi=> [A|] hyi; last by case: hyi.
case hj : (eta j) hyj=> [B|] hyj; last by case: hyj.
have hA := @partial_enumeration_members [the choiceType of set (R_n R n)] G eta hEta i A hi.
have hB := @partial_enumeration_members [the choiceType of set (R_n R n)] G eta hEta j B hj.
have hAB : A<>B.
  move=> heq; rewrite -heq in hj.
  have he := @partial_enumeration_unique [the choiceType of set (R_n R n)] G eta hEta i j A hi hj.
  by move: hNe; rewrite he eqxx.
have hEmpty := hDis A B hA hB hAB.
have hBoth : (A `&` B) y by split.
by rewrite hEmpty in hBoth.
Qed.
