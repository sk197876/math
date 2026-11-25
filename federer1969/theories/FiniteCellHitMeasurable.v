(** Federer (1969), 3.3.19, pp. 303–304:
    a set that contains or misses each whole actual
    finite cell is measurable for the original hit
    measure. This justifies the later coarse-disc sums;
    arbitrary-set additivity is neither assumed nor claimed. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal.
From Federer Require Import FiniteCellHitMeasureUP FiniteCellHitIndicesLaws MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_cell_hit_whole_cell_measurable]:
    supporting measurability of original coarse level discs
    for finer psi_n in the cyclic sum of
    3.3.19, p. 304. Each actual fine cell
    lies wholly on one side of the split; the
    exact finite hit counts therefore split additively. *)
Theorem finite_cell_hit_whole_cell_measurable (R:realType) (I X:choiceType)
    (F:{fset I}) (S:I->set X) (w:R) (mu:set X->\bar R) (P:set X):
  is_finite_cell_hit_measure F S w mu ->
  (forall i,i \in F ->S i `<=` P \/S i `&` P = set0) ->
  measure_measurable mu P.
Proof.
move=>hMu hCells T.
pose H:=finite_cell_hit_indices F S T.
pose A:=finite_cell_hit_indices F S (T `&` P).
pose B:=finite_cell_hit_indices F S (T `\` P).
have hUnion:H=(A `|` B)%fset.
  apply/fsetP=>i;rewrite in_fsetU;apply/idP/idP.
  - move=>/finite_cell_hit_indices_membership[hi [x [hxS hxT]]].
    apply/orP;case:(pselect (P x))=>hxP.
    + left;apply/finite_cell_hit_indices_membership;split=>//;exists x;by split.
    + right;apply/finite_cell_hit_indices_membership;split=>//;exists x;by split.
  - move=>/orP[/finite_cell_hit_indices_membership[hi [x [hxS [hxT hxP]]]]|
      /finite_cell_hit_indices_membership[hi [x [hxS [hxT hxP]]]]];
      apply/finite_cell_hit_indices_membership;split=>//;exists x;by split.
have hIntersection:(A `&` B)%fset=fset0.
  apply/fsetP=>i;rewrite in_fsetI in_fset0;apply/negP=>/andP[hA hB].
  have [hi [x [hxS [_ hxP]]]]:=(@finite_cell_hit_indices_membership I X F S (T `&` P) i).1 hA.
  have [_ [y [hyS [_ hyP]]]]:=(@finite_cell_hit_indices_membership I X F S (T `\` P) i).1 hB.
  case:(hCells i hi)=>[hInside|hDisjoint].
  - exact:hyP (hInside y hyS).
  - have hFalse:(S i `&` P) x by split.
    by rewrite hDisjoint in hFalse.
have hCard:(#|` H|=#|` A|+#|` B|)%N by rewrite hUnion cardfsU hIntersection cardfs0 subn0.
rewrite !hMu.
change ((#|` H|%:R*w)%R%:E=(#|` A|%:R*w)%R%:E+(#|` B|%:R*w)%R%:E).
by rewrite hCard natrD mulrDl EFinD.
Qed.
