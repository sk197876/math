(** Federer (1969), 3.3.19, p. 303: existence
    and outer-measure laws for the independently specified
    finite weighted cell-hit values. Component hits are
    only local witnesses. No additivity on arbitrary sets
    or Borel regularity is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets
  cardinality constructive_ereal.
From Federer Require Import FiniteCellHitMeasureUP MeasureUP MeasureSum NonnegativeSum
  NonnegativeSumSupport NonnegativeSumGrouping.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_cell_hit_measure_exists]: the
    original weighted hit-count formula actually defines
    an outer measure, as asserted in 3.3.19, p. 303.
    Each local one-cell hit is an outer measure;
    their finite sum is identified with the literal
    cardinal formula using the existing numerical-sum laws. *)
Theorem finite_cell_hit_measure_exists (R:realType) (I X:choiceType)
    (F:{fset I}) (S:I->set X) (w:R):
  (0<=w)%R ->exists mu:set X->\bar R,
    is_finite_cell_hit_measure F S w mu /\is_measure mu.
Proof.
move=>hw.
pose c:=fun i:I=>fun T:set X=>if `[<S i `&` T!=set0>] then w%:E else 0.
have hComponent i:is_measure (c i).
  constructor.
  - move=>T;rewrite /c;case:ifP=>_;first by rewrite lee_fin;exact hw.
    exact:lexx.
  - move=>T C hC hCover;rewrite /c.
    case:asboolP=>[hHit|hMiss];last exact:nonnegative_sum_nonnegative.
    have [x [hxS hxT]]:=hHit.
    have [B hB hxB]:=hCover x hxT.
    have hHitB:S i `&` B!=set0 by exists x;split.
    have hValue:c i B=w%:E by rewrite /c (asboolT hHitB).
    have hTerm:=@nonnegative_sum_term R [the choiceType of set X] C (c i) B hB.
    by rewrite hValue in hTerm.
have [mu hSum]:=@measure_sum_exists R X I [set` F] c.
have hMeasure:=@measure_sum_is_measure R X I [set` F] c mu (fun i _=>hComponent i) hSum.
exists mu;split;last exact hMeasure.
move=>T;rewrite hSum /c nonnegative_sum_predicate.
pose G:=finite_cell_hit_indices F S T.
have hIndices:([set` F] `&` [set i | `[< S i `&` T!=set0 >]])=[set` G].
  apply/seteqP;split.
  - move=>i [hi hHit];change (is_true (i \in G));rewrite /G /finite_cell_hit_indices in_fset /= !inE.
    by rewrite hi hHit.
  - move=>i hi;change (is_true (i \in G)) in hi.
    have /andP[hF hHit]:(i \in F) && `[<S i `&` T!=set0>].
      by move:hi;rewrite /G /finite_cell_hit_indices in_fset /= !inE.
    by split.
rewrite hIndices nonnegative_sum_finite;last by move=>i _;rewrite lee_fin.
by rewrite sumEFin big_seq_fsetE sumr_const cardT cardfE mulr_natl cardE.
Qed.

(** Source for [finite_cell_hit_measure_is_measure]: every
    object with the independent original hit-count laws is
    an outer measure, supporting psi_n in 3.3.19,
    p. 303. Existence and uniqueness discharge the
    laws without exposing the local component construction. *)
Theorem finite_cell_hit_measure_is_measure (R:realType) (I X:choiceType)
    (F:{fset I}) (S:I->set X) (w:R) (mu:set X->\bar R):
  (0<=w)%R ->is_finite_cell_hit_measure F S w mu ->is_measure mu.
Proof.
move=>hw hMu;have [nu [hNu hMeasure]]:=@finite_cell_hit_measure_exists R I X F S w hw.
have hEqual:=@finite_cell_hit_measure_unique R I X F S w mu nu hMu hNu.
by rewrite hEqual.
Qed.
