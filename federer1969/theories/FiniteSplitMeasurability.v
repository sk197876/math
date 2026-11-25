(** Federer (1969), 2.1.4–5, p. 56: finite
    measurable hulls and regularity. This supporting
    criterion detects the missing source-measurability issue
    in the upper inequality of 3.2.27, pp. 262–263. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure MeasureNullRemainder
  RegularMeasureUP BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [regular_finite_split_measurable]: supporting
    consequence of the finite-hull and regularity laws in
    2.1.4–5, p. 56. Inside a finite measurable A,
    equality of the two outer masses in its split by E
    implies E measurable. This does not assert a null
    difference for a general nonmeasurable measure hull. *)
Lemma regular_finite_split_measurable (R:realType) (X:choiceType)
    (mu:set X->\bar R) (A E:set X):
  is_measure mu ->is_regular_measure mu ->measure_measurable mu A ->mu A < +oo ->
  E `<=` A ->mu A=mu E+mu (A `\` E) ->measure_measurable mu E.
Proof.
move=>hMu hRegular hA hFinite hEA hSplit.
have [B [hEB [hB hMass]]]:=hRegular E.
pose M:=A `&` B.
have hM:measure_measurable mu M:=measure_measurable_intersection hMu hA hB.
have hMA:M `<=` A by move=>x [hx _].
have hEM:E `<=` M by move=>x hx; split; [exact:hEA x hx|exact:hEB x hx].
have hEValue:mu E=mu M.
  apply/eqP; rewrite eq_le (measure_mono hMu hEM) /=.
  rewrite hMass; apply:(measure_mono hMu)=>x [_ hx]; exact hx.
have hAM:A `&` M=M.
  apply/seteqP; split; first by move=>x [_ hx].
  by move=>x hx; split; first exact:hMA x hx.
have hIntersection:(A `\` E) `&` M=M `\` E.
  apply/seteqP; split.
  - by move=>x [[_ hn] hx]; split.
  - move=>x [hx hn]; split; last exact hx; split; first exact:hMA x hx; exact hn.
have hDifference:(A `\` E) `\` M=A `\` M.
  apply/seteqP; split.
  - by move=>x [[hx _] hn]; split.
  - move=>x [hx hn]; split; last exact hn; split; first exact hx.
    move=>he; exact:hn (hEM x he).
have hASplit:mu A=mu M+mu (A `\` M) by have h:=hM A; rewrite hAM in h.
have hOther:mu (A `\` E)=mu (M `\` E)+mu (A `\` M).
  by have h:=hM (A `\` E); rewrite hIntersection hDifference in h.
have hSelf:mu A=mu A+mu (M `\` E).
  by rewrite {1}hSplit hEValue hOther addeA addeAC -hASplit.
have hFin:mu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hMu A)).
have hZero:mu (M `\` E)=0.
  have h:=congr1 (fun z=>z-mu A) hSelf.
  rewrite subee // addeAC subee // add0e in h; exact:esym h.
exact:(measurable_subset_null_remainder hMu hEM hM hZero).1.
Qed.

(** Source for [regular_nonmeasurable_split_strict]: local
    diagnostic for the upper inequality in 3.2.27,
    pp. 262–263. A nonmeasurable subset of a finite
    measurable set has strictly larger total outer split
    mass. This correction is not listed in the working erratum. *)
Lemma regular_nonmeasurable_split_strict (R:realType) (X:choiceType)
    (mu:set X->\bar R) (A E:set X):
  is_measure mu ->is_regular_measure mu ->measure_measurable mu A ->mu A < +oo ->
  E `<=` A ->~measure_measurable mu E ->mu A<mu E+mu (A `\` E).
Proof.
move=>hMu hRegular hA hFinite hEA hNot.
have hIntersection:A `&` E=E.
  apply/seteqP; split; first by move=>x [_ hx].
  by move=>x hx; split; first exact:hEA x hx.
have hBound:=MeasureSplit.measure_split_upper hMu A E.
rewrite hIntersection in hBound.
rewrite lt_neqAle hBound andbT.
apply/eqP=>hEquality; exact:hNot (regular_finite_split_measurable hMu hRegular hA hFinite hEA hEquality).
Qed.
