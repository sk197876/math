(** Federer (1969), 2.1.5, p. 57, third irregular example. Use the corrected
    formula from Federer's May 1987 erratum, erratum p. 1, book p. 57 line
    26: card(A), not card(S), for A contained in S. The three points are
    None, Some false, Some true; S consists of the latter two. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumProduct NonnegativeSumBoolean
  CountingMeasure MeasureUP MeasureBasic BoundedNonemptyMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [two_point_support]: Federer 2.1.5, p. 57,
    third example's set S of two points, concretely the Some values. *)
Definition two_point_support : set (option bool) := [set x | x != None].

(** Source for [two_point_support_counting]: Federer 2.1.5,
    p. 57, third example's hypothesis card(S)=2; counting is 2.1.2,
    p. 54. Reindexing along Some gives the two-point count. *)
Lemma two_point_support_counting (R : realType) :
  counting_measure (R := R) two_point_support = (2 : R)%:E.
Proof.
have he : two_point_support = Some @` (@setT bool).
  apply/seteqP; split.
  - move=> [b|] hx; first by exists b.
    by move: hx; rewrite /two_point_support /=.
  - move=> x [b _ <-]; by [].
rewrite counting_measure_sum he nonnegative_sum_injective_image.
- rewrite nonnegative_sum_bool; first by rewrite -EFinD.
  by move=> b; rewrite lee_fin ler01.
- by move=> a b _ _ [].
- by move=> b _; rewrite lee_fin ler01.
Qed.

(** Source for [two_point_restriction_measure]: Federer 2.1.5,
    p. 57, third example, corrected by erratum p. 1, book p. 57
    line 26. A set avoiding None lies in S and has its cardinality
    as value; any set containing None has value two. *)
Definition two_point_restriction_measure (R : realType) (A : set (option bool)) : \bar R :=
  if None \in A then (2 : R)%:E else counting_measure (R := R) A.
Arguments two_point_restriction_measure {R} A.

(** Source for [two_point_restriction_measure_inside]: Federer
    2.1.5, p. 57, corrected cardinality formula for A contained in S;
    erratum p. 1, book p. 57 line 26. *)
Lemma two_point_restriction_measure_inside (R : realType) (A : set (option bool)) :
  A `<=` two_point_support -> two_point_restriction_measure (R := R) A = counting_measure (R := R) A.
Proof.
move=> hA; rewrite /two_point_restriction_measure; case: ifP=> // /set_mem hn.
have h := hA None hn; by rewrite /two_point_support /= in h.
Qed.

(** Source for [two_point_restriction_measure_outside]: Federer
    2.1.5, p. 57, third example's value two for sets not contained in S. *)
Lemma two_point_restriction_measure_outside (R : realType) (A : set (option bool)) :
  ~ A `<=` two_point_support -> two_point_restriction_measure (R := R) A = (2 : R)%:E.
Proof.
move=> hn; rewrite /two_point_restriction_measure; case: ifP=> // ha.
exfalso; apply: hn=> x hx; apply/eqP=> he.
have hN : A None by rewrite -he.
by move: ha; rewrite (mem_set hN).
Qed.

(** Source for [two_point_restriction_measure_is_measure]: Federer
    2.1.5, p. 57, verification of the corrected third example.
    It is monotone and lies between one and two on nonempty sets. *)
Lemma two_point_restriction_measure_is_measure (R : realType) :
  is_measure (@two_point_restriction_measure R).
Proof.
have hcount : is_measure (fun A : set (option bool) => counting_measure (R := R) A).
  exact: (@counting_measure_is_measure R _).
have hsub (A : set (option bool)) : None \notin A -> A `<=` two_point_support.
  move=> hn x hx; apply/eqP=> he; by move: hn; rewrite -he (mem_set hx).
have hbound (A : set (option bool)) : None \notin A -> counting_measure (R := R) A <= (2 : R)%:E.
  move=> hn; rewrite -two_point_support_counting.
  exact: (@measure_mono R _ _ hcount A two_point_support (hsub A hn)).
apply: bounded_nonempty_is_measure.
- rewrite /two_point_restriction_measure in_set0.
  exact: (@measure_empty R _ _ hcount).
- move=> A B hAB; rewrite /two_point_restriction_measure.
  case: ifP=> ha; case: ifP=> hb; first exact: lexx.
  + have h := hAB None (set_mem ha); by move: hb; rewrite (mem_set h).
  + apply: hbound; by rewrite ha.
  + exact: (@measure_mono R _ _ hcount A B hAB).
- move=> A hA; rewrite /two_point_restriction_measure; case: ifP=> _.
  + by rewrite lee_fin ler1n.
  + have [x hx] := proj1 (set0P A) hA; rewrite counting_measure_sum.
    exact: (@nonnegative_sum_term R _ A (fun _ => (1 : R)%:E) x hx).
- move=> A; rewrite /two_point_restriction_measure; case: ifP=> ha; first exact: lexx.
  apply: hbound; by rewrite ha.
Qed.
