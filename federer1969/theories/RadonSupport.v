(** Federer (1969), 2.2.5, pp. 62-63: the complement of the support has
    measure zero for a Radon measure. Federer's erratum p. 1 corrects book
    p. 63 line 2 to "finitely many open sets". Source context:
    RadonMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum
  NonnegativeSumSupport MeasureSupport CompactFiniteCover RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_in_null_open_union]: Federer 2.2.5, p. 63,
    supporting step: every compact subset of a union of open null sets is
    null, because it has a finite subcover. This step needs only the measure
    laws, not Radon regularity. *)
Lemma compact_in_null_open_union (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) K : compact K ->
  K `<=` \bigcup_(U in [set U | open U /\ mu U = 0]) U -> mu K = 0.
Proof.
move=> hK hc; have [D hD hcover] := @compact_open_finite_cover T _
  [set U | open U /\ mu U = 0] (fun U => U) K hK (fun U hU => hU.1) hc.
have hb := @measure_indexed_cover R T _ mu hm K [set` D] (fun U => U)
  (finite_set_countable (finite_fset D)) hcover.
have hs : nonnegative_sum [set` D] mu = 0.
  apply: nonnegative_sum_zero=> U hU.
  have hd : U \in D by exact hU.
  have hu := hD U hd; move: hu; rewrite inE=> hu; exact: hu.2.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
by rewrite hs in hb.
Qed.

(** Source for [radon_support_complement_null]: Federer 2.2.5, pp. 62-63,
    displayed claim and proof: the complement of the support is open; all
    its compact subsets are null by finite subcovers, and inner regularity
    makes the whole complement null. *)
Theorem radon_support_complement_null (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_radon_measure mu) : mu (~` measure_support mu) = 0.
Proof.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
apply: (@radon_inner_least R T mu hr (~` measure_support mu) (closed_openC (@measure_support_closed R T mu)) 0)=> K hK hKS.
have hnull : mu K = 0.
  apply: (@compact_in_null_open_union R T mu hm K hK).
  by rewrite measure_support_formula setCK in hKS.
by rewrite hnull.
Qed.
