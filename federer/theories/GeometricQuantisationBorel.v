(** Federer (1969), proof of 2.4.4(2), p. 83: the scalar geometric
    approximant is Borel and countably valued. These facts follow from its
    abstract cell laws alone. Source context: GeometricQuantisationUP.v. The
    narrow num_normedtype import supplies real order-ray topology, as in
    RealIntegerCells.v. *)
From mathcomp Require Import all_boot all_order all_algebra ssrint boolp classical_sets cardinality
  reals topology num_normedtype.
From Federer Require Import RealMetricBackground GeometricQuantisationUP GeometricQuantisationLaws
  BorelFunctionUP CountableRangeBorelFunction TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [geometric_quantisation_level]: enumeration of
    zero and the integer-power values of the step approximant
    in Federer 2.4.4(2), p. 83. *)
Definition geometric_quantisation_level (R : realType) (t : R) (i : option int) : R :=
  if i is Some j then t^j else 0.

(** Source for [geometric_quantisation_range_countable]: countable
    range of the geometric approximant in Federer 2.4.4(2), p. 83. *)
Lemma geometric_quantisation_range_countable (R : realType) (t : R) (q : R -> R) :
  is_geometric_quantisation t q -> countable (q @` setT).
Proof.
move=> hq; have hs : q @` setT `<=` geometric_quantisation_level t @` setT.
  move=> y [x _ <-]; have [hx|hx] := leP x 0.
  - exists None=> //; exact: esym (hq.1 x hx).
  - have [j [_ [_ he]]] := hq.2 x hx; exists (Some j)=> //; exact: esym he.
apply: sub_countable (subset_card_le hs) _.
apply: sub_countable (card_image_le _ _) _; exact: countableP.
Qed.

(** Source for [geometric_quantisation_fibre_borel]: the fibres
    of the approximant in Federer 2.4.4(2), p. 83,
    are the specified half-open cells, the nonpositive half-line,
    or the empty set. *)
Lemma geometric_quantisation_fibre_borel (R : realType) (t : R) (q : real_line_metric R -> real_line_metric R) :
  1 < t -> is_geometric_quantisation t q -> forall y,
  borel_set (q @^-1` [set y]).
Proof.
move=> ht hq y; have [hy|hy] := eqVneq y 0.
- have he : q @^-1` [set y] = [set x : real_line_metric R | x<=0].
    apply/seteqP; split=> x; rewrite hy=> hx.
    + apply: (geometric_quantisation_zero_fibre ht hq x).1; exact hx.
    + exact ((geometric_quantisation_zero_fibre ht hq x).2 hx).
  rewrite he; apply: closed_borel_set; exact: closed_le.
- have [hj|hj] := pselect (exists j : int, y=t^j).
  + have [j hjvalue] := hj.
    have he : q @^-1` [set y] = [set x : real_line_metric R | t^j<=x /\ x<t^(j+1)].
      apply/seteqP; split=> x hx.
      * apply: (geometric_quantisation_positive_fibre ht hq x j).1; by rewrite hx hjvalue.
      * have hh := (geometric_quantisation_positive_fibre ht hq x j).2 hx.
        change (q x=y); by rewrite hjvalue hh.
    rewrite he; apply: (borel_family_binary_intersection (borel_sets_family [the topologicalType of real_line_metric R])).
    * apply: closed_borel_set; exact: closed_ge.
    * apply: open_borel_set; exact: open_lt.
  + have he : q @^-1` [set y] = set0.
      apply/seteqP; split=> x; last by case.
      move=> hyx; have [hx|hx] := leP x 0.
      * have hz := hq.1 x hx; apply: (negP hy); apply/eqP; by rewrite -hyx hz.
      * have [j [_ [_ he]]] := hq.2 x hx; apply: hj; exists j; by rewrite -hyx he.
    rewrite he; apply: open_borel_set; exact: open0.
Qed.

(** Source for [geometric_quantisation_borel]: Borel property
    of the scalar step approximant in Federer 2.4.4(2), p. 83,
    used to compose it with the given measurable function. *)
Theorem geometric_quantisation_borel (R : realType) (t : R) (q : real_line_metric R -> real_line_metric R) :
  1 < t -> is_geometric_quantisation t q -> is_borel_function q.
Proof.
move=> ht hq; apply: countable_range_borel_function.
- exact: geometric_quantisation_range_countable hq.
- exact: geometric_quantisation_fibre_borel ht hq.
Qed.
