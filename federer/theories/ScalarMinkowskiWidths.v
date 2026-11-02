(** Scalar endpoint estimates supporting convexity under Steiner
    symmetrisation in Federer (1969), 2.10.30, p. 195. Nonnegative weighted
    sums of two sections give weighted sums of their infima and suprema as
    bounds for the containing section. Extrema need not be attained. This
    expands the book's brief convexity assertion rather than assuming a
    Brunn–Minkowski theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring lra.
From Federer Require Import ScalarConvexSectionLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_minkowski_endpoint_bounds]: supporting
    endpoint estimates for the convex normal sections
    of 2.10.30, p. 195. The containing set
    is only required to have finite order bounds. *)
Lemma scalar_minkowski_endpoint_bounds (R : realType) (A B C : set R) (a b : R) :
  A !=set0 -> B !=set0 -> has_lbound C -> has_ubound C ->
  0<=a -> 0<=b -> (forall x y, A x -> B y -> C (a*x+b*y)) ->
  inf C<=a*inf A+b*inf B /\ a*sup A+b*sup B<=sup C.
Proof.
move=> hA hB hlo hhi ha hb hmap.
have [x hx] := hA; have [y hy] := hB.
have hC : C !=set0 by exists (a*x+b*y); exact: hmap.
have hupper y0 : B y0 -> a*sup A+b*y0<=sup C.
  move=> hy0.
  have hpoint x0 : A x0 -> a*x0<=sup C-b*y0.
    move=> hx0; have hh := sup_upper_bound (conj hC hhi) (hmap x0 y0 hx0 hy0); lra.
  have hh := nonnegative_multiple_supremum_bound hA ha hpoint; lra.
have hlower y0 : B y0 -> inf C<=a*inf A+b*y0.
  move=> hy0.
  have hpoint x0 : A x0 -> inf C-b*y0<=a*x0.
    move=> hx0; have hh := ge_inf hlo (hmap x0 y0 hx0 hy0); lra.
  have hh := nonnegative_multiple_infimum_bound hA ha hpoint; lra.
split.
- have hpoint y0 : B y0 -> inf C-a*inf A<=b*y0.
    move=> hy0; have hh := hlower y0 hy0; lra.
  have hh := nonnegative_multiple_infimum_bound hB hb hpoint; lra.
- have hpoint y0 : B y0 -> b*y0<=sup C-a*sup A.
    move=> hy0; have hh := hupper y0 hy0; lra.
  have hh := nonnegative_multiple_supremum_bound hB hb hpoint; lra.
Qed.

(** Source for [scalar_minkowski_width_bound]: supporting
    concavity of section width for the convexity
    conclusion in 2.10.30, p. 195. This
    purely scalar estimate uses no measure construction. *)
Theorem scalar_minkowski_width_bound (R : realType) (A B C : set R) (a b : R) :
  A !=set0 -> B !=set0 -> has_lbound C -> has_ubound C ->
  0<=a -> 0<=b -> (forall x y, A x -> B y -> C (a*x+b*y)) ->
  a*(sup A-inf A)+b*(sup B-inf B)<=sup C-inf C.
Proof.
move=> hA hB hlo hhi ha hb hmap.
have [hl hu] := scalar_minkowski_endpoint_bounds hA hB hlo hhi ha hb hmap.
have he : a*(sup A-inf A)+b*(sup B-inf B)=
    (a*sup A+b*sup B)-(a*inf A+b*inf B) by ring.
rewrite he; exact: lerB hu hl.
Qed.
