(** Centred scalar-section convex combinations supporting Federer (1969),
    2.10.30, p. 195. Convex scalar sections have their actual interval
    widths as Lebesgue lengths. Endpoint bounds then show that centring
    preserves weighted section inclusions. This is a supporting proof of the
    printed convexity assertion, with no compactness assumption. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring lra.
From Federer Require Import RealMetricBackground InnerConvex CoveringFamilyUP
  CenteredSectionUP CenteredSectionLaws ScalarConvexSectionLength ScalarMinkowskiWidths LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [centered_section_minkowski_inclusion]: supporting
    normal-line convexity estimate for 2.10.30,
    p. 195. Open-ended convex sections and zero
    coefficients are included; the centred replacements
    retain closed endpoints. *)
Theorem centered_section_minkowski_inclusion (R : realType)
    (A B C A' B' C' : set (real_line_metric R)) (a b : R) :
  is_centered_section A A' -> is_centered_section B B' -> is_centered_section C C' ->
  @is_inner_convex R R^o A -> @is_inner_convex R R^o B -> @is_inner_convex R R^o C ->
  metric_set_bounded A -> metric_set_bounded B -> metric_set_bounded C ->
  0<=a -> 0<=b -> (forall x y, A x -> B y -> C (a*x+b*y)) ->
  forall x y, A' x -> B' y -> C' (a*x+b*y).
Proof.
move=> hA hB hC hAc hBc hCc hAb hBb hCb ha hb hmap x y hx hy.
have hA' : A' !=set0 by exists x.
have hB' : B' !=set0 by exists y.
have hneA := (centered_section_support_law hA).2 hA'.
have hneB := (centered_section_support_law hB).2 hB'.
have [z hz] := hneA; have [w hw] := hneB.
have hneC : C !=set0 by exists (a*z+b*w); exact: hmap.
have [r [hr [hAr hAm]]] := centered_section_membership hA hneA.
have [s [hs [hBs hBm]]] := centered_section_membership hB hneB.
have [v [hv [hCv hCm]]] := centered_section_membership hC hneC.
have hwidthA : sup A-inf A=r+r.
  have hh := scalar_convex_section_length hAc hneA hAb.
  rewrite hAr in hh.
  have he : r+r=sup A-inf A by move/eqP: hh; rewrite eqe=> /eqP.
  exact (esym he).
have hwidthB : sup B-inf B=s+s.
  have hh := scalar_convex_section_length hBc hneB hBb.
  rewrite hBs in hh.
  have he : s+s=sup B-inf B by move/eqP: hh; rewrite eqe=> /eqP.
  exact (esym he).
have hwidthC : sup C-inf C=v+v.
  have hh := scalar_convex_section_length hCc hneC hCb.
  rewrite hCv in hh.
  have he : v+v=sup C-inf C by move/eqP: hh; rewrite eqe=> /eqP.
  exact (esym he).
have [hlo hhi] := bounded_scalar_order_bounds hCb.
have hh := scalar_minkowski_width_bound hneA hneB hlo hhi ha hb hmap.
rewrite hwidthA hwidthB hwidthC !mulrDr in hh.
have hrad : a*r+b*s<=v by lra.
have hnx := (hAm x).1 hx; have hny := (hBm y).1 hy.
have hnorm : `|a*x+b*y|<=a*r+b*s.
  apply: le_trans (ler_normD _ _) _.
  rewrite !normrM (ger0_norm ha) (ger0_norm hb).
  exact: lerD (ler_wpM2l ha hnx) (ler_wpM2l hb hny).
apply: (hCm _).2; exact: le_trans hnorm hrad.
Qed.
