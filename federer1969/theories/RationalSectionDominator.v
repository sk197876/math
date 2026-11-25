(** Federer (1969), 2.6.3(2), p. 118: the two displayed bounds and the
    inverse-square integral imply absolute integrability of each section
    with y>0. We exhibit a summable majorant, assembled from a unit-interval
    characteristic function and the proved inverse-square tail. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype lra.
From Federer Require Import RealMetricBackground MeasureUP MeasureIntegralUP MeasureSubsetIntegral
  SummableRealFunctionUP SummableRealArithmetic CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureCharacteristicIntegral BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions
  LebesgueScalarMeasure RealSubsetIntegralGraph InverseSquareTailIntegral RationalFubiniKernel RationalKernelBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rational_positive_section_dominator]: supporting summable
    majorant proving the finiteness of integral |f(x,y)| for y>0 in Federer
    2.6.3(2), p. 118 The majorant's actual integral is (4y+1+y^2)(y^-4+1). *)
Theorem rational_positive_section_dominator (R : realType) (y : R) :
  0 < y -> exists H : R -> R,
    is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand H)
      ((4*y+1+y^+2)*(y^-1)^+4+(4*y+1+y^+2))%:E /\
    (forall x, 0 <= H x) /\ (forall x, `|rational_fubini_kernel x y| <= H x).
Proof.
move=> hy; pose C := 4*y+1+y^+2; pose c := C*(y^-1)^+4.
pose s := @CharacteristicFunction.value R R `[0,1].
have hs := @CharacteristicFunction.laws R R `[0,1].
pose u (x : R) := if 1 <= x then (x^-1)^+2 else 0.
pose H (x : R) := c*s x+C*u x.
have hC : 0 <= C by rewrite /C !addr_ge0 ?mulr_ge0 ?sqr_ge0 //; exact: ltW hy.
have hc : 0 <= c.
  apply: mulr_ge0 hC _; by rewrite exprn_ge0 // invr_ge0; exact: ltW hy.
have hs0 x : 0 <= s x.
  case: (pselect (`[0,1] x))=> hx.
  - by rewrite /s (@characteristic_on_set R R _ _ hs x hx) ler01.
  - by rewrite /s (@characteristic_off_set R R _ _ hs x hx) lexx.
have hu0 x : 0 <= u x by rewrite /u; case: ifP=> _; [exact: sqr_ge0 | exact: lexx].
have hH0 x : 0 <= H x by rewrite /H addr_ge0 //; exact: mulr_ge0.
have hA : measure_measurable (@lebesgue_scalar_measure R) `[0,1].
  apply: (borel_regular_borel_measurable (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
  apply: closed_borel_set; exact: segment_closed_real.
have hsi : is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand s) 1%:E.
  have hi := @measure_characteristic_integral R R _ (lebesgue_scalar_is_measure R) `[0,1] s hs hA.
  by rewrite lebesgue_scalar_segment ?ler01 // subr0 in hi.
have hui : is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand u) 1%:E.
  apply: ((@real_subset_integral_total R R _ [set x : R | 1 <= x]
    (fun x => (x^-1)^+2) u 1%:E _ _).1 (@inverse_square_lebesgue_tail R)).
  - by move=> x hx; rewrite /u hx.
  - move=> x hx; have hn : ~~ (1 <= x) by apply/negP.
    by rewrite /u (negPf hn).
have hci := @real_total_integral_scale R R _ (lebesgue_scalar_is_measure R) s 1 c hsi.
have hCi := @real_total_integral_scale R R _ (lebesgue_scalar_is_measure R) u 1 C hui.
rewrite mulr1 in hci.
rewrite mulr1 in hCi.
have hHi := @real_total_integral_add R R _ (lebesgue_scalar_is_measure R) _ _ c C hci hCi.
exists H; split=> //; split=> // x.
case: (lerP x 0)=> hx.
- rewrite rational_fubini_kernel_nonpositive_left // normr0; exact: hH0.
- case: (lerP x 1)=> hx1.
  + have hxA : `[0,1] x by rewrite /= in_itv /= (ltW hx) hx1.
    have hb := rational_kernel_small_bound hy (ltW hx) hx1.
    apply: le_trans hb _; rewrite /H /s (@characteristic_on_set R R _ _ hs x hxA) mulr1.
    change (c <= c+C*u x).
    rewrite lerDl; exact: mulr_ge0 hC (hu0 x).
  + have hb := rational_kernel_large_bound hy (ltW hx1).
    apply: le_trans hb _; rewrite /H /u (ltW hx1) /=.
    change (C*(x^-1)^+2 <= c*s x+C*(x^-1)^+2).
    rewrite lerDr; exact: mulr_ge0 hc (hs0 x).
Qed.
