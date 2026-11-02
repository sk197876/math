(** Federer (1969), 1.10.5, p. 48, the mass infimum. The infimum is a
    seminorm for every input seminorm. These laws precede the duality and
    positive-definiteness arguments; neither is assumed here. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP SymmetricAlgebra SymmetricGrading
  SymmetricDecompositions SymmetricDecompositionCosts SymmetricProjectiveMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Laws.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.

(** Source for [symmetric_projective_mass_triangle]: Federer 1.10.5, p. 48,
    supporting triangle inequality. Concatenate decompositions whose costs
    are each within half of an arbitrary positive error. *)
Theorem symmetric_projective_mass_triangle m (hm : (0<m)%N)
    (x y : symmetric_power V m) :
  symmetric_projective_mass hN hm (x+y) <=
    symmetric_projective_mass hN hm x + symmetric_projective_mass hN hm y.
Proof.
apply/ler_addgt0Pr=> eps he.
have hh : 0 < eps/2 by rewrite divr_gt0 // ltr0n.
have [s [hs hcs]] := symmetric_projective_mass_approximate hN hm x hh.
have [t [ht hct]] := symmetric_projective_mass_approximate hN hm y hh.
have hd := symmetric_decomposition_add hs ht.
have hb := symmetric_projective_mass_cost_bound hN hm hd.
rewrite symmetric_decomposition_cost_cat in hb.
apply: le_trans hb _; apply: ltW.
have hc := ltrD hcs hct; by rewrite addrACA -splitr in hc.
Qed.

(** Source for [symmetric_projective_mass_scale_le]: Federer 1.10.5,
    p. 48, supporting one-sided absolute homogeneity. Scaling the
    first factor of every product bounds the new infimum by the old
    one times the absolute scalar, including the zero scalar. *)
Lemma symmetric_projective_mass_scale_le m (hm : (0<m)%N) c (x : symmetric_power V m) :
  symmetric_projective_mass hN hm (c *: x) <= `|c| * symmetric_projective_mass hN hm x.
Proof.
case: m hm x=> [|m] hm x //.
case: (eqVneq c 0)=> [->|hc].
- by rewrite scale0r symmetric_projective_mass_zero normr0 mul0r.
have hp : 0 < `|c| by rewrite normr_gt0.
rewrite mulrC -(ler_pdivrMr _ _ hp).
apply: symmetric_projective_mass_greatest=> s hs.
rewrite (ler_pdivrMr _ _ hp) mulrC.
have hd := symmetric_decomposition_scale c hs.
have hh := symmetric_projective_mass_cost_bound hN hm hd.
by rewrite (symmetric_decomposition_cost_scale_first hN) in hh.
Qed.

(** Source for [symmetric_projective_mass_scale]: Federer 1.10.5,
    p. 48, absolute homogeneity of the infimum seminorm. The
    reverse inequality follows by scaling back by the inverse scalar. *)
Theorem symmetric_projective_mass_scale m (hm : (0<m)%N) c (x : symmetric_power V m) :
  symmetric_projective_mass hN hm (c *: x) = `|c| * symmetric_projective_mass hN hm x.
Proof.
case: (eqVneq c 0)=> [->|hc].
- by rewrite scale0r symmetric_projective_mass_zero normr0 mul0r.
apply/eqP; rewrite eq_le; apply/andP; split; first exact: symmetric_projective_mass_scale_le.
have hh := symmetric_projective_mass_scale_le hm c^-1 (c *: x).
rewrite scalerA mulVf // scale1r normfV in hh.
have hb := ler_wpM2l (normr_ge0 c) hh.
by rewrite mulrA mulfV ?normr_eq0 // mul1r in hb.
Qed.

(** Source for [symmetric_projective_mass_seminorm]: Federer 1.10.5, p. 48.
    The positive-degree mass infimum obeys all three real-valued seminorm
    laws in arbitrary dimension. *)
Theorem symmetric_projective_mass_seminorm m (hm : (0<m)%N) :
  is_real_seminorm (symmetric_projective_mass hN hm).
Proof.
constructor.
- exact: symmetric_projective_mass_nonnegative.
- exact: symmetric_projective_mass_scale.
- exact: symmetric_projective_mass_triangle.
Qed.
End Laws.
