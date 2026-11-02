(** Private proof of the printed smooth
    cutoff in Federer (1969), 3.1.11,
    p. 223. Its formula uses the
    already sealed flat exponential; all public
    uses go through ScalarUnitCutoffSealed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra.
From Federer Require Import FlatExponentialUP FlatExponentialSealed FlatExponentialOrder
  ScalarSmoothSequenceUP ScalarSmoothSequenceArithmetic
  ScalarSmoothCompositionSealed ScalarUnitCutoffUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_unit_cutoff_exists]:
    the second displayed function on Federer
    3.1.11, p. 223, is a
    nonincreasing smooth unit cutoff. Its
    denominator f(f(1)) is proved positive
    before it is cancelled. *)
Theorem scalar_unit_cutoff_exists (R : realType) :
  exists g : R->R,
    (forall x, g x=
      FlatExponential.value (FlatExponential.value 1-FlatExponential.value x)/
        FlatExponential.value (FlatExponential.value (1:R))) /\
    is_scalar_unit_cutoff g /\
    exists G : nat->R->R, is_scalar_smooth_derivative_sequence g G.
Proof.
pose f := @FlatExponential.value R.
pose c := f 1.
pose d := f c.
pose g x := f (c-f x)/d.
have hc : 0<c by rewrite /c /f flat_exponential_positive.
have hd : 0<d by rewrite /d /f flat_exponential_positive.
have hd0 : d!= 0 by rewrite gt_eqF.
have hdi : 0<=d^-1 by rewrite invr_ge0; exact: ltW hd.
exists g; split; first by move=>x.
split.
- constructor.
  + move=>x hx; rewrite /g /f (flat_exponential_nonpositive_value
      (@FlatExponential.laws R) hx) subr0.
    change (d/d= 1); exact: divff hd0.
  + move=>x hx.
    have hfx : c<=f x := flat_exponential_nondecreasing hx.
    have hn : c-f x<= 0 by rewrite subr_le0.
    rewrite /g /f (flat_exponential_nonpositive_value
      (@FlatExponential.laws R) hn).
    exact: mul0r.
  + move=>x y hxy.
    have hfx : f x<=f y := flat_exponential_nondecreasing hxy.
    have harg : c-f y<=c-f x by rewrite lerD2l lerN2.
    have hnum : f (c-f y)<=f (c-f x) := flat_exponential_nondecreasing harg.
    exact (ler_wpM2r hdi hnum).
  + move=>x; apply/andP; split.
    * exact (mulr_ge0 (flat_exponential_nonnegative _) hdi).
    * rewrite /g ler_pdivrMr // mul1r.
      apply: flat_exponential_nondecreasing.
      have hn : 0<=f x := flat_exponential_nonnegative x; lra.
- have [F [hF hzero]] := @FlatExponential.smooth_derivatives R.
  have [G hG] := scalar_smooth_affine_derivatives_exists c (-1) hF.
  have [H hH] := ScalarSmoothComposition.derivatives hF hG.
  have hs := scalar_smooth_sequence_scale d^-1 hH.
  have he : (fun x=>d^-1*f (c+(-1)*f x))=g.
    apply: funext=>x; by rewrite mulN1r /g mulrC.
  rewrite he in hs.
  by exists (fun k x=>d^-1*H k x).
Qed.
