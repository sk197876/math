(** Federer (1969), 3.4.8(2), p. 326:
    the actual zero ideal has no positive directional
    witness, and its depth is the prescribed n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermRing
  AnalyticGermJetZeroNegate AnalyticReductionLociUP AnalyticReductionActual
  AnalyticRotatedGermIdeal AnalyticReductionDepthUP AnalyticReductionDepthLaws AnalyticDepthSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ZeroIdeal.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=(@analytic_germ_ring R X NX hNX 0).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation I0:=([set alpha:G|alpha = 0]).

(** Source for [analytic_rotated_zero_ideal]: actual
    orthogonal pullback preserves the zero ideal,
    supporting depth({0}) in 3.4.8(2), p. 326. *)
Lemma analytic_rotated_zero_ideal (g:O) (alpha:G):
  @analytic_rotated_germ_ideal R X B hB n e he I0 g alpha <->alpha = 0.
Proof.
rewrite analytic_rotated_germ_ideal_membership;split.
- move=>[beta [hBeta <-]];by rewrite hBeta rmorph0.
- move=>->;exists 0;split=>//;exact:rmorph0.
Qed.

(** Source for [analytic_reduction_zero_B_empty]: the
    original positive-order derivative test fails for
    the actual zero ideal, 3.4.8(2), p. 326. *)
Lemma analytic_reduction_zero_B_empty j (g:O):
  ~@analytic_reduction_actual_B R X B hB n e he omega I0 j g.
Proof.
have hLaws:=@analytic_reduction_actual_laws R X B hB n e he omega I0.
move/(analytic_reduction_B_membership hLaws j g)=>[alpha [hAlpha [hQ [k [hK hJet]]]]].
have hZero:alpha = 0 by exact:(analytic_rotated_zero_ideal g alpha).1 hAlpha.
apply:hJet;rewrite hZero analytic_germ_jet_zero;exact:linear0.
Qed.

(** Source for [analytic_depth_zero_ideal]: the original
    special convention depth({0})=n follows from the
    same finite-minimum laws, 3.4.8(2), p. 326. *)
Lemma analytic_depth_zero_ideal:@AnalyticDepth.value R X B hB n e he omega I0 = n.
Proof.
exact:(analytic_reduction_depth_empty_family analytic_reduction_zero_B_empty
  (@AnalyticDepth.laws R X B hB n e he omega I0)).
Qed.
End ZeroIdeal.
