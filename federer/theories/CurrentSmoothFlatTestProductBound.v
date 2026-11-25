(** Federer (1969), 4.1.17, p. 374: smooth coefficient
    contraction preserves the original fixed-compact flat class.
    This supporting test estimate uses the actual exterior product,
    the graded Leibniz rule of 4.1.7, p. 356, and the original
    compact flat seminorm of 4.1.12, p. 367. Only a finite
    coefficient bound is needed; no sharp constant one is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom ScalarCoefficients TensorUP RealNormUP
  NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingProduct
  CurrentSpaces CurrentCoefficientNorms CurrentFormWedgeBound
  SmoothCompactSet SmoothTestSpaces SmoothFunctionTopology
  SmoothDerivativeSeminormUP SmoothDerivativeSeminormLaws
  CurrentTestFormProduct CurrentTestValueLaws
  CurrentTestExteriorDerivative CurrentTestExteriorLeibniz CurrentTestDegreeComass
  SmoothCurrentExteriorDerivative CurrentFlatFormSeminormLaws
  CurrentFlatTestPointBounds CurrentCompactZerothBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CurrentSmoothFlatTestProductBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation E d := (@current_smooth_space R h2 n U hU d).
Local Notation DT d := (@current_test_space R h2 n U hU d).
Local Notation sv d := (@current_smooth_value R h2 n U hU d).
Local Notation tv d := (@current_test_value R h2 n U hU d).
Local Notation hE d := (@current_smooth_space_laws R h2 n U hU d).
Local Notation inc d := (smooth_test_inclusion (hE d)).
Local Notation hD d := (@current_smooth_derivative_laws R h2 n U hU d).
Local Notation nu d := (smooth_function_derivative_seminorm (hD d)).
Local Notation N d := (@current_form_comass R h2 n d).
Local Notation hN d := (@current_form_comass_real_norm R h2 n d).
Local Notation sd d := (@smooth_current_exterior_derivative R h2 n d U hU).
Local Notation td d := (@current_test_exterior_derivative R h2 n d U hU).
Local Notation P a b := (@current_test_form_product R h2 n a b U hU).
Local Notation Flat d := (@current_flat_test_seminorm R h2 n d U hU K).

(** Source for [current_smooth_flat_test_product_bound]: multiplying
    an original compact test by a fixed smooth k-form has a finite
    F_K bound in the original degrees k+p, supporting Federer
    4.1.17, p. 374. The constant depends only on that coefficient,
    its exterior derivative on K and the existing finite wedge
    bounds. Both degrees and the compact set may be zero or empty. *)
Theorem current_smooth_flat_test_product_bound (gamma:E k):
  exists c:R,0<=c /\forall psi:DT p,
    Flat (k+p) (P k p gamma psi)<=c*Flat p psi.
Proof.
have[c0 [h0 hBound0]]:=(@current_form_wedge_bounded R h2 n k p).2.
have[c1 [h1 hBound1]]:=(@current_form_wedge_bounded R h2 n k.+1 p).2.
have[c2 [h2Bound hBound2]]:=(@current_form_wedge_bounded R h2 n k p.+1).2.
pose a:=nu k K 0%N gamma.
pose b:=nu k.+1 K 0%N (sd k gamma).
have ha:0<=a:=smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws (hD k) K 0%N) gamma.
have hb:0<=b:=smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws (hD k.+1) K 0%N) (sd k gamma).
pose c:=c0*a+(c1*b+c2*a).
have hFirstNonnegative:0<=c0*a:=mulr_ge0 h0 ha.
have hRestNonnegative:0<=c1*b+c2*a:=
  addr_ge0 (mulr_ge0 h1 hb) (mulr_ge0 h2Bound ha).
have hc:0<=c:=addr_ge0 hFirstNonnegative hRestNonnegative.
have hFirst:c0*a<=c.
  have h:=lerD (lexx (c0*a)) hRestNonnegative.
  by rewrite addr0 in h.
have hRest:c1*b+c2*a<=c.
  have h:=lerD hFirstNonnegative (lexx (c1*b+c2*a)).
  by rewrite add0r in h.
exists c;split;first exact:hc.
move=>psi;pose f:=Flat p psi.
have hf:0<=f:=real_seminorm_nonnegative
  (@current_flat_test_is_seminorm R h2 n p U hU K) psi.
have hPoint x:smooth_compact_carrier K x->
    N (k+p) (tv (k+p) (P k p gamma psi) x)<=c*f /\
    N (k+p).+1 (tv (k+p).+1
      (td (k+p) (P k p gamma psi)) x)<=c*f.
  move=>hx;have hUx:=smooth_compact_in_domain K x hx.
  have hGamma:=@current_compact_zeroth_point_bound R h2 n k U hU K gamma x hx.
  have hDgamma:=@current_compact_zeroth_point_bound R h2 n k.+1 U hU K
    (sd k gamma) x hx.
  have hPsi:=@current_flat_test_point_bound R h2 n p U hU K psi x hx.
  have hDpsi:=@current_flat_test_derivative_point_bound R h2 n p U hU K psi x hx.
  have hA:=real_seminorm_nonnegative (hN k).1 (sv k gamma x).
  have hDA:=real_seminorm_nonnegative (hN k.+1).1 (sv k.+1 (sd k gamma) x).
  have hB:=real_seminorm_nonnegative (hN p).1 (tv p psi x).
  have hDB:=real_seminorm_nonnegative (hN p.+1).1 (tv p.+1 (td p psi) x).
  have hProduct0:
      N (k+p) (tv (k+p) (P k p gamma psi) x)<=(c0*a)*f.
    rewrite (@current_test_form_product_values R h2 n k p U hU gamma psi x hUx).
    apply:(le_trans (hBound0 (sv k gamma x) (tv p psi x))).
    rewrite -mulrA.
    exact:(ler_wpM2l h0 (ler_pM hA hB hGamma hPsi)).
  split.
  - exact:(le_trans hProduct0 (ler_wpM2r hf hFirst)).
  - rewrite (@current_test_exterior_leibniz R h2 n k p U hU gamma psi)
      current_test_add_value current_test_scale_value.
    apply:(le_trans (real_seminorm_triangle (hN (k+p).+1).1 _ _)).
    rewrite (real_seminorm_scale (hN (k+p).+1).1)
      normrX normrN normr1 expr1n mul1r !current_test_degree_transport_comass.
    have hProduct1:
        N (k.+1+p) (tv (k.+1+p) (P k.+1 p (sd k gamma) psi) x)<=
          (c1*b)*f.
      rewrite (@current_test_form_product_values R h2 n k.+1 p U hU
        (sd k gamma) psi x hUx).
      apply:(le_trans (hBound1 (sv k.+1 (sd k gamma) x) (tv p psi x))).
      rewrite -mulrA.
      exact:(ler_wpM2l h1 (ler_pM hDA hB hDgamma hPsi)).
    have hProduct2:
        N (k+p.+1) (tv (k+p.+1) (P k p.+1 gamma (td p psi)) x)<=
          (c2*a)*f.
      rewrite (@current_test_form_product_values R h2 n k p.+1 U hU
        gamma (td p psi) x hUx).
      apply:(le_trans (hBound2 (sv k gamma x) (tv p.+1 (td p psi) x))).
      rewrite -mulrA.
      exact:(ler_wpM2l h2Bound (ler_pM hA hDB hGamma hDpsi)).
    apply:(le_trans (lerD hProduct1 hProduct2)).
    rewrite -mulrDl.
    exact (ler_wpM2r hf hRest).
rewrite /current_flat_test_seminorm current_flat_form_seminorm_formula
  -(@current_test_exterior_derivative_inclusion R h2 n (k+p) U hU
    (P k p gamma psi)) ge_max.
apply/andP;split.
- apply:(@current_compact_zeroth_least_bound R h2 n (k+p) U hU K
    (inc (k+p) (P k p gamma psi)) (c*f) (mulr_ge0 hc hf))=>x hx.
  exact:(hPoint x hx).1.
- apply:(@current_compact_zeroth_least_bound R h2 n (k+p).+1 U hU K
    (inc (k+p).+1 (td (k+p) (P k p gamma psi))) (c*f)
    (mulr_ge0 hc hf))=>x hx.
  exact:(hPoint x hx).2.
Qed.
End CurrentSmoothFlatTestProductBound.
