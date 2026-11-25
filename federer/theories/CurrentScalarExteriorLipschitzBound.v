(** Federer (1969), 4.1.12, p. 369: a smooth
    scalar cutoff with Lipschitz constant L has
    exterior derivative comass at most L. Reuse
    the original differential bound of 3.1.1,
    p. 209, and the literal degree-zero exterior
    formula of 4.1.6, p. 352. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormDifferentialLipschitzBound
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero
  CurrentSpaces CurrentCoefficientNorms CurrentFormInducedNorm CurrentZeroCovectorMaps
  SmoothCurrentExteriorDerivative ExteriorDifferentialUP ExteriorDifferentialNormBound
  AlternatingFormUnitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentScalarExteriorLipschitzBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable hFull:forall x:X,True->norm_domain_interior NX (fun _=>True) x.
Local Notation E := (@current_smooth_space R h2 n (fun _=>True) hFull 0%N).
Local Notation ev := (@current_smooth_value R h2 n (fun _=>True) hFull 0%N).
Local Notation NY := (@current_form_comass R h2 n 0%N).
Local Notation hNY := (@current_form_comass_real_norm R h2 n 0%N).
Local Notation coeff := (@current_zero_form_coefficient R n).
Local Notation d := (@smooth_current_exterior_derivative R h2 n 0%N (fun _=>True) hFull).

(** Source for [current_scalar_exterior_lipschitz_bound]:
    a smooth original scalar form with Lipschitz
    coefficient of constant L>=0 has |d phi|<=L
    at every original point, supporting the exact
    derivative constant in Federer 4.1.12, p. 369.
    The statement includes dimension zero. *)
Theorem current_scalar_exterior_lipschitz_bound (phi:E) L:
  0<=L->(forall x y,`|coeff (ev phi x)-coeff (ev phi y)|<=L*NX (x-y))->
  forall x,@current_form_comass R h2 n 1%N
    (@current_smooth_value R h2 n (fun _=>True) hFull 1%N (d phi) x)<=L.
Proof.
move=>hL hLipschitz x.
have[D [hD hExterior]]:=@smooth_current_exterior_derivative_actual R h2 n 0%N
  (fun _=>True) hFull phi x Logic.I.
have hFormLipschitz a b:NY (ev phi a-ev phi b)<=L*NX (a-b).
  rewrite current_zero_form_coefficient_norm (linB (hom_linear coeff));exact:hLipschitz a b.
have hDifferential:=@norm_differential_global_lipschitz_bound R X (A_m X R^o 0%N)
  NX NY hNX hNY (ev phi) x D L hD hFormLipschitz.
apply:(alternating_form_unit_tuple_least hNX (@scalar_absolute_value_norm R)
  (@current_form_comass_is_induced R h2 n 1%N _) hL)=>t hUnit.
rewrite hExterior exterior_differential_trace_tuple_values big_ord1 expr0 scale1r.
have hEmpty:exterior_omitted_tuple t ord0=[tuple]:=tuple0 _.
rewrite hEmpty.
have hNorm:`|(D (tnth t ord0)) [tuple]|=NY (D (tnth t ord0)).
  symmetry;exact:(@current_zero_form_coefficient_norm R h2 n (D (tnth t ord0))).
rewrite hNorm.
have hScale:=ler_wpM2l hL (hUnit ord0);rewrite mulr1 in hScale.
exact:le_trans (hDifferential (tnth t ord0)) hScale.
Qed.
End CurrentScalarExteriorLipschitzBound.
