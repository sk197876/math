(** Federer (1969), 4.1.12, p. 367: the
    original exact scalar-multiplier estimate on currents,
    with compact index K intersect spt gamma.
    Retain Federer's ordinary partial multiplication:
    zero times infinity is not silently defined. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces SmoothCompactSet
  SmoothFunctionSupport SmoothTestSpaces CurrentSupportGeometry SmoothCompactSupportIntersection
  CurrentContraction CurrentTestFormProduct CurrentFlatNorm CurrentFlatFormSeminormLaws
  CurrentFlatDualSeminormSealed CurrentFlatDualSeminormBasic CurrentFlatScalarTestProductBound
  ExtendedRealPartial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatMultiplier.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation E0 := (@current_smooth_space R h2 n U hU 0%N).
Local Notation sv0 := (@current_smooth_value R h2 n U hU 0%N).
Local Notation hE0 := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation inc0 := (smooth_test_inclusion hE0).
Variable gamma:@current_test_space R h2 n U hU 0%N.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation coefficient := (@current_flat_scalar_coefficient R h2 n U hU K (inc0 gamma)).
Local Notation contract := (@current_contraction R h2 n 0%N m U hU (inc0 gamma)).
Local Notation product := (@current_test_form_product R h2 n 0%N m U hU (inc0 gamma)).

(** Source for [current_flat_multiplier_compact]: the
    original compact K intersect spt gamma in the
    multiplier estimate of Federer 4.1.12, p. 367.
    This is the preceding literal set-intersection index. *)
Definition current_flat_multiplier_compact:smooth_compact_set hNX U:=
  @smooth_compact_support_intersection R X (A_m X R^o 0%N) E0 NX hNX U sv0 K (inc0 gamma).
Local Notation L := current_flat_multiplier_compact.
Local Notation LF := (@current_flat_norm R h2 n m U hU L).

(** Source for [current_flat_multiplier_compact_carrier]:
    the output compact is exactly K intersect the
    original support of gamma, Federer 4.1.12,
    p. 367. Use the public intersection identity. *)
Lemma current_flat_multiplier_compact_carrier:
  smooth_compact_carrier L=smooth_compact_carrier K `&` @current_test_support R h2 n 0%N U hU gamma.
Proof.
exact:(@smooth_compact_support_intersection_carrier R X (A_m X R^o 0%N) E0 NX hNX U sv0
  K (inc0 gamma)).
Qed.

(** Source for [current_flat_multiplier_finite_bound]:
    the original exact multiplier estimate when F_K(T)
    is finite, Federer 4.1.12, p. 367. The
    coefficient and compact index remain precisely those
    printed; a zero coefficient is allowed. *)
Theorem current_flat_multiplier_finite_bound (T:C) a:
  F T=a%:E->(LF (contract T)<=(coefficient * a)%:E)%E.
Proof.
move=>hValue.
have ha:=@current_flat_dual_nonnegative R h2 n m U hU K (action T).
change (is_true (0<=F T)%E) in ha;rewrite hValue lee_fin in ha.
have hCoefficient:=@current_flat_scalar_coefficient_nonnegative R h2 n U hU K (inc0 gamma).
have hL:smooth_compact_carrier L=smooth_compact_carrier K `&`
    @smooth_function_support R X (A_m X R^o 0%N) NX hNX U E0 sv0 (inc0 gamma).
  exact:current_flat_multiplier_compact_carrier.
apply:(@current_flat_dual_upper_from_bound R h2 n m U hU L (action (contract T))
  (coefficient*a) (mulr_ge0 hCoefficient ha))=>phi.
rewrite current_contraction_evaluation.
apply:(le_trans (@current_flat_dual_finite_bound R h2 n m U hU K (action T) a hValue (product phi))).
have h:=ler_wpM2l ha (@current_flat_scalar_test_product_bound R h2 n m U hU
  K L (inc0 gamma) hL phi).
by rewrite mulrA [a*coefficient]mulrC in h.
Qed.

(** Source for [current_flat_multiplier_bound]: the
    original F_(K intersect spt gamma)(T contracted
    gamma) <= [nu_K^0(gamma)+nu_K^0(d gamma)] F_K(T),
    Federer 4.1.12, p. 367. The ordinary product
    retains its original domain; infinite flat values
    are included whenever that product is defined. *)
Theorem current_flat_multiplier_bound (T:C):
  mule_def coefficient%:E (F T)->(LF (contract T)<=coefficient%:E * F T)%E.
Proof.
move=>hDefined.
case:(ltP (F T) (+oo)%E)=>hFinite.
- have [a [ha hValue]]:=@current_flat_dual_finite_value R h2 n m U hU K (action T) hFinite.
  have hCurrentValue:F T=a%:E:=hValue.
  rewrite hCurrentValue -EFinM.
  exact:current_flat_multiplier_finite_bound hCurrentValue.
- have hInfinite:F T=(+oo)%E.
    apply/eqP;rewrite eq_le;apply/andP;split;first exact:leey.
    exact:hFinite.
  have hNonzero:coefficient!=0 by move:hDefined;rewrite hInfinite /mule_def.
  have hCoefficient:=@current_flat_scalar_coefficient_nonnegative R h2 n U hU K (inc0 gamma).
  have hPositive:0<coefficient by rewrite lt0r hNonzero hCoefficient.
  have hPositiveExtended:(0<coefficient%:E)%E by rewrite lte_fin.
  rewrite hInfinite (gt0_muley hPositiveExtended);exact:leey.
Qed.

(** Source for [current_flat_multiplier_partial_bound]:
    the same original inequality with its right-hand
    side expressed by Federer's partial product graph,
    supporting 4.1.12, p. 367. No value is
    assigned to the excluded zero-times-infinity case. *)
Theorem current_flat_multiplier_partial_bound (T:C) b:
  extended_multiply coefficient%:E (F T)=Some b->(LF (contract T)<=b)%E.
Proof.
rewrite /extended_multiply.
case hDefined:(mule_def coefficient%:E (F T))=>//hValue.
have hProduct:(coefficient%:E * F T)%E=b by injection hValue.
rewrite -hProduct;exact:current_flat_multiplier_bound hDefined.
Qed.
End CurrentFlatMultiplier.
