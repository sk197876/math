(** Federer (1969), 4.1.7, p. 359:
    a Borel target restriction is contraction
    with its bounded Baire characteristic zero-form.
    The scalar extension is only a
    representative outside V; all assertions retain
    the original relative target and source domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground NormBoundedLinearTopology ScalarApproximateTargetTopology
  NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingZero AlternatingDual CurrentDomain CurrentCoefficientNorms CurrentZeroCovectorMaps
  CurrentFormPullbackOnDomain CurrentMapDifferential CurrentProperSupportDomain MetricSubsetBackground
  OpenSubspaceExtension TopologicalBorel CharacteristicFunctionUP CharacteristicFunctionSealed
  BaireFunctions BairePostcomposition BorelCharacteristicBaire.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentBorelZeroForm.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation Y := (R_n R n).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation YT := (real_norm_metric_space hNY).
Variable V:set Y.
Local Notation VT := (current_domain R n V).
Local Notation A := (A_m Y R^o 0).
Local Notation AN := (@current_form_comass R h2 n 0%N).
Local Notation hAN := (@current_form_comass_real_norm R h2 n 0%N).
Variable B:set VT.
Local Notation chi := (@CharacteristicFunction.value R VT B).
Local Notation hChi := (@CharacteristicFunction.laws R VT B).

(** Source for [current_borel_zero_form]: the
    original characteristic zero-form on V,
    supporting Federer 4.1.7, p. 359.
    Extension by zero only supplies an
    ambient representative of the given field. *)
Definition current_borel_zero_form:Y->A:=
  fun y=>@zero_form R Y R^o (@open_extension R YT V chi y).

(** Source for [current_borel_zero_form_values]:
    the original zero-form has the exact
    characteristic value at every point of V,
    supporting Federer 4.1.7, p. 359. *)
Lemma current_borel_zero_form_values (y:VT):
  current_borel_zero_form (set_val y)=@zero_form R Y R^o (chi y).
Proof. by rewrite /current_borel_zero_form (@open_extensionE R YT V chi y). Qed.

(** Source for [current_borel_zero_form_baire]: the
    characteristic zero-form of every original
    relative Borel subset is Baire,
    supporting Federer 4.1.7, p. 359,
    by 2.2.15, p. 71. *)
Theorem current_borel_zero_form_baire:
  borel_set B->@is_baire_function R VT (real_norm_metric_space hAN)
    (fun y:VT=>(current_borel_zero_form (set_val y):real_norm_metric_space hAN)).
Proof.
move=>hB.
have hZero:continuous (fun c:real_line_metric R=>(@zero_form R Y R^o c:real_norm_metric_space hAN)).
  have hBound:=@norm_bounded_linear_continuous R R^o A (fun c:R^o=>`|c|) AN
    (@scalar_absolute_value_norm R) hAN (@current_scalar_zero_form R n)
    (@current_scalar_zero_form_bounded R h2 n).
  move=>c;exact:(continuous_comp (@real_scalar_norm_identity_continuous R c) (hBound c)).
have hChar:=@borel_characteristic_baire R (metric_subset (V:set YT)) B chi hB hChi.
have hPost:=@baire_continuous_postcomposition R VT (real_line_metric R) (real_norm_metric_space hAN)
  (fun c=>@zero_form R Y R^o c) hZero chi hChar.
have hValues:(fun y:VT=>current_borel_zero_form (set_val y))=(fun y=>@zero_form R Y R^o (chi y)).
  apply:funext=>y;exact:current_borel_zero_form_values.
by rewrite hValues.
Qed.

(** Source for [current_borel_zero_form_bound]: the
    original Borel characteristic zero-form has
    comass at most one at every
    point of V, supporting Federer
    4.1.7, p. 359. *)
Theorem current_borel_zero_form_bound y:V y->AN (current_borel_zero_form y)<=1.
Proof.
move=>hy;pose z:VT:=exist _ y (mem_set hy).
change (AN (current_borel_zero_form (set_val z))<=1).
rewrite current_borel_zero_form_values.
change (AN (@current_scalar_zero_form R n (chi z))<=1).
rewrite (@current_zero_form_coefficient_norm R h2 n) (@current_scalar_zero_form_inverse R n).
case:(pselect (B z))=>hz.
- by rewrite (characteristic_on_set hChi hz) normr1.
- by rewrite (characteristic_off_set hChi hz) normr0.
Qed.

(** Source for [current_borel_zero_form_pullback]:
    the actual degree-zero pullback is the
    characteristic function of the original inverse
    image, supporting Federer 4.1.7, p. 359.
    Its value is independent of the
    particular differential of f. *)
Theorem current_borel_zero_form_pullback v (U:set (R_n R v)) (f:R_n R v->Y)
    (hImage:forall x,U x->V (f x)):
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R v)) hNY U f->
  forall x:current_domain R v U,
    @current_form_pullback_on_domain R v n 0%N U V f current_borel_zero_form x=
      @zero_form R (R_n R v) R^o (chi (@current_map_on_domain R v n U V f hImage x)).
Proof.
move=>hf x.
rewrite (@current_form_pullback_on_domain_actual R v n 0%N U V f current_borel_zero_form hImage hf x).
have hValues:=current_borel_zero_form_values (@current_map_on_domain R v n U V f hImage x).
change (current_borel_zero_form (f (set_val x))=
  @zero_form R Y R^o (chi (@current_map_on_domain R v n U V f hImage x))) in hValues.
rewrite hValues.
apply:form_ext=>t;by rewrite A_m_dualE !zero_formE.
Qed.
End CurrentBorelZeroForm.
