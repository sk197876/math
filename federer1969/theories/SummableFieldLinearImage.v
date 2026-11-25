(** Federer (1969), 4.1.19, p. 377: bounded
    linear coefficient maps act on the actual
    raw L1 carriers. The field values
    determine the map and retain the original
    bound. Only existence is asserted here;
    no selected implementation is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric MeasureUP
  VectorDaniellHypotheses MeasureLpNorm MeasureLpMembershipUP
  SummableFieldSealed SummableFieldLaws SummableFieldIntegral
  SummableFieldRepresentation TotalLoneLinearImage.
From Federer Require Import PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [summable_field_linear_image_exists]:
    the bounded coefficient maps used for the
    L1 duality in Federer 4.1.19, p. 377,
    are linear on the original raw representatives.
    The old bounded-linear integral estimate and
    exact representative laws supply existence, without
    quotienting by almost equality. *)
Theorem summable_field_linear_image_exists
    (R : realType) (X : topologicalType) (A B : lmodType R)
    (NA : A -> R) (NB : B -> R)
    (hNA : is_real_norm NA) (hNB : is_real_norm NB)
    (hSep : is_separable_normed_space hNB)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (L : Hom A B) (c : R) (hC : 0 <= c)
    (hBound : forall v, NB (L v) <= c*NA v) :
  exists J : Hom (@SummableField.space R X A NA hNA mu hm)
      (@SummableField.space R X B NB hNB mu hm),
    (forall w x,
      @summable_field_value R X B NB hNB mu hm (J w) x =
        L (@summable_field_value R X A NA hNA mu hm w x)) /\
    forall w, @summable_field_size R X B NB hNB mu hm (J w) <=
      c*@summable_field_size R X A NA hNA mu hm w.
Proof.
pose WA := @SummableField.space R X A NA hNA mu hm.
pose WB := @SummableField.space R X B NB hNB mu hm.
pose va := @summable_field_value R X A NA hNA mu hm.
pose vb := @summable_field_value R X B NB hNB mu hm.
have hImage (w : WA) : exists z : WB,
    vb z = (fun x => L (va w x)).
  have [hMember hCap] := @total_lone_bounded_linear_image R X A B NA NB
    hNA hNB hSep mu hm L c hC hBound (va w)
    (@summable_field_lone R X A NA hNA mu hm w).
  have [z [hValue hSize]] := @summable_total_field_representative R X B NB
    hNB mu hm (fun x => (L (va w x) : real_norm_metric_space hNB)) hMember.
  by exists z.
pose j (w : WA) : WB := projT1 (cid (@hImage w)).
have hValue (w : WA) : vb (j w) = (fun x => L (va w x)).
  exact: (projT2 (cid (@hImage w))).
have hLinear : linear j.
  move=> a u v; apply: (@summable_field_value_injective R X B NB hNB mu hm).
  change (vb (j (a*:u+v))=vb (a*:j u+j v)).
  rewrite hValue /va /vb (@summable_field_value_add R X A NA hNA mu hm)
    (@summable_field_value_scale R X A NA hNA mu hm)
    (@summable_field_value_add R X B NB hNB mu hm)
    (@summable_field_value_scale R X B NB hNB mu hm).
  have hJU := @hValue u; have hJV := @hValue v.
  rewrite /vb in hJU hJV; rewrite hJU hJV.
  apply: funext=> x; exact: (hom_linear L a (va u x) (va v x)).
exists (@HomMap R WA WB j (introT (asboolP _) hLinear)); split.
- move=> w x.
  have hPoint := congr1 (fun f : X -> B => f x) (@hValue w).
  exact hPoint.
- move=> w.
  have [hMember hCap] := @total_lone_bounded_linear_image R X A B NA NB
    hNA hNB hSep mu hm L c hC hBound (va w)
    (@summable_field_lone R X A NA hNA mu hm w).
  have hSource : @summable_field_size R X A NA hNA mu hm w =
      fine (measure_lp_norm mu NA 1 (partial_function_total (va w))).
    have hLP : measure_lp_norm mu NA 1 (partial_function_total (va w))=
        (@summable_field_size R X A NA hNA mu hm w)%:E.
      exact: (esym (@summable_field_size_exact R X A NA hNA mu hm w)).
    by rewrite hLP.
  have hTarget : @summable_field_size R X B NB hNB mu hm (j w) =
      fine (measure_lp_norm mu NB 1
        (partial_function_total (fun x => L (va w x)))).
    rewrite -(hValue w).
    have hLP : measure_lp_norm mu NB 1 (partial_function_total (vb (j w)))=
        (@summable_field_size R X B NB hNB mu hm (j w))%:E.
      exact: (esym (@summable_field_size_exact R X B NB hNB mu hm (j w))).
    by rewrite hLP.
  by rewrite hSource hTarget.
Qed.

(** Source for [summable_scalar_orbit_map_exists]:
    the original scalar component f y lies
    in the full L1 coefficient space,
    supporting Federer 4.1.19, p. 377.
    Its bound retains the exact coefficient norm
    N(y), including y zero and zero functions. *)
Theorem summable_scalar_orbit_map_exists
    (R : realType) (X : topologicalType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (hSep : is_separable_normed_space hN)
    (mu : set X -> \bar R) (hm : is_measure mu) (y : V) :
  exists J : Hom
      (@SummableField.space R X R^o
        (fun t : R => `|t|%R) (scalar_absolute_value_norm R) mu hm)
      (@SummableField.space R X V N hN mu hm),
    (forall f x, @summable_field_value R X V N hN mu hm (J f) x =
      @summable_field_value R X R^o (fun t : R => `|t|%R)
        (scalar_absolute_value_norm R) mu hm f x*:y) /\
    forall f, @summable_field_size R X V N hN mu hm (J f) <=
      N y*@summable_field_size R X R^o (fun t : R => `|t|%R)
        (scalar_absolute_value_norm R) mu hm f.
Proof.
have hLinear : linear (fun s : R^o => s*:y).
  move=> a s t; change ((a*s+t)*:y = a*:(s*:y)+t*:y).
  by rewrite scalerDl scalerA.
pose L := @HomMap R R^o V (fun s => s*:y)
  (introT (asboolP _) hLinear).
have hY : 0 <= N y := real_seminorm_nonnegative hN.1 y.
have hOrbit (s : R^o) : N (L s) <= N y*`|s|.
  change (is_true (N (s*:y) <= N y*`|s|)).
  by rewrite (real_seminorm_scale hN.1) mulrC.
exact: (@summable_field_linear_image_exists R X R^o V
  (fun s : R => `|s|%R) N (scalar_absolute_value_norm R) hN hSep mu hm
  L (N y) hY hOrbit).
Qed.
