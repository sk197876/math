(** Federer (1969), 3.4.12, p. 338:
    a bounded complex linear map is holomorphic on
    every open original domain. Apply the real analytic
    linear-map theorem and actual differential uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed
  RealNormUP NormDifferentialUP NormDifferentialLinear NormDifferentialDirectional
  NormAnalyticLinear HolomorphicUP ComplexRealLinearMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_hom_real]: the same complex
    linear map considered over the underlying real spaces,
    used in the original differential condition of 3.4.12,
    p. 338. This adapter uses only scalar restriction. *)
Definition complex_hom_real (R:realFieldType)
    (X Y:lmodType (ComplexScalars.C R)) (L:Hom X Y):
  Hom (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) Y):=
  hom_of_linear (restrict_linear (ComplexScalars.embed R) (hom_as_linear L)).

(** Source for [complex_hom_real_values]: scalar restriction
    changes no value of the original map, supporting
    3.4.12, p. 338. *)
Lemma complex_hom_real_values (R:realFieldType)
    (X Y:lmodType (ComplexScalars.C R)) (L:Hom X Y) x:
  complex_hom_real L x=L x.
Proof. by []. Qed.

(** Source for [holomorphic_bounded_linear]: the original
    analytic linear maps of 3.1.24, p. 240,
    with the complex first-differential condition of 3.4.12,
    p. 338. Boundedness and domain openness remain explicit. *)
Theorem holomorphic_bounded_linear (R:realType)
    (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm (fun x:restricted_space (ComplexScalars.embed R) X=>NX x))
    (hNY:is_real_norm (fun y:restricted_space (ComplexScalars.embed R) Y=>NY y))
    (A:X->Prop) (L:Hom X Y):
  (forall a,A a ->@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX A a) ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) Y) NX NY (complex_hom_real L) ->
  is_holomorphic hNX hNY A (fun x=>L x).
Proof.
move=>hOpen hBound;split.
- exact:(norm_bounded_linear_analytic hNX hNY hOpen hBound).
- move=>a M ha hActual.
  have hLinear:=norm_differential_linear hNX hNY (hOpen a ha) hBound.
  have hEqual:=norm_differential_unique hNX hNY hActual hLinear.
  move=>c x;rewrite hEqual !complex_hom_real_values.
  change (L (c*:(x:X))=c*:(L x:Y)).
  have h:=hom_linear L c x 0.
  change (L (c*:(x:X)+0)=c*:(L x:Y)+L 0) in h.
  have hZero:L 0=0 by exact:linear0.
  by rewrite !addr0 hZero addr0 in h.
Qed.
