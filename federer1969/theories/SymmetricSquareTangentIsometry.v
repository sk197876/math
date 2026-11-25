(** Federer (1969), 3.2.28(4), printed p. 266:
    DT preserves inner products on the tangent space of
    every unit-sphere submanifold. The statement below uses
    the actual proved differential and even holds for tangent
    vectors of arbitrary unit-sphere subsets. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom InnerProductUP InnerProductLaws InnerNorm
  SymmetricGrading SymmetricFormIsomorphism InnerSymmetric InnerSymmetricPositivity
  TangentConeUP UnitSphereSubsetTangents SymmetricTwoFactorInner
  SymmetricSquareDifferential NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TangentIsometry.
Variable R:realType.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Local Notation Y:=(symmetric_power V 2).
Local Notation hS:=(@symmetric_inner_productP R V B hB 2).
Local Notation S:=(@symmetric_inner_form R V B hB 2).

(** Source for [inner_projective_square_tangent_pairing]:
    the differential is an isometry on the sphere tangent,
    Federer 3.2.28(4), p. 266, from the exact
    degree-two pairing of 1.10.5, p. 47. *)
Lemma inner_projective_square_tangent_pairing (A:set V) x (L:Hom V Y):
  (forall y,A y ->inner_norm hB y= 1) ->inner_norm hB x= 1 ->
  (forall h,L h=symmetric_tuple_component [tuple h;x]) ->
  forall h k,norm_tangent_cone (inner_norm hB) A x h ->
    norm_tangent_cone (inner_norm hB) A x k ->S (L h) (L k)=B h k.
Proof.
move=>hA hx hL h k hh hk.
have hOrth:=@unit_sphere_subset_tangent_orthogonal R V B hB A x hA hx h hh.
have hUnit:B x x= 1 by rewrite -[B x x](inner_norm_sqr hB) hx expr1n.
rewrite !hL symmetric_two_factor_inner hUnit mulr1.
by rewrite (inner_symmetric hB h x) hOrth mulr0 addr0.
Qed.

(** Source for [inner_projective_square_actual_tangent_isometry]:
    the actual DT has unit tangent Jacobian, supporting
    the area argument in Federer 3.2.28(4), pp. 266–267.
    This theorem proves existence of the actual differential
    together with its full tangent inner-product law. *)
Theorem inner_projective_square_actual_tangent_isometry (A:set V) x:
  (forall y,A y ->inner_norm hB y= 1) ->inner_norm hB x= 1 ->
  exists L:Hom V Y,
    has_norm_differential (inner_norm hB) (inner_norm hS) (fun _=>True)
      (@SymmetricSquareGeometry.inner_projective_square R V) x L /\
    forall h k,norm_tangent_cone (inner_norm hB) A x h ->
      norm_tangent_cone (inner_norm hB) A x k ->S (L h) (L k)=B h k.
Proof.
move=>hA hx.
have [L [hD hL]]:=inner_projective_square_differential_exists hB x.
exists L; split; first exact hD.
exact:inner_projective_square_tangent_pairing hA hx hL.
Qed.
End TangentIsometry.
