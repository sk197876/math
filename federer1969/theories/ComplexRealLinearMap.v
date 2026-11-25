(** Federer (1969), 3.4.12, p. 338:
    complex linearity of an actual real differential
    is an independent scalar-commutation law. Its complex
    linear-map carrier is supplied only after the law
    has been proved for the original real map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_complex_linear_real_map]: the original
    requirement that Df(x) be complex linear in
    3.4.12, p. 338. The original underlying
    real differential is retained as an actual map. *)
Definition is_complex_linear_real_map (R:realFieldType)
    (X Y:lmodType (ComplexScalars.C R))
    (L:Hom (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) Y)):Prop:=
  forall (c:ComplexScalars.C R) (x:X),L (c*:x)=c*:(L x:Y).

(** Source for [complex_real_linear_map_exists]: the
    original differential in 3.4.12, p. 338,
    is represented by an actual complex linear map
    when its independent complex scalar law holds. *)
Theorem complex_real_linear_map_exists (R:realFieldType)
    (X Y:lmodType (ComplexScalars.C R))
    (L:Hom (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) Y)):
  is_complex_linear_real_map L ->exists M:Hom X Y,forall x,M x=L x.
Proof.
move=>hComplex.
rewrite /is_complex_linear_real_map in hComplex.
have hLinear:linear (fun x:X=>(L x:Y)).
  move=>c x y.
  change (L (c*:x+y)=c*:(L x:Y)+(L y:Y)).
  rewrite linearD.
  change (L (c*:x)+L y=c*:(L x:Y)+L y).
  by rewrite hComplex.
exists (@HomMap (ComplexScalars.C R) X Y (fun x=>L x) (introT (asboolP _) hLinear)).
by move=>x.
Qed.

(** Source for [complex_real_linear_map_unique]: the
    underlying real map determines the original complex
    differential uniquely, supporting 3.4.12, p. 338. *)
Lemma complex_real_linear_map_unique (R:realFieldType)
    (X Y:lmodType (ComplexScalars.C R)) (M N:Hom X Y):
  (forall x,M x=N x) ->M=N.
Proof. exact:hom_ext. Qed.
