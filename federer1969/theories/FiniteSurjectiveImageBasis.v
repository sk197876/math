(** Federer (1969), 3.4.7, p. 325: the
    transverse space has finite dimension. This supporting
    linear-algebra proof extracts a basis from the images
    of an original finite basis; it uses the project's
    proved basis and finite-span laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom LinearBasis FiniteSpans FiniteBasisCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_surjective_image_basis_exists]:
    a surjective linear image of the original finite
    source has a finite basis, supporting 3.4.7,
    p. 325. The basis remains an existence witness. *)
Theorem finite_surjective_image_basis_exists (R:fieldType) (X Y:lmodType R)
    n (e:'I_n->X) (L:{linear X->Y}):
  is_basis e ->(forall y,exists x,L x = y) ->
  exists m,exists f:'I_m->Y,is_basis f.
Proof.
move=>he hSurjective.
have [m [f [hIndependent hSpan]]]:=finite_independent_span [seq L (e i)|i<-enum 'I_n].
have hSource x:in_finite_span f (L x).
  move:x;apply:(@basis_induction R (Choice.clone 'I_n _) X e he (fun x=>in_finite_span f (L x)))=>[|x y hx hy|a x hx|i].
  - rewrite linear0;exact:in_finite_span_zero.
  - rewrite linearD;exact:in_finite_span_add hx hy.
  - rewrite linearZ;exact:(@in_finite_span_scale R Y m f a (L x) hx).
  - apply:hSpan;apply/mapP;exists i;first exact:mem_enum.
    reflexivity.
exists m,f;apply:(@finite_basis_criterion R [the finType of 'I_m] Y f hIndependent)=>y.
have [x <-]:=hSurjective y;exact:hSource x.
Qed.
