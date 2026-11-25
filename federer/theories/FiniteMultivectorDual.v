(** Federer (1969), 4.1.7, p. 357: the
    canonical multivector pairing identifies the whole
    dual of the finite covector space. Reuse the
    algebraic bidual representative from 2.4.12, p. 88. *)
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import Hom FreeVector LinearBasis FiniteDualDimension
  FiniteContinuousReflexivity ExteriorGrading AlternatingForms AlternatingIsomorphism
  AlternatingPairing MultivectorDualUP MultivectorDualSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section FiniteMultivectorDual.
Variable K:fieldType.
Variable V:lmodType K.
Variable m:nat.
Variable I:finType.
Variable b:I->exterior_power V m.
Hypothesis hb:is_basis b.
Local Notation E := (@MultivectorDual.evaluation K V m).

(** Source for [finite_multivector_dual_injective]:
    the original covector evaluations distinguish
    multivectors, supporting Federer 4.1.7, p. 357. *)
Theorem finite_multivector_dual_injective:injective E.
Proof.
move=>xi eta he.
apply:(can_inj (basis_coordinatesK hb)); apply/fsfunP=>i.
have h:=congr1 (fun a:Hom (A_m V K^o m) K^o=>a (hom_to_form (dual_basis hb i))) he.
rewrite !MultivectorDual.laws /pairing !hom_to_formK in h.
change (dual_basis hb i xi=dual_basis hb i eta).
exact:h.
Qed.

(** Source for [finite_multivector_dual_surjective]:
    every linear functional on the original finite
    covectors is evaluation at a multivector,
    supporting Federer 4.1.7, p. 357. *)
Theorem finite_multivector_dual_surjective:
  forall a:Hom (A_m V K^o m) K^o,exists xi:exterior_power V m,E xi = a.
Proof.
move=>ell.
pose ed:=hom_of_linear (GRing.Linear.clone _ _ _ _ (@form_to_hom K V K^o m) _).
have hi:injective ed:=can_inj (@form_to_homK K V K^o m).
have [xi hxi]:=@finite_dual_subspace_representative K I (exterior_power V m)
  (A_m V K^o m) b hb ed hi ell.
exists xi; apply:hom_ext=>phi.
rewrite MultivectorDual.laws.
symmetry; exact:(hxi phi).
Qed.
End FiniteMultivectorDual.
