(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(14), p. 336:
    the product of the finitely many original component
    witnesses gives B_j for their union ideal.
    Reuse the proved binary product and the original
    finite-union ideal identity, preserving nonempty components. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology HolomorphicGermRing SetGermUP SetGermSealed SetGermLaws SetGermOrder
  SetGermBooleanOrder SetGermBoundary SetGermFiniteUnion HolomorphicGermVanishingSealed HolomorphicGermVanishingIdeal
  HolomorphicGermVanishingUnion HolomorphicIdealPropriety HolomorphicReductionActual HolomorphicReductionIntersectionProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteWitnesses.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Hypothesis hHerm:is_hermitian_product Herm.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation T:=(Topological.clone (real_norm_metric_space hNXR) _).
Local Notation G:=(@set_germ_space T 0).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNXR 0).
Local Notation union:=(@set_germ_finite_union T 0).
Local Notation Bj:=(fun alpha=>@holomorphic_reduction_actual_B R X Herm hHerm n e he omega (ideal alpha)).

(** Source for [holomorphic_reduction_finite_union]: the original
    product witness Phi in 3.4.8(14), p. 336,
    for a finite nonempty family of original nonempty germs.
    The chosen direction and rotation remain fixed throughout. *)
Theorem holomorphic_reduction_finite_union (F:seq G) (j:'I_n)
    (g:@unitary_group R X Herm hHerm (n+n) eR heR):
  F<>[::] ->(forall alpha,alpha \in F ->alpha<>@set_germ T 0 set0) ->
  (forall alpha,alpha \in F ->Bj alpha j g) ->Bj (union F) j g.
Proof.
elim:F=>[|alpha F ih].
- by move=>hNonempty;case:(hNonempty erefl).
- case:F ih=>[|beta F] ih hNonempty hMembers hWitnesses.
  + rewrite /set_germ_finite_union /= set_germ_union_empty.
    exact:hWitnesses alpha (mem_head alpha [::]).
  + pose tau:=union (beta::F).
    have hTau:tau<>@set_germ T 0 set0.
      move=>hEmpty.
      have hSub:=@set_germ_finite_union_member T 0 (beta::F) beta (mem_head beta F).
      change (set_germ_subset beta tau) in hSub;rewrite hEmpty in hSub.
      apply:(hMembers beta);first by rewrite in_cons mem_head orbT.
      exact:set_germ_subset_antisymmetric hSub (set_germ_empty_subset beta).
    have hAlpha:alpha<>@set_germ T 0 set0:=hMembers alpha (mem_head alpha (beta::F)).
    have hProper gamma (hGamma:gamma<>@set_germ T 0 set0):~ideal gamma (1:A).
      move=>hUnit;apply:hGamma;exact:(holomorphic_set_ideal_contains_one gamma).1 hUnit.
    change (@holomorphic_reduction_actual_B R X Herm hHerm n e he omega
      (ideal (@SetGerms.join T 0 alpha tau)) j g).
    rewrite holomorphic_set_ideal_union.
    apply:(@holomorphic_reduction_intersection_product R X Herm hHerm n e he omega
      (ideal alpha) (ideal tau) j g (holomorphic_set_ideal_ring_laws alpha) (hProper alpha hAlpha)
      (holomorphic_set_ideal_ring_laws tau) (hProper tau hTau)).
    * exact:hWitnesses alpha (mem_head alpha (beta::F)).
    * apply:ih;first by discriminate.
      -- move=>gamma hGamma;apply:hMembers;by rewrite in_cons hGamma orbT.
      -- move=>gamma hGamma;apply:hWitnesses;by rewrite in_cons hGamma orbT.
Qed.
End FiniteWitnesses.
