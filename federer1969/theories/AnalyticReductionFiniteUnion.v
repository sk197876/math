(** Federer (1969), 3.4.8(14), p. 336:
    the product of the finitely many original component
    witnesses gives B_j for their union ideal.
    Reuse the proved binary product and the original
    finite-union ideal identity, preserving nonempty components. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology AnalyticGermRing SetGermUP SetGermSealed SetGermLaws SetGermOrder
  SetGermBooleanOrder SetGermBoundary SetGermFiniteUnion GermVanishingSealed GermVanishingIdeal
  GermVanishingUnion AnalyticIdealPropriety AnalyticReductionActual AnalyticReductionIntersectionProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteWitnesses.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=(@set_germ_space T 0).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation union:=(@set_germ_finite_union T 0).
Local Notation Bj:=(fun alpha=>@analytic_reduction_actual_B R X B hB n e he omega (ideal alpha)).

(** Source for [analytic_reduction_finite_union]: the original
    product witness Phi in 3.4.8(14), p. 336,
    for a finite nonempty family of original nonempty germs.
    The chosen direction and rotation remain fixed throughout. *)
Theorem analytic_reduction_finite_union (F:seq G) (j:'I_n)
    (g:@orthogonal_group R X B hB n e he):
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
      move=>hUnit;apply:hGamma;exact:(analytic_set_ideal_contains_one gamma).1 hUnit.
    change (@analytic_reduction_actual_B R X B hB n e he omega
      (ideal (@SetGerms.join T 0 alpha tau)) j g).
    rewrite analytic_set_ideal_union.
    apply:(@analytic_reduction_intersection_product R X B hB n e he omega
      (ideal alpha) (ideal tau) j g (analytic_set_ideal_ring_laws alpha) (hProper alpha hAlpha)
      (analytic_set_ideal_ring_laws tau) (hProper tau hTau)).
    * exact:hWitnesses alpha (mem_head alpha (beta::F)).
    * apply:ih;first by discriminate.
      -- move=>gamma hGamma;apply:hMembers;by rewrite in_cons hGamma orbT.
      -- move=>gamma hGamma;apply:hWitnesses;by rewrite in_cons hGamma orbT.
Qed.
End FiniteWitnesses.
