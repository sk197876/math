(** Federer (1969), 3.4.5, p. 319: a fixed
    analytic inner map makes each composite derivative depend
    continuously on finitely many outer derivatives. This expands
    the composition formula of 3.1.11, p. 222. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal ring.
From Federer Require Import Hom RealNormUP SymmetricForms SymmetricFormSum SymmetricOperatorNorm
  SymmetricMultiIndices SymmetricMonomials SymmetricDividedMonomials CompositionMultiIndices CompositionPositiveDegree
  CompositionFormCoefficient CompositionTermPostcomposeBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [composition_form_finite_outer_bound]: the
    finite derivative estimate proving continuity of the original
    pullback in 3.4.5, p. 319. The factor multiplying
    the outer tolerance is an actual finite sum determined only
    by the inner derivatives. *)
Theorem composition_form_finite_outer_bound (R:realType) (X Y T:lmodType R)
    (NX:X->R) (NY:Y->R) (NT:T->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNT:is_real_norm NT)
    p (phi:forall i,S_m X Y i) (psi:forall i,S_m Y T i) (C:'I_p->R) (B:R):
  (1<=p)%N ->(forall i,0<=C i) ->
  (forall i,(symmetric_operator_norm hNX.1 NY (phi (val i).+1)<=(C i)%:E)%E) ->
  0<=B ->
  (forall j,(1<=j<=p)%N ->(symmetric_operator_norm hNY.1 NT (psi j)<=B%:E)%E) ->
  (symmetric_operator_norm hNX.1 NT
    (@composition_differential_form_coefficient R X Y T p phi psi p)<=
    (B*\sum_(alpha:composition_indices p p)
      ((p`!)%:R/(symmetric_multi_factorial (composition_indices_unbound alpha))%:R)*
        symmetric_scalar_monomial (fun i:'I_p=>C i/((val i).+1`!)%:R)
          (composition_indices_unbound alpha))%:E)%E.
Proof.
move=>hp hC hPhi hB hPsi.
apply:(proj2 (symmetric_operator_norm_bound hNX.1 NT _ _))=>t ht.
have hterm (alpha:composition_indices p p):
    NT (@composition_differential_form_term R X Y T p phi psi p alpha t)<=
    B*(((p`!)%:R/(symmetric_multi_factorial (composition_indices_unbound alpha))%:R)*
      symmetric_scalar_monomial (fun i:'I_p=>C i/((val i).+1`!)%:R)
        (composition_indices_unbound alpha)).
  have hDegree:(1<=symmetric_multi_degree (composition_indices_unbound alpha)<=p)%N.
    apply/andP;split;[exact:composition_indices_positive_outer_degree|exact:composition_indices_outer_degree].
  have hLinearId:linear (fun z:T=>z) by move=>b z w.
  pose L:=@HomMap R T T (fun z=>z) (introT (asboolP _) hLinearId).
  have hIdentity z:NT (L z)<=1*NT z by rewrite mul1r.
  have hBound:=@composition_form_term_postcompose_bound R X Y T T NX NY NT NT
    hNX hNY hNT hNT p p phi psi C L 1 B alpha t hC hPhi ler01 hB
    hIdentity (hPsi _ hDegree) ht.

  have hEqual:(p`!)%:R*(1*B/(symmetric_multi_factorial (composition_indices_unbound alpha))%:R)*
      symmetric_scalar_monomial (fun i:'I_p=>C i/((val i).+1`!)%:R) (composition_indices_unbound alpha)=
    B*(((p`!)%:R/(symmetric_multi_factorial (composition_indices_unbound alpha))%:R)*
      symmetric_scalar_monomial (fun i:'I_p=>C i/((val i).+1`!)%:R) (composition_indices_unbound alpha)) by ring.
  by rewrite hEqual in hBound.
have hLinear:linear (fun F:S_m X T p=>F t).
  move=>b F G;by rewrite sform_addE sform_scaleE.
pose E:=@HomMap R (S_m X T p) T (fun F=>F t) (introT (asboolP _) hLinear).
have hSum:(\sum_(alpha:composition_indices p p)
    @composition_differential_form_term R X Y T p phi psi p alpha) t=
  \sum_(alpha:composition_indices p p) @composition_differential_form_term R X Y T p phi psi p alpha t.
  change (E (\sum_(alpha:composition_indices p p)
    @composition_differential_form_term R X Y T p phi psi p alpha)=
    \sum_(alpha:composition_indices p p) E (@composition_differential_form_term R X Y T p phi psi p alpha)).
  by rewrite linear_sum.
rewrite /composition_differential_form_coefficient hSum mulr_sumr.
apply:le_trans (real_seminorm_sum hNT.1 _) _.
apply:ler_sum=>alpha _;exact:hterm.
Qed.
