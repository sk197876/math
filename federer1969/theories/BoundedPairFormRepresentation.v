(** Federer (1969), 4.1.19, p. 377: the
    two restricted Omega functionals give the
    bounded measurable forms phi and psi.
    The original pair cost keeps the same
    pointwise bound for both natural degrees. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentCoefficientNorms CompactSummableMultivectors
  CurrentLonePairImageUP CurrentLonePairCost
  CompactMultivectorFunctionalRepresentation FlatCochainRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section BoundedPairForms.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation A := (@compact_summable_multivector_space R h2 n m U hU).
Local Notation B := (@compact_summable_multivector_space R h2 n m.+1 U hU).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation sizeA := (@compact_summable_multivector_size R h2 n m U hU).
Local Notation sizeB := (@compact_summable_multivector_size R h2 n m.+1 U hU).
Local Notation cost := (@current_lone_pair_cost R h2 n m U hU).

(** Source for [bounded_lone_pair_form_representation]:
    the two bounded measurable differential forms
    of degrees m and m+1 in Federer
    4.1.19, p. 377, represent the
    two original factors and obey the same
    original pair bound c. This supporting theorem
    derives the forms from a bounded beta;
    it assumes no weak derivative equation or norm equality. *)
Theorem bounded_lone_pair_form_representation (beta : Hom P R^o) (c : R) :
  0 <= c -> (forall v, `|beta v| <= c*cost v) ->
  exists phi : UT -> A_m X R^o m,
  exists psi : UT -> A_m X R^o m.+1,
    @is_lone_pair_form_density R h2 n m U hU beta phi psi /\
    (forall x, @current_form_comass R h2 n m (phi x) <= c) /\
    forall x, @current_form_comass R h2 n m.+1 (psi x) <= c.
Proof.
move=> hC hBound.
have hLeft : linear (fun xi : A => ((xi,0):P)).
  move=> a xi zeta.
  change ((a*:xi+zeta,0) = (a*:xi+zeta,a*:(0:B)+0)).
  by rewrite scaler0 add0r.
have hRight : linear (fun eta : B => ((0,eta):P)).
  move=> a eta zeta.
  change ((0,a*:eta+zeta) = (a*:(0:A)+0,a*:eta+zeta)).
  by rewrite scaler0 add0r.
pose left := @HomMap R A P (fun xi => (xi,0))
  (introT (asboolP _) hLeft).
pose right := @HomMap R B P (fun eta => (0,eta))
  (introT (asboolP _) hRight).
pose betaA := hom_comp beta left.
pose betaB := hom_comp beta right.
have hA (xi : A) : `|betaA xi| <= c*sizeA xi.
  have h := hBound (xi,0).
  rewrite /current_lone_pair_cost /=
    (real_seminorm_zero
      (@compact_summable_multivector_size_laws R h2 n m.+1 U hU)) addr0 in h.
  exact: h.
have hB (eta : B) : `|betaB eta| <= c*sizeB eta.
  have h := hBound (0,eta).
  rewrite /current_lone_pair_cost /=
    (real_seminorm_zero
      (@compact_summable_multivector_size_laws R h2 n m U hU)) add0r in h.
  exact: h.
have [phi [hPhi [hPhiBound hPhiAction]]] :=
  @compact_multivector_functional_representation R h2 n m U hU
    betaA c hC hA.
have [psi [hPsi [hPsiBound hPsiAction]]] :=
  @compact_multivector_functional_representation R h2 n m.+1 U hU
    betaB c hC hB.
exists phi,psi; split; last by split.
split.
- split; first exact: hPhi.
  by exists c; split.
split.
- split; first exact: hPsi.
  by exists c; split.
split.
- move=> xi; exact: hPhiAction.
- move=> eta; exact: hPsiAction.
Qed.
End BoundedPairForms.
