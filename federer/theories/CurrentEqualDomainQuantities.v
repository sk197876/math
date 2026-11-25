(** Federer (1969), 4.1.18, pp. 374–375: the
    mass and representability of a current do not
    depend on proof presentations of the same original
    open domain. Reuse only the existing exact domain
    transport and proof irrelevance.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentDomainTransport
  CurrentIntegrationCriterion CurrentMassSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentEqualDomainQuantities.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variables U V:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Hypothesis hV:forall x,V x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) V x.
Variable e:U=V.
Variable T:@current_space R h2 n U hU m.

(** Source for [current_equal_domain_mass]: exact original
    mass under a change of equal-domain presentation,
    supporting the sharp bounds of 4.1.18, p. 374. *)
Theorem current_equal_domain_mass:
  @CurrentMass.value R h2 n m V hV
    (@current_domain_transport R h2 n U hU V e hV m T)=
  @CurrentMass.value R h2 n m U hU T.
Proof.
subst V;have hProof:hV=hU:=Prop_irrelevance _ _;subst hV.
by rewrite current_domain_transport_refl.
Qed.

(** Source for [current_equal_domain_representable]: exact
    original Radon representability is invariant under
    equal-domain transport, supporting 4.1.18,
    pp. 374–375. No representation is fabricated
    by this equality adapter. *)
Theorem current_equal_domain_representable:
  @is_integration_representable_current R h2 n m U hU T <->
  @is_integration_representable_current R h2 n m V hV
    (@current_domain_transport R h2 n U hU V e hV m T).
Proof.
subst V;have hProof:hV=hU:=Prop_irrelevance _ _;subst hV.
by rewrite current_domain_transport_refl.
Qed.
End CurrentEqualDomainQuantities.
