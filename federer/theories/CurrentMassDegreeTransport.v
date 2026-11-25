(** Federer (1969), 4.1.11, p. 365: identifying
    equal natural degree expressions changes neither a
    current nor its original mass. This supporting law
    concerns only the existing equality transport. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentMassSealed
  CurrentDegreeTransport CurrentDegreeTransportIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_mass_degree_transport]: the original
    mass is invariant under identification of equal degrees,
    supporting the source-chain mass in Federer 4.1.11,
    p. 365, with no finiteness or representation premise. *)
Theorem current_mass_degree_transport (R:realType) (h2:(1+1:R)!=0)
    n (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    k l (e:k=l) (T:@current_space R h2 n U hU k):
  @CurrentMass.value R h2 n l U hU (@current_degree_transport R h2 n U hU k l e T)=
    @CurrentMass.value R h2 n k U hU T.
Proof.
case:l/e.
by rewrite current_degree_transport_identity.
Qed.
