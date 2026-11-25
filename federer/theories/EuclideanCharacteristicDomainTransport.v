(** Federer (1969), 4.1.27, p. 384:
    the cube product may be viewed in
    its whole Euclidean domain. Equality transport
    of a containing open domain preserves
    the original characteristic current, just as
    for the full Cartesian presentation in
    4.1.11, p. 366. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDomainTransport OpenEuclideanCharacteristicCurrent
  EuclideanLebesgueDimensions MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_characteristic_domain_transport]: an equal
    presentation of the original open domain
    changes no characteristic-current action, supporting
    the product source in 4.1.27,
    p. 384. This is equality transport
    of existing currents, not a new integration operator. *)
Theorem euclidean_characteristic_domain_transport (R:realType) (h2:(1+1:R)!=0) n
    (U V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall x,V x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V x)
    (e:U=V) (A:set (R_n R n))
    (hA:measure_measurable (@euclidean_lebesgue_measure R n) A):
  @current_domain_transport R h2 n U hU V e hV n
    (@open_euclidean_characteristic_current R h2 n U hU A hA)=
      @open_euclidean_characteristic_current R h2 n V hV A hA.
Proof.
subst V;have hOpen:hV=hU:=Prop_irrelevance _ _;subst hV.
exact:current_domain_transport_refl.
Qed.
