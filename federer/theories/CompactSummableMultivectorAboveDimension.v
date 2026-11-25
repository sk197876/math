(** Federer (1969), 4.1.18, p. 376: Omega_(n+1)
    is zero, as used in the original downward induction
    and its final top-degree conclusion. Reuse the
    exterior-power theorem of 1.3.2, p. 15,
    with the original coordinate basis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates ExteriorGrading FiniteExteriorPowers CurrentDomain
  CompactSummableMultivectors CompactSummableFieldExtensionality
  CompactSummableFieldFinitePrefix.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [compact_summable_multivector_above_dimension]:
    every original compact summable coefficient of degree
    greater than n is the actual zero field,
    Federer 4.1.18, p. 376. Empty U and n=0 remain. *)
Theorem compact_summable_multivector_above_dimension (R:realType)
    (h2:(1+1:R)!=0) n m (hDegree:(n<m)%N)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (xi:@compact_summable_multivector_space R h2 n m U hU):xi=0.
Proof.
apply:(@compact_summable_field_value_injective R (current_domain R n U)
  (exterior_power (R_n R n) m) _ _ _ _).
apply:funext=>x.
rewrite compact_summable_field_value_zero.
exact:(@exterior_power_above_dimension R n (R_n R n)
  (@coordinate_basis R n) (@coordinate_basisP R n) h2 m hDegree _).
Qed.
