(** Federer (1969), 4.1.8, p. 361, used in
    4.1.12, p. 369: finite original masses give
    the numerical Cartesian mass bound. Their
    integration representations follow from 4.1.7 and
    are not extra hypotheses on the input currents. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentCartesianMassBound CurrentFiniteMassRepresentation CurrentMassSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianFiniteMassBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).

(** Source for [current_cartesian_finite_mass_bound]:
    M(S times T)<=a b for M(S)=a and M(T)=b,
    supporting the exact flat product estimate in
    Federer 4.1.12, p. 369. Zero masses and
    zero degrees remain included. *)
Theorem current_cartesian_finite_mass_bound
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j) a b:
  @CurrentMass.value R h2 m i A hA S=a%:E->
  @CurrentMass.value R h2 n j B hB T=b%:E->
  (@CurrentMass.value R h2 (m+n) (i+j) AB hAB
    (@CartesianCurrentProduct.value R h2 m n i j A B hA hB S T)<=(a*b)%:E)%E.
Proof.
move=>hMassS hMassT.
have hSFinite:(@CurrentMass.value R h2 m i A hA S < +oo)%E by rewrite hMassS;exact:ltry.
have hTFinite:(@CurrentMass.value R h2 n j B hB T < +oo)%E by rewrite hMassT;exact:ltry.
have hS:=@current_finite_mass_representation R h2 m i A hA S hSFinite.
have hT:=@current_finite_mass_representation R h2 n j B hB T hTFinite.
have hDef:mule_def (@CurrentMass.value R h2 m i A hA S) (@CurrentMass.value R h2 n j B hB T).
  by rewrite hMassS hMassT /mule_def.
have h:=@current_cartesian_mass_bound R h2 m n i j A B hA hB S T hS hT hDef.
by rewrite hMassS hMassT -EFinM in h.
Qed.
End CurrentCartesianFiniteMassBound.
