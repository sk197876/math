(** Federer (1969), 3.4.12, p. 339, extending the definitions
    of 3.4.5, p. 321: functional holomorphic submanifolds and
    blocks retain the original complex equations and independent
    complex differentials. These laws assume no chart existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP FiniteIndependence
  ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm FiniteCoordinates
  HolomorphicCoordinateNorm HolomorphicUP HolomorphicLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [is_functional_holomorphic_submanifold]: replace the
    original real analytic equations and independent real differentials
    by holomorphic equations and independent complex differentials,
    exactly as directed in 3.4.12, p. 339. The empty
    equation family retains the full-dimension boundary. *)
Definition is_functional_holomorphic_submanifold (R:realType) n m
    (U S:set (coordinate_space (ComplexScalars.C R) n)):Prop:=
  let X:=coordinate_space (ComplexScalars.C R) n in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  (m<=n)%N /\@open (real_norm_metric_space hNX) U /\
  exists f:'I_(n-m)->X->ComplexScalars.C R,exists g:X->ComplexScalars.C R,
    (forall i,@is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R)
      hNX (@complex_modulus_real_norm R) U (f i)) /\
    @is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R)
      hNX (@complex_modulus_real_norm R) U g /\
    (forall x,S x <->U x /\(forall i,f i x=0) /\g x<>0) /\
    forall x,S x ->exists D:'I_(n-m)->Hom X (ComplexScalars.C R)^o,
      (forall i,@has_norm_differential R (restricted_space (ComplexScalars.embed R) X)
        (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) U (f i) x (complex_hom_real (D i))) /\
      finite_independent D.
(** Source for [is_functional_holomorphic_block]: components of the
    original functional holomorphic submanifolds are the original blocks,
    extending 3.4.5, p. 321, under 3.4.12, p. 339. *)
Definition is_functional_holomorphic_block (R:realType) n m
    (U B:set (coordinate_space (ComplexScalars.C R) n)):Prop:=
  exists S:set (coordinate_space (ComplexScalars.C R) n),is_functional_holomorphic_submanifold m U S /\
    exists a:coordinate_space (ComplexScalars.C R) n,S a /\
      B=@connected_component (Topological.clone (real_norm_metric_space
        (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) S a.
