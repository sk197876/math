(** Federer (1969), 1.6.6, p. 27: a finite-dimensional real subspace
    invariant under i has a complex basis and even real dimension. The
    ambient complex space may be arbitrary-dimensional. Source context are
    recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates ModuleQuotient SubspaceCarrier
  ScalarRestriction ComplexScalarSealed ComplexSubspaces ComplexOrderedBases
  FiniteDimension FiniteIndependence FiniteBasisComparison BoundedIndependentBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Finite.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Variable S : subspace VR.
Variable hs : complex_stable_subspace S.
Local Notation SC := (GRing.Lmodule.clone C (subspace_space (stable_complex_subspace hs)) _).
Local Notation SCR := (restricted_space embed SC).
Local Notation SR := (GRing.Lmodule.clone R (subspace_space S) _).
Variable m : nat.
Variable b : 'I_m -> SR.
Hypothesis hb : is_basis b.

(** Source for [complex_subspace_independent_bound]: Federer
    1.6.6, p. 27, complex basis of the associated space. Supporting
    finiteness: a complex independent family cannot exceed the known
    finite real dimension. *)
Lemma complex_subspace_independent_bound p (v : 'I_p -> SC) :
  finite_independent v -> (p <= m)%N.
Proof.
move=> hv.
have hr := @complex_independent_real R SC 'I_p v hv.
have hi : finite_independent (fun j => stable_subspace_real (hs:=hs) (v j)).
  exact (@finite_independent_map R 'I_p SCR SR
    (GRing.Linear.clone _ _ _ _ (stable_subspace_real (hs:=hs)) _) v
    (can_inj (@stable_subspace_realK R V S hs)) hr).
have hd := @finite_independent_dimension R (finite_basis_vect hb) p
  (fun j => stable_subspace_real (hs:=hs) (v j)) hi.
by rewrite finite_basis_dimension card_ord in hd.
Qed.

(** Source for [complex_subspace_basis_exists]: Federer 1.6.6,
    p. 27, choose a complex basis of the associated space. A bounded
    independent-family argument constructs such a finite basis. *)
Theorem complex_subspace_basis_exists : exists p (v : 'I_p -> SC), is_basis v.
Proof.
have [p [v [hv hp]]] := @bounded_independent_basis C SC m complex_subspace_independent_bound.
by exists p, v.
Qed.

(** Source for [complex_subspace_real_basis]: Federer 1.6.6,
    p. 27, the paired real basis of a complex plane. Every complex
    basis gives a real basis of twice the size in the original carrier. *)
Lemma complex_subspace_real_basis p (v : 'I_p -> SC) (hv : is_basis v) :
  is_basis (fun j => stable_subspace_real (hs:=hs) (ordered_real_basis v j)).
Proof.
exact: (@basis_transport R (Choice.clone 'I_(p+p) _) SCR SR
  (ordered_real_basis v)
  (GRing.Linear.clone _ _ _ _ (stable_subspace_real (hs:=hs)) _)
  (GRing.Linear.clone _ _ _ _ (stable_subspace_complex hs) _)
  (@stable_subspace_realK R V S hs) (@stable_subspace_complexK R V S hs) (ordered_real_basisP hv)).
Qed.

(** Source for [complex_subspace_even_dimension]: Federer
    1.6.6, p. 27, m=2p. The real dimension is exactly twice
    the size of any complex basis, including the zero subspace. *)
Theorem complex_subspace_even_dimension p (v : 'I_p -> SC) (hv : is_basis v) :
  m = (p+p)%N.
Proof. exact: finite_basis_size hb (complex_subspace_real_basis hv). Qed.
End Finite.
