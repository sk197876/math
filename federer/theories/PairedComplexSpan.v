(** Federer (1969), 1.8.2, p. 40: supporting the converse
    equality case. A full real basis a_1,i a_1,...,a_m,i a_m
    spans the same space over the complex scalars using a_1,...,a_m.
    This is a coordinate consequence of 1.6.6, pp. 26-27. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction ComplexScalarSealed
  Hom LinearBasis FiniteDualDimension OrthonormalBilinearCoordinates
  SkewNormalFormUP FiniteSpans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [paired_real_basis_complex_span]: Federer 1.8.2,
    p. 40, supporting identification of the complex plane associated
    with an orthonormal paired volume. Orthogonality is unnecessary
    for this spanning statement. *)
Theorem paired_real_basis_complex_span (R : realFieldType)
    (V : lmodType (ComplexScalars.C R)) k (a : 'I_k -> V)
    (hb : @is_basis R (Choice.clone ('I_k * bool)%type _)
      (restricted_space (ComplexScalars.embed R) V)
      (paired_family a (fun i => ComplexScalars.ii R *: a i))) z :
    in_finite_span a z.
Proof.
pose d := fun p => dual_basis hb p z.
exists (fun i => ComplexScalars.embed R (d (i,false)) +
  ComplexScalars.embed R (d (i,true)) * ComplexScalars.ii R).
have hx := orthonormal_basis_vector_expansion hb z.
have hsum : (\sum_(p : 'I_k * bool) @GRing.scale R
    (restricted_space (ComplexScalars.embed R) V) (d p)
    (paired_family a (fun j => ComplexScalars.ii R *: a j) p)) =
  \sum_(i : 'I_k) \sum_(b : bool) @GRing.scale R
    (restricted_space (ComplexScalars.embed R) V) (d (i,b))
    (paired_family a (fun j => ComplexScalars.ii R *: a j) (i,b)).
  rewrite pair_bigA; apply: eq_bigr => [[i b]] _; by [].
rewrite {1}hx hsum.
apply: eq_bigr => i _; rewrite big_bool /paired_family /=.
change (ComplexScalars.embed R (d (i,true)) *: (ComplexScalars.ii R *: a i) +
  ComplexScalars.embed R (d (i,false)) *: a i =
  (ComplexScalars.embed R (d (i,false)) +
    ComplexScalars.embed R (d (i,true)) * ComplexScalars.ii R) *: a i).
by rewrite scalerA scalerDl addrC.
Qed.
