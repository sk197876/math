(** Federer (1969), 1.8.2, p. 40: on an invariant complex
    subspace the imaginary rotation has no missing normal-form
    directions. Surjectivity makes its orthonormal normal-form pairs
    a basis; orthogonality makes their coefficients equal to one. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws LinearBasis
  FiniteBasisCriterion OrthonormalFamilies SkewNormalFormUP
  SkewNormalVectorActions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [surjective_skew_normal_basis]: Federer 1.8.2,
    p. 40, supporting completeness of the paired normal form for
    the imaginary rotation, whose inverse is its negative. *)
Theorem surjective_skew_normal_basis (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (f : {linear V -> V})
    k (a b : 'I_k -> V) (lambda : 'I_k -> R)
    (ho : orthonormal_family B (paired_family a b))
    (heq : forall x y, B (f x) y =
      \sum_i lambda i * skew_pair_form B (a i) (b i) x y)
    (hs : forall x, exists y, f y = x) : is_basis (paired_family a b).
Proof.
have hi := orthonormal_independent hB ho.
apply: (finite_basis_criterion hi).
move=> x; have [y hy] := hs x.
exists (fun p : 'I_k * bool =>
  if p.2 then lambda p.1 * B y (a p.1) else -(lambda p.1 * B y (b p.1))).
rewrite -hy (skew_normal_vector_expansion hB heq) /paired_family.
rewrite -(pair_bigA +%R (fun (i : 'I_k) (j : bool) =>
  (if j then lambda i * B y (a i) else -(lambda i * B y (b i))) *:
  (if j then b i else a i))).
apply: eq_bigr => i _.
by rewrite big_bool /paired_family /= scalerBr !scalerA scaleNr.
Qed.
