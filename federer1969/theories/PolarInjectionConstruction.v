(** Federer (1969), 1.7.3, p. 30: existence of g and h with their prescribed
    values on the adapted basis. the statement and Federer give g symmetric
    and h orthogonal. Private witness, imported only by its seal and audit. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  OrthonormalFamilies FiniteIndependence LinearBasis BasisInterpolation
  PartialOrthonormalCompletion OrthogonalBasisCriteria PolarFactorisationUP
  TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Construction.
Variable R : realType.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.
Variable u : 'I_n -> U.
Hypothesis hu : finite_independent u.
Variable f : {linear V -> U}.
Hypothesis hfo : forall i j, i != j -> C (f (e i)) (f (e j)) = 0.

(** Source for [polar_injection_basis_witness]: Federer
    1.7.3, p. 30, construct g(e_i)=|f(e_i)|e_i and h(e_i)
    equal to the normalised image whenever it is nonzero, completing
    the remaining images orthonormally. This proves h composed with g=f. *)
Theorem polar_injection_basis_witness :
  exists (g : {linear V -> V}) (h : {linear V -> U}),
    is_injection_factorisation B C f g h /\
    (forall i, g (e i) = inner_norm hC (f (e i)) *: e i) /\
    (forall i, f (e i) != 0 -> h (e i) = inner_normalize hC (f (e i))).
Proof.
pose P := fun i => f (e i) != 0.
pose v := fun i => inner_normalize hC (f (e i)).
have hv i : P i -> C (v i) (v i) = 1 by exact: inner_normalize_square.
have hvo i j : i != j -> P i -> P j -> C (v i) (v j) = 0.
  move=> hij _ _; apply: inner_normalize_orthogonal.
  rewrite (inner_symmetric hC); apply: inner_normalize_orthogonal.
  rewrite (inner_symmetric hC); exact: hfo hij.
have [d [hd hdv]] := @partial_orthonormal_completion R U C hC n u hu P v hv hvo.
pose g := basis_interpolation he (fun i => inner_norm hC (f (e i)) *: e i).
pose h := basis_interpolation he d.
have hg i : g (e i) = inner_norm hC (f (e i)) *: e i := basis_interpolationE he _ i.
have hh i : h (e i) = d i := basis_interpolationE he _ i.
exists g, h; split; last by split=> // i hi; rewrite hh hdv.
constructor.
- exact: (@symmetric_diagonal_basis_criterion R V B hB n e he ho g
    (fun i => inner_norm hC (f (e i))) hg).
- apply: (@orthogonal_map_basis_criterion R V U B C hB hC n e he ho h).
  by move=> i j; rewrite !hh hd.
- apply: (basis_linear_ext he (linear_comp h g) f) => i.
  change (h (g (e i)) = f (e i)).
  rewrite hg linearZ hh.
  have [hz|hn] := eqVneq (f (e i)) 0.
  + rewrite hz inner_norm0.
    change ((0 : R) *: d i = 0); exact: scale0r.
  + rewrite (hdv i hn); exact: inner_normalizeK hn.
Qed.
End Construction.
