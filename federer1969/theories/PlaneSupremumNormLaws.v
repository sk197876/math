(** Federer (1969), 2.10.44, printed p. 202,
    first example: the coordinate supremum mu is a
    norm on R^2. Prove its real norm laws and
    the printed maximum formula from the abstract
    least-bound specification alone. This uses the
    project's proved uniform-norm algebra, not an
    external normed-space implementation. Source
    editions and counterexample comparison: PlaneSupremumNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates RealNormUP
  UniformFunctionNormUP UniformFunctionNormLaws PlaneSupremumNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [plane_coordinate_index_cases]: supporting
    two-coordinate indexing for mu in 2.10.44,
    p. 202. This is finite-index infrastructure,
    not a separately stated book assertion. *)
Lemma plane_coordinate_index_cases (i : 'I_2) : i=ord0 \/ i=ord_max.
Proof.
case: i=> [[|[|k]] hi].
- left; exact: val_inj.
- right; exact: val_inj.
- exfalso; by move: hi; rewrite ltnS ltnS ltn0.
Qed.

(** Source for [plane_supremum_norm_value]: direct
    two-coordinate supremum formula in 2.10.44,
    p. 202, derived from the norm's order laws. *)
Lemma plane_supremum_norm_value (R : realType) (N : R_n R 2 -> R)
    (hN : is_plane_supremum_norm N) x :
  N x=Num.max `|x ord0| `|x ord_max|.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@uniform_function_norm_least R 'I_2 (fun i=>x i) (N x) (hN x)
    (Num.max `|x ord0| `|x ord_max|)).
  + by rewrite le_max normr_ge0.
  + move=> i; have [->|->] := plane_coordinate_index_cases i.
    * by rewrite le_max lexx.
    * by rewrite le_max lexx orbT.
- rewrite ge_max; apply/andP; split.
  + exact (@uniform_function_norm_bound R 'I_2 (fun i=>x i) (N x) (hN x) ord0).
  + exact (@uniform_function_norm_bound R 'I_2 (fun i=>x i) (N x) (hN x) ord_max).
Qed.

(** Source for [plane_supremum_norm_is_real_norm]: supporting
    verification that the printed mu is a real
    norm in 2.10.44, p. 202. Nonnegativity,
    homogeneity, triangle inequality and separation
    follow only from its uniform-bound specification. *)
Theorem plane_supremum_norm_is_real_norm (R : realType) (N : R_n R 2 -> R) :
  is_plane_supremum_norm N -> is_real_norm N.
Proof.
move=> hN; split.
- constructor.
  + move=> x; exact: uniform_function_norm_nonnegative (hN x).
  + move=> a x.
    have hs := hN (a*:x).
    have he : (fun i : 'I_2=>(a*:x) i)=(fun i=>a*x i).
      apply: funext=> i; by rewrite ffunE.
    rewrite he in hs.
    exact (@uniform_function_norm_unique R 'I_2 (fun i=>a*x i) _ _ hs
      (@uniform_function_norm_scale R 'I_2 (fun i=>x i) (N x) a (hN x))).
  + move=> x y.
    have hs := hN (x+y).
    have he : (fun i : 'I_2=>(x+y) i)=(fun i=>x i+y i).
      apply: funext=> i; by rewrite ffunE.
    rewrite he in hs.
    exact: uniform_function_norm_triangle (hN x) (hN y) hs.
- move=> x hx.
  have hs := hN x; rewrite hx in hs.
  have hh := @uniform_function_norm_separates R 'I_2 (fun i=>x i) hs.
  apply/ffunP=> i; by rewrite (hh i) ffunE.
Qed.
