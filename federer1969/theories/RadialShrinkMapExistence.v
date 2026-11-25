(** Existence proof for Federer (1969), 4.1.15,
    p. 372. The case formula is only an existence witness
    for the independent printed value laws. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import RealNormUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct RadialShrinkMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [radial_shrink_map_exists]: the original
    Psi_r exists for 0<r<infinity, Federer 4.1.15, p. 372.
    A real radius is finite. The witness handles dimension
    zero and makes no nonzero-vector assumption. *)
Theorem radial_shrink_map_exists (R : realType) n (r : R) :
  0 < r -> exists P,
    @is_radial_shrink_map R n r P.
Proof.
move=> hr.
pose N := inner_norm (@euclidean_inner_productP R n).
exists (fun y : R_n R n =>
  if N y < r then 0 else (1-r/N y) *: y).
constructor.
- move=> y hy; by rewrite hy.
- move=> y hy.
  have hNot : ~~ (N y < r) by rewrite -leNgt.
  by rewrite (negPf hNot).
Qed.
