(** Federer (1969), 2.10.45, printed p. 203: use the positive subdivision
    count and its mesh bracket to bound cell widths and the total cube-count
    times mesh-volume. These consequences use only abstract count laws.
    Source context: UniformMeshCountUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import UniformMeshCountUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [uniform_mesh_count_cell_width]: supporting
    side-width bound for the j(T)^m covering
    cubes in 2.10.45, p. 203. Equal
    subdivision yields widths at most the supplied mesh. *)
Lemma uniform_mesh_count_cell_width (R : realType) (u h : R) k :
  is_uniform_mesh_count u h k -> u/k%:R<=h.
Proof.
move=> hk.
have hkpos : (0<k%:R :> R) by rewrite ltr0n; exact: uniform_mesh_count_positive_law hk.
rewrite ler_pdivrMr // mulrC; exact: uniform_mesh_count_covers_law hk.
Qed.

(** Source for [uniform_mesh_count_power_budget]: direct
    j(T)^m diam(T)^m<=(u+delta)^m estimate
    in the last display of 2.10.45,
    p. 203, when the positive mesh is
    at most the common cutoff delta. *)
Lemma uniform_mesh_count_power_budget (R : realType) (u h delta : R) k m :
  0<=u -> 0<=h -> h<=delta -> is_uniform_mesh_count u h k ->
    (k%:R)^+m*h^+m<=(u+delta)^+m.
Proof.
move=> hu hh hd hk.
rewrite -exprMn; apply: lerXn2r.
- by apply: mulr_ge0=> //; exact: ler0n.
- exact: addr_ge0 hu (le_trans hh hd).
- exact: le_trans (uniform_mesh_count_upper_law hk) (lerD (lexx _) hd).
Qed.
