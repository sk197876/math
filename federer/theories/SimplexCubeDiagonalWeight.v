(** Federer (1969), 4.1.27, p. 384:
    the product of the diagonal prefix
    coefficients is exactly the printed power
    product in the wedge Jacobian. Apply
    the finite exponent identity without cancelling
    coordinates, retaining degenerate and degree-zero cases. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  SimplexCubeParametrisationUP FinitePrefixProductPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_cube_diagonal_weight]: the exact
    coefficient multiplying zeta in 4.1.27,
    p. 384. The auxiliary natural-index extension
    is used only inside this finite
    algebraic proof and is not a
    public choice of the parametrising map. *)
Theorem simplex_cube_diagonal_weight (R:realType) m (x:R_n R m):
  (\prod_(i:'I_m) simplex_cube_prefix_product x (val i))=
    simplex_cube_jacobian_weight x.
Proof.
pose w k:=oapp x 0 (insub k:option 'I_m).
have hW (i:'I_m):w (val i)=x i by rewrite /w valK.
have hPrefix k (hK:(k<=m)%N):
    simplex_cube_prefix_product x k=\prod_(j<k) w j.
  rewrite /simplex_cube_prefix_product (big_ord_widen m w hK).
  apply:eq_bigr=>j _;exact:esym (hW j).
have hOuter:(\prod_(i:'I_m) simplex_cube_prefix_product x (val i))=
    \prod_(i<m) \prod_(j<i) w j.
  apply:eq_bigr=>i _;exact:hPrefix (val i) (ltnW (ltn_ord i)).
rewrite hOuter (@finite_prefix_product_power R w m) /simplex_cube_jacobian_weight.
apply:eq_bigr=>i _;by rewrite hW.
Qed.
