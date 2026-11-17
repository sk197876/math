(** Federer (1969), 3.4.8(8), p. 330:
    the original primitive linear combination
    is exactly omega_m composed with the
    inverse original rotation. Reuse orthonormal
    bilinear coordinates and fixed-prefix covectors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthonormalParseval OrthonormalBilinearCoordinates
  FiniteDualDimension DualityAnnihilator OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  OrthogonalCoordinateFixing AnalyticFixedPrefixPullback OrdinalCoordinateTail OrdinalCoordinateTailSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation action:=(fun g:O=>@orthogonal_element_map R X B hB n e he g).
Variables q h:O.
Hypothesis hInverse:forall x:X,action q (action h x) = x.

(** Source for [orthogonal_inverse_covector_coordinates]:
    the full coordinate identity in the
    displayed calculation of 3.4.8(8), p. 330.
    The existing orthonormal bilinear expansion
    computes the original inverse pullback. *)
Theorem orthogonal_inverse_covector_coordinates (i:'I_n) (x:X):
  omega i (action h x) = \sum_(j<n) omega j (action q (e i))*omega j x.
Proof.
have hOmega j:omega j = dual_basis he j:=biorthogonal_basis_unique he hDual j.
rewrite hOmega (@orthonormal_basis_inner_coordinate R X B hB [the finType of 'I_n] e hON he).
have hInner:=@orthogonal_element_inner R X B hB n e he q (action h x) (e i).
rewrite hInverse in hInner.
rewrite -hInner (inner_symmetric hB x (action q (e i)))
  (@orthonormal_basis_bilinear_coordinates R X B (inner_bilinear hB)
    [the finType of 'I_n] e hON he).
apply:eq_bigr=>j _;by rewrite -!hOmega.
Qed.

(** Source for [orthogonal_primitive_suffix_covector]:
    the original suffix combination of
    omega_j(q(e_m)) omega_j equals omega_m q^-1,
    3.4.8(8), p. 330. Actual Q_m
    membership removes exactly the zero prefix;
    no primitive-coordinate equation is assumed. *)
Theorem orthogonal_primitive_suffix_covector (m:'I_n)
  (hMN:((m:nat)<=n)%N):
  @analytic_suffix_rotation_group R X B hB n e he m q ->forall x:X,
  omega m (action h x) = \sum_(i<n-m)
    omega (ordinal_coordinate_tail_index hMN i) (action q (e m))*
    omega (ordinal_coordinate_tail_index hMN i) x.
Proof.
move=>hQ x;rewrite orthogonal_inverse_covector_coordinates.
apply:ordinal_coordinate_tail_sum=>j hJM.
have hFixed:=@analytic_fixed_prefix_covector R X B hB n e he hON omega hDual m q hQ j hJM (e m).
rewrite hFixed hDual.
have hDifferent:j!=m by apply/eqP=>hEqual;by rewrite hEqual ltnn in hJM.
by rewrite (negbTE hDifferent) mul0r.
Qed.
End Coordinates.
