(** Federer (1969), 3.2.28(4), printed p. 267:
    G(n,m) is realized by the actual symmetric squares
    of unit simple m-vectors and is a smooth manifold
    of dimension m(n-m) for positive m<=n. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct
  EuclideanLinearMaps InnerProductUP InnerNorm ExteriorGrading ExteriorNorm InnerExterior
  InnerExteriorPositivity FiniteExteriorPowers FiniteOrdinalBasis NonzeroSimple
  AssociatedSubspace SimpleElementary SymmetricGrading InnerSymmetric InnerSymmetricPositivity
  SymmetricSquareGeometry GrassmannSquareUP GrassmannSquareRealisation
  FiniteInnerSmoothSubmanifoldUP EuclideanOrientedGrassmannSmooth SymmetricSquareSmoothSubmanifold.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_grassmann_square_set]: the actual
    square realization of G(n,m) in Federer 3.2.28(4),
    p. 267. Membership specifies a represented abstract
    plane, with existence and uniqueness proved separately. *)
Definition euclidean_grassmann_square_set (R:realType) n m:
    set (symmetric_power (exterior_power (R_n R n) m) 2):=
  [set t|exists P:G (R_n R n) m,
    is_grassmann_square_representative (@euclidean_inner_productP R n)
      (euclidean_two_nonzero R) P t].

(** Source for [euclidean_grassmann_square_image]: the exact
    identity G(n,m)=T(Go(n,m)) under the symmetric-square
    realization, Federer 3.2.28(4), p. 267.
    Source and image use the actual exterior and
    symmetric Hilbert products, without quotient defaults. *)
Theorem euclidean_grassmann_square_image (R:realType) n m:
  @euclidean_grassmann_square_set R n m=
    (@inner_projective_square R (exterior_power (R_n R n) m)) @`
    [set x|simple x /\exterior_norm (euclidean_two_nonzero R)
      (@euclidean_inner_productP R n) x= 1].
Proof.
apply/seteqP; split=>t.
- move=>[P [x [hs [hx [hP ht]]]]]; exists x; first by split.
  exact ht.
- move=>[x [hs hx] ht].
  have hn:x!=0 by apply/eqP=>hz; move:hx; rewrite hz exterior_norm_zero=>/eqP; by rewrite eq_sym oner_eq0.
  pose P:=associated_G (euclidean_two_nonzero R) (nonzero_simple_lift hn hs).
  exists P,x; split; first exact hs.
  split; first exact hx.
  split; last exact ht.
  by move=>v.
Qed.

(** Source for [euclidean_grassmann_smooth_submanifold]: the
    smooth manifold and dimension assertion for the square
    realization of G(n,m), Federer 3.2.28(4), p. 267.
    The actual orientation quotient, image identification,
    tangent isometry and same-chart smooth image theorem
    discharge the geometric assertions. *)
Theorem euclidean_grassmann_smooth_submanifold (R:realType) n m:
  (0<m)%N ->(m<=n)%N ->
  is_inner_smooth_submanifold
    (@symmetric_inner_form R (exterior_power (R_n R n) m)
      (@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
        (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m)
      (@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
        (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m) 2)
    (m*(n-m))%N (@euclidean_grassmann_square_set R n m).
Proof.
move=>hm hmn.
pose E:=exterior_power (R_n R n) m.
pose B:=@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m.
pose hB:=@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m.
pose A:set E:=[set x|simple x /\inner_norm hB x= 1].
have hb:=finite_ordinal_basis (@finite_e_lambda_basis R n (R_n R n)
  (@FiniteCoordinates.coordinate_basis R n) (@FiniteCoordinates.coordinate_basisP R n)
  (euclidean_two_nonzero R) m).
have hA:is_inner_smooth_submanifold B (m*(n-m))%N A:=
  @euclidean_oriented_grassmann_smooth_submanifold R m n hm hmn.
have hUnit x (hx:A x):inner_norm hB x= 1:=hx.2.
have hAnti x (hx:A x):A (-x).
  split.
  - have hs:=@simple_scale R (R_n R n) m x (-1) hm hx.1.
    by rewrite scaleN1r in hs.
  - by rewrite inner_normN; exact:hx.2.
have hSmooth:=@inner_projective_square_smooth_submanifold R E B hB _ _ hb
  (m*(n-m)) A hA hUnit hAnti.
rewrite euclidean_grassmann_square_image; exact hSmooth.
Qed.
