(** Federer (1969), 1.6.5, pp. 25-26, the complete product-space
    contraction identity. The proof covers all Grassmann basis
    pairs by a four-block partition and extends by bilinearity.
    The full-algebra version permits any top form and all input
    degrees. The displayed degree-specific version uses the
    normalised dual bases of 1.5.2 and explicitly states the bounds
    needed for its duality maps. No transversality or simplicity
    hypothesis is imposed on the final inputs. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors ProductBasisIdentity BilinearBasisExt
  ProductContractionAlgebra ProductContraction DualProductContraction ProductSpaceMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [product_space_contraction_hom]: Federer 1.6.5,
    pp. 25-26, the displayed identity after the inverse-duality
    reduction on p. 26. Direct full-algebra formulation for every
    pair of homogeneous multivectors and any top form. Includes
    degrees above the ambient dimension, where the inputs vanish. *)
Theorem product_space_contraction_hom (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  (phi : A_m V K^o n) k l (xi : exterior_power V k) (eta : exterior_power V l) :
  product_contraction_hom h2 (form_homogeneous phi) (component_val xi) (component_val eta) =
  (-1 : K)^+((n-k) * l) *:
    diagonal_contraction_hom h2 (form_homogeneous phi) (component_val xi) (component_val eta).
Proof.
pose f (x : exterior_power V k) (y : exterior_power V l) :=
  product_contraction_hom h2 (form_homogeneous phi) (component_val x) (component_val y).
pose g (x : exterior_power V k) (y : exterior_power V l) :=
  (-1 : K)^+((n-k) * l) *:
    diagonal_contraction_hom h2 (form_homogeneous phi) (component_val x) (component_val y).
have hf : bilinear f.
  split.
  - move=> y c x z; rewrite /f linearP
      (proj1 (product_contraction_hom_bilinear h2 (form_homogeneous phi))); by [].
  - move=> x c y z; rewrite /f linearP
      (proj2 (product_contraction_hom_bilinear h2 (form_homogeneous phi))); by [].
have hg : bilinear g.
  split.
  - move=> y c x z; rewrite /g (linearP (@component_val _ _ _ _))
      (proj1 (diagonal_contraction_hom_bilinear h2 (form_homogeneous phi))) !linearP; by [].
  - move=> x c y z; rewrite /g (linearP (@component_val _ _ _ _))
      (proj2 (diagonal_contraction_hom_bilinear h2 (form_homogeneous phi))) !linearP; by [].
apply: (@bilinear_basis_ext K (Choice.clone (Lambda n k) _) (Choice.clone (Lambda n l) _)
  (exterior_power V k) (exterior_power V l)
  (exterior_space (GRing.Lmodule.clone K (V * V)%type _))
  (@finite_e_lambda K n V e k) (@finite_e_lambda K n V e l)
  (finite_e_lambda_basis he h2 k) (finite_e_lambda_basis he h2 l) f g hf hg) xi eta => a b.
rewrite /f /g /finite_e_lambda !e_lambdaE.
exact: basis_pair_product_identity.
Qed.

(** Source for [product_space_contraction]: Federer 1.6.5,
    p. 25, main displayed identity with D^ and D_. Direct theorem
    in degree k+l-n, with the printed sign (-1)^((n-k)l).
    The bounds k,l<=n make explicit the domain of the duality maps
    introduced in 1.5.2; the full-algebra theorem also covers higher
    input degrees. The zero-dimensional case is included. *)
Theorem product_space_contraction (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (omega : 'I_n -> A_m V K^o 1)
  (he : is_basis e) (hd : forall i j, omega i [tuple e j] = if i == j then 1 else 0)
  k l (hk : (k <= n)%N) (hl : (l <= n)%N) (hkl : (n <= k+l)%N)
  (xi : exterior_power V k) (eta : exterior_power V l) :
  FedererProductContraction.product_contraction h2 hkl
    (omega_lambda h2 omega (Lambda_top n)) xi eta =
  FedererProductContraction.diagonal_dual_product h2 hk hl hkl
    (omega_lambda h2 omega (Lambda_top n)) (e_lambda e (val (Lambda_top n))) xi eta.
Proof.
apply: val_inj.
rewrite /FedererProductContraction.product_contraction
  /FedererProductContraction.diagonal_dual_product linearZ.
change (left_interior_hom h2
  (wedge (exterior_algebra_map (FedererProduct.P_map V) (component_val xi))
    (exterior_algebra_map (FedererProduct.Q_map V) (component_val eta)))
  (form_homogeneous (A_m_dual (FedererProduct.f_map V)
    (omega_lambda h2 omega (Lambda_top n)))) =
  (-1 : K)^+((n-k) * l) *:
  exterior_algebra_map (FedererProduct.g_map V)
    (component_val (exterior_reindex (product_contraction_degree hk hl)
      (D_upper h2 (e_lambda e (val (Lambda_top n))) (product_contraction_bound hk hl hkl)
        (form_wedge h2 (scalar_bilinear K)
          (D_p (omega_lambda h2 omega (Lambda_top n)) hk xi)
          (D_p (omega_lambda h2 omega (Lambda_top n)) hl eta)))))).
rewrite exterior_reindexE (@dual_product_contraction K h2 V n e omega he hd)
  form_pullback_hom.
have hh : (form_homogeneous (D_p (omega_lambda h2 omega (Lambda_top n)) hl eta)
    : Hom (exterior_space V) K^o) =
  right_interior_hom (component_val eta) (form_homogeneous (omega_lambda h2 omega (Lambda_top n))).
  apply: hom_ext => x; exact: D_pE.
rewrite hh.
exact: (@product_space_contraction_hom K h2 V n e he
  (omega_lambda h2 omega (Lambda_top n)) k l xi eta).
Qed.

(** Source for [product_space_volume_change]: Federer 1.6.5,
    p. 25, sentence following the main display: both members
    acquire the determinant factor under change of dual bases.
    Direct functional formulation: pulling the top form back by
    an endomorphism f multiplies both reduced members by det(f).
    This also holds for noninvertible f; an automorphism gives the
    stated change of basis. The convention is pullback of forms. *)
Theorem product_space_volume_change (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  (f : {linear V -> V}) (phi : A_m V K^o n) x y :
  product_contraction_hom h2 (form_homogeneous (A_m_dual f phi)) x y =
    det h2 he f *: product_contraction_hom h2 (form_homogeneous phi) x y /\
  diagonal_contraction_hom h2 (form_homogeneous (A_m_dual f phi)) x y =
    det h2 he f *: diagonal_contraction_hom h2 (form_homogeneous phi) x y.
Proof.
have hp : (form_homogeneous (A_m_dual f phi) : Hom (exterior_space V) K^o) =
    det h2 he f *: (form_homogeneous phi : Hom (exterior_space V) K^o).
  apply: hom_ext => z.
  by rewrite (A_m_dual_det h2 he) linearZ hom_m_scaleE.
rewrite hp; split.
- exact: (linZ (product_contraction_volume_linear h2 x y)).
- exact: (linZ (diagonal_contraction_volume_linear h2 x y)).
Qed.
