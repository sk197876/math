(** Federer (1969), 1.8.4, pp. 40-41: the product
    pairing factors when the first covectors are dual to the first
    vector factors and annihilate the subspace supporting the second
    multivector. This supporting algebraic identity includes empty
    degrees and arbitrary vector spaces. Its contraction calculation
    is the block rule already proved for 1.6.5, p. 26. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors ExteriorAlgebra ExteriorGrading ExteriorMaps
  ExteriorHomogeneousProducts FiniteExteriorPowers AlternatingProduct CovectorProducts
  HomogeneousHom AlternatingExtension LeftInteriorHom InteriorBlock ExteriorExpansion Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Pairing.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables U V : lmodType K.
Variable f : {linear U -> V}.
Variable p : nat.
Variable e : 'I_p -> V.
Variable a : 'I_p -> A_m V K^o 1.
Hypothesis hd : forall i j, one_hom (a i) (e j) = if i == j then 1 else 0.
Hypothesis hz : forall i u, one_hom (a i) (f u) = 0.
Local Notation alpha := (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) a).
Local Notation volume := (e_lambda e (ord_tuple p)).

(** Source for [annihilating_block_contraction]: Federer 1.8.4,
    pp. 40-41, supporting contraction computation for a full
    multivector in the annihilated subspace, rather than just a
    decomposable second factor. *)
Theorem annihilating_block_contraction q (y : exterior_power U q) :
  left_interior_hom h2
    (wedge (component_val volume) (exterior_algebra_map f (component_val y)))
    (form_homogeneous alpha) = exterior_algebra_map f (component_val y).
Proof.
apply: (@exterior_component_induction K U q (fun z =>
  left_interior_hom h2 (wedge (component_val volume) (exterior_algebra_map f z))
    (form_homogeneous alpha) = exterior_algebra_map f z))
  (component_homogeneous y) => [|z t hzt htt|c z hzt|s hs].
- by rewrite linear0 (bil0r (wedge_bilinear V)) (bil0l (left_interior_hom_bilinear h2 V)).
- by rewrite linearD (bilDr (wedge_bilinear V))
    (bilDl (left_interior_hom_bilinear h2 V)) hzt htt.
- by rewrite linearZ (bilZr (wedge_bilinear V))
    (bilZl (left_interior_hom_bilinear h2 V)) hzt.
- rewrite exterior_algebra_map_word e_lambdaE.
  pose t : q.-tuple U := Tuple (introT eqP hs).
  have hseq : [seq f (tnth t i) | i <- enum 'I_q] = map f s.
    by rewrite (map_comp f (tnth t)) map_tnth_enum.
  rewrite -hseq.
  exact: (@interior_dual_block K h2 V p q e (fun i => f (tnth t i)) a hd
    (fun i j => hz i (tnth t j))).
Qed.

(** Source for [annihilating_block_pairing]: Federer 1.8.4,
    p. 41, the displayed product pairing after the first block
    has been normalised to pair to one. No simplicity is required
    of the second multivector or second covector. *)
Theorem annihilating_block_pairing q (y : exterior_power U q)
    (psi : A_m V K^o q) :
  pairing (exterior_product volume (exterior_power_map f q y))
    (form_wedge h2 (scalar_bilinear K) alpha psi) =
  pairing (exterior_power_map f q y) psi.
Proof.
change (form_homogeneous (form_wedge h2 (scalar_bilinear K) alpha psi)
  (component_val (exterior_product volume (exterior_power_map f q y))) =
  form_homogeneous psi (exterior_algebra_map f (component_val y))).
rewrite exterior_productE /form_wedge homogeneous_formK -left_interior_diagram.
by rewrite annihilating_block_contraction.
Qed.
End Pairing.
