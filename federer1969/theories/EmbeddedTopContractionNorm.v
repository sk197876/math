(** Federer (1969), 1.7.11, p. 36: supporting identification of the
    top-target operator norm with a contraction in an ambient product space.
    It combines 1.7.6, p. 34, 1.7.8, p. 34, and the contraction naturality
    used in 1.6.5. Source context: ProductInnerUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP OrthogonalMaps ExteriorNorm
  ExteriorNormNaturality ExteriorCovectorInner ExteriorOperatorNorm
  TopTargetExteriorNorm UpperDualityNorm InteriorNaturality DualityMaps
  LeftInterior ExteriorGrading ExteriorMaps ExteriorMapScaling
  AlternatingCoordinates AlternatingDual AlternatingPairing LinearBasis TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [embedded_top_contraction_norm]: Federer
    1.7.11, p. 36, supporting norm reduction: for an orthogonal
    inclusion i and f=g composed with i, contraction of i's image
    of a unit source volume by g's pullback of a unit target form
    has norm equal to the top-target exterior operator norm of f. *)
Theorem embedded_top_contraction_norm (R : realType) (h2 : (1+1 : R) != 0)
    (U V W : lmodType R) (A : U -> U -> R) (B : V -> V -> R)
    (C : W -> W -> R) (hA : is_inner_product A)
    (hB : is_inner_product B) (hC : is_inner_product C)
    q n (b : 'I_q -> U) (e : 'I_n -> V) (hb : is_basis b) (he : is_basis e)
    (hn : (n <= q)%N) (i : {linear U -> W}) (hi : is_orthogonal_map A C i)
    (f : {linear U -> V}) (g : {linear W -> V}) (hf : forall x, f x = g (i x))
    (E : exterior_power U q) (hE : exterior_norm h2 hA E = 1)
    (omega : A_m V R^o n) (ho : exterior_covector_norm h2 hB he omega = 1) :
  exterior_operator_norm h2 hA hB hb f n =
    exterior_norm h2 hC
      (left_interior h2 hn (exterior_power_map i q E) (A_m_dual g omega)).
Proof.
have hpull : A_m_dual f omega = A_m_dual i (A_m_dual g omega).
  apply: pairing_ext => z; rewrite !A_m_dual_pairing.
  congr (pairing _ omega).
  rewrite exterior_power_map_composition.
  exact (@exterior_power_map_ext R U V f (linear_comp g i) hf n z).
rewrite (@top_target_operator_unit_value R h2 U V A B hA hB q n b e hb he f omega ho).
rewrite -(@upper_duality_norm R h2 U A hA q b hb E hE n hn) hpull /D_upper.
rewrite -(@exterior_norm_orthogonal_natural R h2 U W A C hA hC i hi
  (q-n) (left_interior h2 hn E (A_m_dual i (A_m_dual g omega)))).
by rewrite left_interior_natural.
Qed.
