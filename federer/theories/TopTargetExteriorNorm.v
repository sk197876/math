(** Federer (1969), 1.7.6, p. 34: top-target exterior norm, evaluation on
    unit top covectors, and surjectivity. The proofs reduce to the
    source-top assertions by the adjoint and the gamma isometries. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorIsomorphism
  ExteriorCovectorInner ExteriorNorm ExteriorMaps ExteriorGrading
  AlternatingCoordinates AlternatingDual LinearBasis Adjoint AdjointUP
  AdjointSurjectivity ExteriorAdjoint ExteriorOperatorNorm
  TopExteriorNorm TopExteriorInjectivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section TopTarget.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variables n k : nat.
Variable b : 'I_n -> V.
Variable e : 'I_k -> U.
Hypothesis hb : is_basis b.
Hypothesis he : is_basis e.
Variable f : {linear V -> U}.

(** Source for [top_target_operator_unit_value]: Federer
    1.7.6, p. 34, when the degree equals the target dimension,
    the exterior operator norm equals the norm of the pullback
    of every unit top-degree covector on the target. *)
Theorem top_target_operator_unit_value (phi : A_m U R^o k)
    (hphi : exterior_covector_norm h2 hC he phi = 1) :
  exterior_operator_norm h2 hB hC hb f k =
    exterior_covector_norm h2 hB hb (A_m_dual f phi).
Proof.
pose a := inner_adjoint hB hC hb f.
have ha : is_adjoint B C f a := inner_adjointP hB hC hb f.
have [g [_ hg]] := @inner_exterior_inverse_exists R h2 U C hC k e he k.
pose x := g phi.
have hx : inner_exterior_form h2 hC x = phi := hg phi.
have hu : exterior_norm h2 hC x = 1.
  by rewrite -(@inner_exterior_form_norm R h2 U C hC k e he k x) hx.
rewrite (@exterior_operator_adjoint_norm_equal R h2 V U B C hB hC n k b e hb he f a ha k).
rewrite (@top_exterior_operator_unit_value R h2 U V C B hC hB k e he a x hu).
rewrite -hx (@adjoint_inner_exterior_form_diagram R h2 V U B C hB hC f a ha k x).
by rewrite inner_exterior_form_norm.
Qed.

(** Source for [top_target_norm_positive_iff_surjective]: Federer
    1.7.6, p. 34, ||exterior_k f|| > 0 iff f is an
    epimorphism, where k is the target dimension. *)
Theorem top_target_norm_positive_iff_surjective :
  0 < exterior_operator_norm h2 hB hC hb f k <-> forall y, exists x, f x = y.
Proof.
pose a := inner_adjoint hB hC hb f.
have ha : is_adjoint B C f a := inner_adjointP hB hC hb f.
rewrite (@exterior_operator_adjoint_norm_equal R h2 V U B C hB hC n k b e hb he f a ha k).
apply: iff_trans (@top_exterior_norm_positive_iff_injective R h2 U V C B hC hB k e he a) _.
exact (@adjoint_injective_iff_surjective R V U B C hB hC n b hb f a ha).
Qed.
End TopTarget.
