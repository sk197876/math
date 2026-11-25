(** Federer (1969), 1.7.12, pp. 36-37: supporting degree-two coefficient
    computation for the first trace identity. The book compares coefficients
    using 1.4.5; here its alternating degree-two coefficient is evaluated
    first on two rank-one tensors. This is the two-by-two determinant from
    1.4.2, pp. 18-19. The local erratum has no correction to pp. 36-37. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TraceAlgebra TraceDefinition TraceBasisProduct
  OneFormIdentification OneFormCommutator ExteriorPowers ExteriorGrading
  ExteriorAlgebra AlternatingAlgebra AlternatingUnit ScalarCoefficients
  AlternatingCoordinates Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [trace_two_rank_one]: Federer 1.7.12,
    pp. 36-37, supporting degree-two coefficient: the trace
    of the product of two rank-one degree-one tensors is the
    determinant of their two-by-two pairing matrix. *)
Lemma trace_two_rank_one (K : fieldType) (h2 : (1+1 : K) != 0)
    (V : lmodType K) (a b : A_m V K^o 1) (v w : V) :
  trace h2 V (alg_mul (A h2 V V)
    (A_pure h2 a (exterior_first_inclusion V v))
    (A_pure h2 b (exterior_first_inclusion V w))) =
  (one_hom a v : K) * (one_hom b w : K) -
    (one_hom a w : K) * (one_hom b v : K).
Proof.
rewrite trace_pure_product.
change (alternating_wedge h2 (scalar_bilinear K) (form_include a) (form_include b)
  (wedge (exterior_degree 1 (exterior_generator v))
    (exterior_degree 1 (exterior_generator w))) =
  (one_hom a v : K) * (one_hom b w : K) -
    (one_hom a w : K) * (one_hom b v : K)).
rewrite !exterior_generator_homogeneous.
have ha : form_include a = one_generator (one_hom a) by rewrite /one_generator one_homK.
have hb : form_include b = one_generator (one_hom b) by rewrite /one_generator one_homK.
rewrite ha hb.
have hh := (@one_forms_wedge_two K h2 V K^o (fun x y : K^o => (x : K) * (y : K))
  (scalar_bilinear K) (one_hom a) (one_hom b) v w).
by rewrite !exterior_word_cons exterior_word_nil wedge_unitr in hh.
Qed.
