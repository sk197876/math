(** Federer (1969), 4.1.1, p. 346: integration
    of the test pairing defines a real linear
    functional. This supporting existence proof
    reuses uniqueness and the original finite
    real sum and scale integral laws of 2.4.4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import Hom MeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section IntegralLinearMapExistence.
Variable R:realType.
Variable X:choiceType.
Variable E:lmodType R.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Variable F:E->X->R.
Hypothesis hF:forall c f g x,F (c*:f+g) x=c*F f x+F g x.
Hypothesis hFinite:forall f:E,exists c:R,is_measure_integral mu (real_total_integrand (F f)) c%:E.

(** Source for [real_integral_linear_candidate]: private
    choice of each proved finite integral value,
    supporting the functional in Federer 4.1.1,
    p. 346. *)
Definition real_integral_linear_candidate f:R^o:=projT1 (cid (hFinite f)).

(** Source for [real_integral_linear_candidate_integral]:
    the chosen value is the actual integral,
    supporting Federer 4.1.1, p. 346. *)
Lemma real_integral_linear_candidate_integral f:
  is_measure_integral mu (real_total_integrand (F f)) (real_integral_linear_candidate f)%:E.
Proof. exact:(projT2 (cid (hFinite f))). Qed.

(** Source for [real_integral_linear_candidate_linear]: the
    integral pairing is linear in the test,
    supporting Federer 4.1.1, p. 346. *)
Lemma real_integral_linear_candidate_linear:linear real_integral_linear_candidate.
Proof.
move=>c f g.
have hScale:=@real_total_integral_scale R X mu hm (F f) (real_integral_linear_candidate f) c
  (real_integral_linear_candidate_integral f).
have hSum:=@real_total_integral_add R X mu hm (fun x=>c*F f x) (F g)
  (c*real_integral_linear_candidate f) (real_integral_linear_candidate g) hScale
  (real_integral_linear_candidate_integral g).
have hEq:(fun x=>c*F f x+F g x)=F (c*:f+g) by apply:funext=>x; symmetry; exact:hF.
rewrite hEq in hSum.
have hUnique:=measure_integral_unique (real_integral_linear_candidate_integral (c*:f+g)) hSum.
exact:(congr1 (@fine R) hUnique).
Qed.

(** Source for [real_integral_linear_map_exists]: there
    exists a real linear map with exactly the
    original integral values, supporting the
    distribution in Federer 4.1.1, p. 346. *)
Theorem real_integral_linear_map_exists:
  exists T:Hom E R^o,forall f:E,is_measure_integral mu (real_total_integrand (F f)) (T f)%:E.
Proof.
exists (@HomMap R E R^o real_integral_linear_candidate
  (introT (asboolP _) real_integral_linear_candidate_linear)).
exact:real_integral_linear_candidate_integral.
Qed.
End IntegralLinearMapExistence.
