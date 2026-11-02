(** Federer (1969), 2.10.1, p. 170: supporting reduction of a
    fixed-open-cover infimum to the already established countable-cover
    laws. Assign infinite auxiliary cost to generators not refining the
    cover; every admissible cover retains its exact original cost. This is a
    proof device, not a change to the gauge. Source context, corrected
    reference and topological convention: OpenRefiningEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumSupport OpenRefiningEnvelopeUP CountableCoverEnvelopeUP
  CountableCoverEnvelopeLaws MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_refinement_cost]: auxiliary constraint
    encoding for the refined covering infimum in Federer
    2.10.1, p. 170. Only forbidden generators receive
    infinite auxiliary cost; all admissible costs are unchanged. *)
Definition open_refinement_cost (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X)) (j : J) :=
  if j \in [set j | generator_refines_cover S H j] then cost j else +oo.

(** Source for [open_refinement_cost_admissible_sum]: supporting
    exact cost preservation for the admissible refined covers
    in Federer 2.10.1, p. 170. *)
Lemma open_refinement_cost_admissible_sum (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X)) (G : set J) :
  (forall j, G j -> generator_refines_cover S H j) ->
  nonnegative_sum G (open_refinement_cost S cost H)=nonnegative_sum G cost.
Proof.
move=> hr; apply: nonnegative_sum_ext=> j hj.
by rewrite /open_refinement_cost (mem_set (hr j hj)).
Qed.

(** Source for [open_refinement_cost_sum_cases]: supporting
    alternative for the constraint encoding in Federer 2.10.1,
    p. 170. A family either refines the given cover, or
    one forbidden generator makes its auxiliary sum infinite. *)
Lemma open_refinement_cost_sum_cases (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X)) (G : set J) :
  ((forall j, G j -> generator_refines_cover S H j) /\
    nonnegative_sum G (open_refinement_cost S cost H)=nonnegative_sum G cost) \/
  nonnegative_sum G (open_refinement_cost S cost H)=+oo.
Proof.
case: (pselect (forall j, G j -> generator_refines_cover S H j))=> hr.
- left; split=> //; exact: open_refinement_cost_admissible_sum.
- right; have [j [hj hn]] : exists j, G j /\ ~ generator_refines_cover S H j.
    apply: contrapT=> hnone; apply: hr=> j hj; apply: contrapT=> hn.
    apply: hnone; by exists j.
  have hfalse : j \notin [set j | generator_refines_cover S H j].
    apply/negP=> hmem; exact: hn (set_mem hmem).
  have ht := @nonnegative_sum_term R J G (open_refinement_cost S cost H) j hj.
  rewrite /open_refinement_cost (negbTE hfalse) in ht.
  by apply/eqP; rewrite eq_le leey /=.
Qed.

(** Source for [open_refining_envelope_as_cover]: supporting
    equivalence of abstract infimum laws for the refined covers
    in Federer 2.10.1, p. 170. This holds for every
    function satisfying the specification, before selecting a witness. *)
Lemma open_refining_envelope_as_cover (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X)) (nu : set X -> \bar R) :
  is_open_refining_envelope S cost H nu ->
  is_countable_cover_envelope S (open_refinement_cost S cost H) nu.
Proof.
move=> hn; constructor.
- move=> A G hc hcov; case: (open_refinement_cost_sum_cases S cost H G)=> [[hr he]|he].
  + rewrite he; exact (@open_refining_envelope_lower R X J S cost H nu hn A G hc hr hcov).
  + by rewrite he leey.
- move=> A b hb; apply: (open_refining_envelope_greatest hn)=> G hc hr hcov.
  have h := hb G hc hcov.
  by rewrite (open_refinement_cost_admissible_sum cost hr) in h.
Qed.

(** Source for [cover_envelope_as_open_refining]: supporting
    converse equivalence for the refined-cover infimum of
    Federer 2.10.1, p. 170, used only to establish
    existence from the already proved fixed-family envelope. *)
Lemma cover_envelope_as_open_refining (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X)) (nu : set X -> \bar R) :
  is_countable_cover_envelope S (open_refinement_cost S cost H) nu ->
  is_open_refining_envelope S cost H nu.
Proof.
move=> hn; constructor.
- move=> A G hc hr hcov.
  have h := @countable_cover_envelope_lower R X J S (open_refinement_cost S cost H) nu hn A G hc hcov.
  by rewrite (open_refinement_cost_admissible_sum cost hr) in h.
- move=> A b hb; apply: (countable_cover_envelope_greatest hn)=> G hc hcov.
  case: (open_refinement_cost_sum_cases S cost H G)=> [[hr he]|he].
  + rewrite he; exact: hb G hc hr hcov.
  + by rewrite he leey.
Qed.

(** Source for [open_refining_envelope_is_measure]: supporting
    fixed-cover measure law for the alternative construction
    of Federer 2.10.1, p. 170. The existing summable-error
    covering proof applies independently of openness or topology. *)
Theorem open_refining_envelope_is_measure (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X)) (nu : set X -> \bar R) :
  is_open_refining_envelope S cost H nu -> (forall j, 0<=cost j) -> is_measure nu.
Proof.
move=> hn hc; apply: (countable_cover_envelope_is_measure (open_refining_envelope_as_cover hn)).
move=> j; rewrite /open_refinement_cost; case: ifP=> _; [exact: hc|exact: leey].
Qed.
