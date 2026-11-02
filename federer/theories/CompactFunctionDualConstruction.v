(** Federer (1969), 2.5.20, p. 114: private witness for the identification
    of continuous linear functionals on E=K(Y) with Daniell integrals.
    Evaluation is inverted only on K(Y); existence and uniqueness there
    follow from the abstract function-space laws. Source context:
    CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP CompactSupportFunctionUP CompactFunctionSpaceUP
  CompactFunctionSpaceLaws CompactFunctionDualUP CompactUniformNorm UniformFunctionNorm UniformFunctionNormUP
  VectorDaniellHypotheses VectorDaniellDualExtension DaniellIntegralUP
  DaniellSpaceWeakTopology DaniellSpaceCompactSpace FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Construction.
Variable R : realType.
Variable Y : topologicalType.
Variable E : lmodType R.
Variable ev : E -> Y -> R.
Hypothesis hv : is_compact_function_space ev.
Hypothesis hh : hausdorff_space Y.
Hypothesis hc : compact (@setT Y).
Local Notation K := (@compactly_supported_continuous_functions R Y).
(** Source for [N]: the uniform norm in Federer 2.5.20, p. 114. *)
Let N := @compact_function_norm R Y E ev.
(** Source for [hN]: norm laws for the conjugate-space
    identification in Federer 2.5.20, p. 114. *)
Let hN := compact_function_norm_laws hv.

(** Source for [compact_function_decode]: private inverse to
    the evaluation bijection E=K(Y), supporting Federer
    2.5.20, p. 114. The zero value outside K(Y)
    is only a total-function convention. *)
Definition compact_function_decode (f : Y -> R) : E :=
  match pselect (K f) with
  | left hf => sval (cid (compact_function_evaluation_surjective hv hf))
  | right _ => 0
  end.

(** Source for [compact_function_decode_evaluation]: the inverse
    recovers every vector of E=K(Y), Federer 2.5.20, p. 114. *)
Lemma compact_function_decode_evaluation v : compact_function_decode (ev v)=v.
Proof.
rewrite /compact_function_decode; case: pselect=> hf.
- apply: (@compact_function_evaluation_injective R Y E ev hv _ v).
  exact: svalP (cid (compact_function_evaluation_surjective hv hf)).
- exfalso; apply: hf; exact (@compact_function_evaluation_member R Y E ev hv v).
Qed.

(** Source for [compact_function_decode_member]: the inverse
    represents every member of K(Y), Federer 2.5.20, p. 114. *)
Lemma compact_function_decode_member f : K f -> ev (compact_function_decode f)=f.
Proof.
move=> hf; have [v <-] := compact_function_evaluation_surjective hv hf.
by rewrite compact_function_decode_evaluation.
Qed.

(** Source for [compact_function_dual_witness]: actual functional
    corresponding to an element of E*, Federer 2.5.20,
    p. 114. It is exposed only through the sealed laws. *)
Definition compact_function_dual_witness (a : weak_dual_space hN) : daniell_weak_space K :=
  fun f => val a (compact_function_decode f).

(** Source for [compact_function_dual_witness_evaluation]: the
    pairing is preserved, Federer 2.5.20, p. 114. *)
Lemma compact_function_dual_witness_evaluation a v :
  compact_function_dual_witness a (ev v)=val a v.
Proof. by rewrite /compact_function_dual_witness compact_function_decode_evaluation. Qed.

(** Source for [compact_function_dual_witness_linear]: supporting
    linearity on K(Y), Federer 2.5.20, p. 114,
    by the vector-space isomorphism E=K(Y). *)
Lemma compact_function_dual_witness_linear a :
  is_linear_functional_on_functions K (compact_function_dual_witness a).
Proof.
split.
- move=> f g hf hg.
  have [u <-] := compact_function_evaluation_surjective hv hf.
  have [v <-] := compact_function_evaluation_surjective hv hg.
  rewrite -(compact_function_evaluation_add hv) !compact_function_dual_witness_evaluation.
  exact: dual_space_add _ _ (set_valP a).
- move=> c f hf; have [v <-] := compact_function_evaluation_surjective hv hf.
  rewrite -(compact_function_evaluation_scale hv) !compact_function_dual_witness_evaluation.
  exact: dual_space_scale _ _ (set_valP a).
Qed.

(** Source for [compact_function_dual_witness_bounded]: the
    conjugate functional is bounded in the uniform norm,
    supporting the Daniell assertion in Federer 2.5.20,
    p. 114, by 2.5.19, p. 113. *)
Lemma compact_function_dual_witness_bounded a :
  is_sup_norm_bounded (compact_function_dual_witness a).
Proof.
have [C [hC hb]] := dual_space_bounded (set_valP a).
exists C; split=> // f hf c hc0 hfc.
have [v hev] := compact_function_evaluation_surjective hv hf.
have hvc : forall y, `|ev v y|<=c by move=> y; rewrite hev; exact: hfc.
rewrite -hev compact_function_dual_witness_evaluation; apply: le_trans (hb v) _.
have hn : compact_function_norm ev v<=c :=
  @uniform_function_norm_least R Y (ev v) (compact_function_norm ev v)
    (compact_support_uniform_norm_specification
      (@compact_function_evaluation_member R Y E ev hv v)) c hc0 hvc.
exact (ler_wpM2l hC hn).
Qed.

(** Source for [compact_function_dual_witness_daniell]: every
    element of E* supplies an actual Daniell integral on K(Y),
    Federer 2.5.20, p. 114, by the compact-space
    criterion of 2.5.19, p. 113. *)
Lemma compact_function_dual_witness_daniell a :
  is_daniell_integral K (compact_function_dual_witness a).
Proof.
exact: (@sup_norm_bounded_daniell R Y hh hc _
  (compact_function_dual_witness_linear a) (compact_function_dual_witness_bounded a)).
Qed.

(** Source for [compact_function_dual_witness_continuous]:
    weak continuity follows by evaluating at each member of
    K(Y), supporting measurability in Federer 2.5.20,
    p. 114; the generating topologies are in 2.5.12(2),
    p. 103, and 2.5.19, p. 113. *)
Lemma compact_function_dual_witness_continuous : continuous compact_function_dual_witness.
Proof.
move=> a.
have hF : Filter (compact_function_dual_witness @ nbhs a) := fmap_filter _ (nbhs_filter a).
apply/(daniell_weak_cvg K _ hF)=> f hf.
exact: (@weak_dual_evaluation_continuous R E N hN (compact_function_decode f) a).
Qed.

(** Source for [compact_function_dual_identification_exists]:
    verified existence of the abstract identification used in
    Federer 2.5.20, p. 114, including weak continuity. *)
Theorem compact_function_dual_identification_exists :
  exists F, @is_compact_function_dual_identification R Y E N hN ev F.
Proof.
exists compact_function_dual_witness; constructor.
- exact: compact_function_dual_witness_evaluation.
- exact: compact_function_dual_witness_daniell.
- exact: compact_function_dual_witness_continuous.
Qed.
End Construction.
