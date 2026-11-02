(** Federer (1969), 2.5.16, p. 110: private realisation of the space E of
    all bounded real valued continuous functions on a metric space Y by a
    subtype of the real valued functions on Y, with nu(f) = sup im |f|
    computed as the supremum of the values |f(w)| together with 0. This
    construction only proves existence of the specification in
    BoundedContinuousSpaceUP.v; later proofs use its sealed laws. Source
    context: BoundedContinuousSpaceUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  topology normedtype.
From Federer Require Import MetricBoundedContinuousEmbedding UniformFunctionNormUP BoundedContinuousSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Construction.
Variable R : realType.
Variable Y : metricType R.
Local Notation F := (GRing.Lmodule.clone R (Y -> R^o) _).

(** Source for [bounded_continuous_pred]: boolean subtype predicate
    for the private realisation of E in Federer 2.5.16, p. 110. *)
Definition bounded_continuous_pred (f : F) := `[< bounded_continuous_functions f >].

(** Source for [BoundedContinuousFunction]: actual-function
    realisation proving existence of E, Federer 2.5.16, p. 110. *)
Record BoundedContinuousFunction := BoundedContinuousFunctionMap {
  (** Source for [bounded_continuous_value]: the evaluation map of
      E, Federer 2.5.16, p. 110. *)
  bounded_continuous_value : Y -> R;
  (** Source for [bounded_continuous_membership]: membership in E,
      Federer 2.5.16, p. 110. *)
  bounded_continuous_membership : bounded_continuous_pred bounded_continuous_value
}.

(** Source for [bounded_continuous_rect]: subtype eliminator
    supporting the vector-space realisation of Federer 2.5.16,
    p. 110; not a separate assertion of the book. *)
Definition bounded_continuous_rect (P : BoundedContinuousFunction -> Type)
    (h : forall f hf, P (@BoundedContinuousFunctionMap f hf)) (z : BoundedContinuousFunction) : P z :=
  match z as z' return P z' with @BoundedContinuousFunctionMap f hf => h f hf end.

HB.instance Definition _ := [isSub for bounded_continuous_value by bounded_continuous_rect].
HB.instance Definition _ := [Choice of BoundedContinuousFunction by <:].

(** Source for [bounded_continuous_closed]: the bounded continuous
    real functions form a vector space under the pointwise operations,
    Federer 2.5.16, p. 110. *)
Lemma bounded_continuous_closed : GRing.submod_closed bounded_continuous_pred.
Proof.
split.
- apply/asboolP; split; first by move=> y; exact: cvg_cst.
  by exists 0=> w; rewrite normr0.
- move=> c f g /asboolP [hf [M hM]] /asboolP [hg [K hK]]; apply/asboolP.
  change (bounded_continuous_functions (fun y => c * f y + g y)); split.
  + move=> y.
    have hcf : {for y, continuous (fun z : Y => c * f z : R^o)}.
      apply: (@continuousM R Y (fun _ => c) f y); last exact: hf.
      exact: cvg_cst.
    exact: (@continuousD R R^o Y (fun z => c * f z) g y hcf (hg y)).
  + exists (`|c| * M + K)=> w; apply: le_trans (ler_normD _ _) _.
    by rewrite normrM; apply: lerD; [apply: ler_wpM2l | exact: hK].
Qed.

HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build R F
  bounded_continuous_pred BoundedContinuousFunction bounded_continuous_closed.

(** Source for [bounded_continuous_norm_values]: the set of values
    |f(w)|, together with 0, whose supremum is nu(f) = sup im |f| in
    Federer 2.5.16, p. 110; the value 0 accounts for an empty Y. *)
Definition bounded_continuous_norm_values (f : BoundedContinuousFunction) : set R :=
  [set `|bounded_continuous_value f w| | w in [set: Y]] `|` [set 0].

(** Source for [bounded_continuous_norm]: private realisation of the
    norm nu(f) = sup im |f| of Federer 2.5.16, p. 110. *)
Definition bounded_continuous_norm (f : BoundedContinuousFunction) : R :=
  sup (bounded_continuous_norm_values f).

(** Source for [bounded_continuous_norm_has_sup]: supporting
    existence of the supremum defining nu in Federer 2.5.16,
    p. 110. *)
Lemma bounded_continuous_norm_has_sup f : has_sup (bounded_continuous_norm_values f).
Proof.
have [_ [M hM]] := elimT (asboolP _) (bounded_continuous_membership f).
split; first by exists 0; right.
exists `|M|=> _ [[w _ <-]|->]; last exact: normr_ge0.
exact: le_trans (hM w) (ler_norm M).
Qed.

(** Source for [bounded_continuous_norm_laws]: the realised norm
    satisfies the least-bound specification of nu, Federer 2.5.16,
    p. 110. *)
Lemma bounded_continuous_norm_laws f :
  is_uniform_function_norm (bounded_continuous_value f) (bounded_continuous_norm f).
Proof.
have hs := bounded_continuous_norm_has_sup f.
rewrite /bounded_continuous_norm; constructor.
- by apply: (sup_upper_bound hs); right.
- by move=> w; apply: (sup_upper_bound hs); left; exists w.
- move=> c hc hb; apply: ge_sup; first exact: hs.1.
  by move=> _ [[w _ <-]|->].
Qed.

(** Source for [bounded_continuous_space_witness]: verified existence
    of the abstract laws of E, Federer 2.5.16, p. 110, including the
    case of an empty Y. *)
Lemma bounded_continuous_space_witness :
  is_bounded_continuous_space bounded_continuous_value bounded_continuous_norm.
Proof.
constructor.
- by move=> c f g y.
- move=> f; exact: (elimT (asboolP _) (bounded_continuous_membership f)).
- exact: val_inj.
- move=> f hf; exists (@BoundedContinuousFunctionMap f (introT (asboolP _) hf)); by [].
- exact: bounded_continuous_norm_laws.
Qed.

End Construction.
