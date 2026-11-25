(** Federer (1969), 4.1.2, p. 347: the
    substitution z |-> x-z preserves the original
    Lebesgue measure. This reuses the translation and
    orthogonal invariance proved in 2.7.16. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanAdditiveGroup EuclideanLebesgueTranslation EuclideanLebesgueLinear IsometryGroupHaar MeasureUP MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_reflection_translation_measure]: the
    original substitution in the two convolution formulas
    preserves actual Lebesgue measure, Federer 4.1.2,
    p. 347. Dimension zero is retained. *)
Theorem euclidean_reflection_translation_measure (R:realType) n (x:R_n R n):
  measure_pushforward (fun z:R_n R n=>x-z) (@euclidean_lebesgue_measure R n)=
    @euclidean_lebesgue_measure R n.
Proof.
pose X:=R_n R n.
pose mu:=@euclidean_lebesgue_measure R n.
have hNeg:=@euclidean_orthogonal_pushforward R n (@negation_linear R n) (@negation_linear_orthogonal R n).
apply:funext=>S.
have hSet:[set z:X|S (x-z)]=(@negation_linear R n) @^-1` ((@euclidean_translation R n x) @^-1` S).
  apply:funext=>z; reflexivity.
change (mu [set z:X|S (x-z)]=mu S).
have hNegS:=hNeg ((@euclidean_translation R n x) @^-1` S).
change (mu ((@negation_linear R n) @^-1` ((@euclidean_translation R n x) @^-1` S))=
  mu ((@euclidean_translation R n x) @^-1` S)) in hNegS.
rewrite hSet hNegS.
exact:(congr1 (fun m=>m S) (@euclidean_lebesgue_translation_pushforward R n x)).
Qed.

(** Source for [euclidean_reflection_translation_involutive]: the
    original substitution is its own inverse, supporting
    Federer 4.1.2, p. 347. *)
Lemma euclidean_reflection_translation_involutive (R:realType) n (x:R_n R n):
  involutive (fun z:R_n R n=>x-z).
Proof. move=>z; by rewrite opprB addrCA subrr addr0. Qed.
