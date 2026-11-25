(** Federer (1969), 4.1.5, p. 349: a positive finite
    scalar factors through the original variation supremum.
    This adapter reuses the already proved extended-real
    scalar-supremum law rather than a new order construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import ExtendedSupremumUP ExtendedRealBounds PositiveScalarExtendedSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_value_supremum_embedded_laws]: the
    real value set of the gauge in Federer 4.1.5, p. 349,
    has the same supremum after finite extended-real inclusion,
    by the earlier 2.1.1 least-upper-bound laws. *)
Lemma real_value_supremum_embedded_laws (R:realType) (A:set R):
  is_extended_supremum A (extended_real_sup ((fun r:R=>r%:E) @` A)).
Proof.
constructor.
- move=>r hr; apply:extended_real_sup_upper; by exists r.
- move=>d hBound; apply:extended_real_sup_least=>z [r hr <-]; exact:(hBound r hr).
Qed.

(** Source for [real_value_supremum_embedding]: the unique
    gauge supremum equals the earlier abstract supremum of
    its finite image, supporting the scalar identity in
    Federer 4.1.5, p. 349. *)
Lemma real_value_supremum_embedding (R:realType) (A:set R) c:
  is_extended_supremum A c ->c=extended_real_sup ((fun r:R=>r%:E) @` A).
Proof.
move=>hC; exact:(extended_supremum_unique hC (real_value_supremum_embedded_laws A)).
Qed.

(** Source for [real_value_supremum_positive_scale]: positive
    scalar multiplication commutes with the original supremum,
    the identity ||S||(eta g)=eta ||S||(g) used in Federer
    4.1.5, p. 349. Infinite supremum values remain valid. *)
Theorem real_value_supremum_positive_scale (R:realType) (A:set R) c a:
  is_extended_supremum A c ->0<a ->
  is_extended_supremum ((fun r:R=>a*r) @` A) (a%:E*c)%E.
Proof.
move=>hC ha.
pose B:set R:=(fun r:R=>a*r) @` A.
have hImage:((fun r:R=>r%:E) @` B)=
    (fun z: \bar R=>(a%:E*z)%E) @` ((fun r:R=>r%:E) @` A).
  apply/seteqP; split.
  - move=>z [r [t ht <-] <-].
    exists t%:E; first by exists t.
    by rewrite EFinM.
  - move=>z [w [t ht <-] <-].
    exists (a*t); first by exists t.
    by rewrite EFinM.
have hSup:extended_real_sup ((fun r:R=>r%:E) @` B)=(a%:E*c)%E.
  rewrite hImage (@extended_real_sup_positive_scalar R ((fun r:R=>r%:E) @` A) a ha).
  by rewrite -(real_value_supremum_embedding hC).
have hLaws:=real_value_supremum_embedded_laws B.
by rewrite hSup in hLaws.
Qed.
