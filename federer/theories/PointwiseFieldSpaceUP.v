(** Federer (1969), 4.1.6, p. 351: forms and multivector
    fields form vector spaces with pointwise operations.
    This independent evaluation specification applies to
    either original fibre. A function model proves existence
    separately, and its carrier is then sealed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_pointwise_field_space]: the vector spaces
    of all fibre-valued functions in Federer 4.1.6,
    p. 351, specified by pointwise linear evaluation and
    exact representation of every original function. *)
Record is_pointwise_field_space (K:fieldType) (X:choiceType)
    (Y E:lmodType K) (ev:Hom E (GRing.Lmodule.clone K (X->Y) _)):Prop:={
  (** Source for [pointwise_field_extensional]: equality of
      the original functions is equality at every point,
      Federer 4.1.6, p. 351. *)
  pointwise_field_extensional:forall f g,(forall x,ev f x=ev g x)->f=g;
  (** Source for [pointwise_field_represents]: every original
      fibre-valued map is a form or field, according to
      its fibre, Federer 4.1.6, p. 351. *)
  pointwise_field_represents:forall f:X->Y,exists e:E,forall x,ev e x=f x
}.

(** Source for [pointwise_field_linear_values]: the pointwise
    vector operations in Federer 4.1.6, p. 351,
    follow from the evaluation Hom, independently of a
    model of the field space. *)
Lemma pointwise_field_linear_values (K:fieldType) (X:choiceType)
    (Y E:lmodType K) (ev:Hom E (GRing.Lmodule.clone K (X->Y) _)) c f g x:
  ev (c*:f+g) x=c*:ev f x+ev g x.
Proof. exact:(congr1 (fun h:X->Y=>h x) (linearP ev c f g)). Qed.
