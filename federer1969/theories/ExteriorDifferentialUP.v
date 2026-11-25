(** Federer (1969), 4.1.6, p. 352: independent
    characteristic laws of exterior differentiation.
    The original signed omission of the i-th argument
    specifies the alternating value of an actual first
    differential. Its existence and opaque value are
    proved and chosen in separate modules. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom ExteriorGrading FiniteExteriorPowers AlternatingForms AlternatingPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_omitted_tuple]: the original
    tuple with its i-th argument deleted, Federer
    4.1.6, p. 352, in v^(i). *)
Definition exterior_omitted_tuple (T:Type) m (t:m.+1.-tuple T) (i:'I_m.+1):m.-tuple T:=
  [tuple tnth t (lift i j)|j<m].

(** Source for [exterior_signed_omission]: the original
    v^(i)=(-1)^(i-1) v_1 wedge ... wedge
    omitted v_i ... wedge v_(m+1), Federer
    4.1.6, p. 352. Ordinals start at zero. *)
Definition exterior_signed_omission (K:fieldType) (V:lmodType K) m
    (t:m.+1.-tuple V) (i:'I_m.+1):exterior_power V m:=
  (-1:K)^+(val i) *: e_lambda (@idfun V) (exterior_omitted_tuple t i).

(** Source for [exterior_differential_trace]: the original
    signed evaluation sum defining d phi(x), Federer
    4.1.6, p. 352, applied to a supplied
    actual linear differential. *)
Definition exterior_differential_trace (K:fieldType) (V W:lmodType K) m
    (L:Hom V (A_m V W m)) (t:m.+1.-tuple V):W:=
  \sum_(i:'I_m.+1) pairing (exterior_signed_omission t i) (L (tnth t i)).

(** Source for [is_exterior_differential_value]: the
    literal first displayed defining formula for
    d phi(x), Federer 4.1.6, p. 352.
    A witness must have every original tuple value. *)
Definition is_exterior_differential_value (K:fieldType) (V W:lmodType K) m
    (L:Hom V (A_m V W m)) (a:A_m V W m.+1):Prop:=
  forall t:m.+1.-tuple V,a t=exterior_differential_trace L t.

(** Source for [exterior_differential_value_unique]: the
    original evaluation formula determines one form,
    Federer 4.1.6, p. 352. This conclusion
    precedes any existence construction. *)
Lemma exterior_differential_value_unique (K:fieldType) (V W:lmodType K) m
    (L:Hom V (A_m V W m)) (a b:A_m V W m.+1):
  is_exterior_differential_value L a ->is_exterior_differential_value L b ->a=b.
Proof. move=>ha hb; apply:form_ext=>t; by rewrite ha hb. Qed.
