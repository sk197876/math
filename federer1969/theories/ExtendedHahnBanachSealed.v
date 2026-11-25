(** Federer (1969), 2.4.12, p. 86: opaque encapsulation of the proved
    extended-seminorm Hahn–Banach construction. Source context:
    ExtendedSeminormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedSeminormUP PartialLinearMap ExtendedHahnBanachConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Module Type EXTENDED_HAHN_BANACH.
(** Source for [extension]: Federer 2.4.12, p. 86,
    Hahn–Banach extension with its agreement and domination laws.
    The sealed implementation proves these obligations for the
    extended-valued seminorm specification. *)
Parameter extension : forall (R : realType) (V : lmodType R)
  (N : V -> \bar R), is_extended_seminorm N -> forall G : V -> R^o -> Prop,
  linear_graph G -> (forall x a, G x a -> (a%:E <= N x)%E) -> {linear V -> R^o}.
(** Source for [agreement]: Federer 2.4.12, p. 86,
    Hahn–Banach extension with its agreement and domination laws.
    The sealed implementation proves these obligations for the
    extended-valued seminorm specification. *)
Parameter agreement : forall (R : realType) (V : lmodType R)
  (N : V -> \bar R) (hN : is_extended_seminorm N) (G : V -> R^o -> Prop)
  (hG : linear_graph G) (hdom : forall x a, G x a -> (a%:E <= N x)%E) x a,
  G x a -> @extension R V N hN G hG hdom x=a.
(** Source for [bound]: Federer 2.4.12, p. 86,
    Hahn–Banach extension with its agreement and domination laws.
    The sealed implementation proves these obligations for the
    extended-valued seminorm specification. *)
Parameter bound : forall (R : realType) (V : lmodType R)
  (N : V -> \bar R) (hN : is_extended_seminorm N) (G : V -> R^o -> Prop)
  (hG : linear_graph G) (hdom : forall x a, G x a -> (a%:E <= N x)%E) x,
  ((@extension R V N hN G hG hdom x)%:E <= N x)%E.
End EXTENDED_HAHN_BANACH.
Module ExtendedHahnBanach : EXTENDED_HAHN_BANACH.
(** Source for [extension]: Federer 2.4.12, p. 86,
    Hahn–Banach extension with its agreement and domination laws.
    The sealed implementation proves these obligations for the
    extended-valued seminorm specification. *)
Definition extension (R : realType) (V : lmodType R)
    (N : V -> \bar R) (hN : is_extended_seminorm N) (G : V -> R^o -> Prop)
    (hG : linear_graph G) (hdom : forall x a, G x a -> (a%:E <= N x)%E) : {linear V -> R^o} :=
  GRing.Linear.clone _ _ _ _ (@extended_dominated_linear_extension R V N hN G hG hdom) _.
(** Source for [agreement]: Federer 2.4.12, p. 86,
    Hahn–Banach extension with its agreement and domination laws.
    The sealed implementation proves these obligations for the
    extended-valued seminorm specification. *)
Lemma agreement (R : realType) (V : lmodType R)
    (N : V -> \bar R) (hN : is_extended_seminorm N) (G : V -> R^o -> Prop)
    (hG : linear_graph G) (hdom : forall x a, G x a -> (a%:E <= N x)%E) x a :
  G x a -> @extension R V N hN G hG hdom x=a.
Proof. exact: extended_dominated_linear_extensionE. Qed.
(** Source for [bound]: Federer 2.4.12, p. 86,
    Hahn–Banach extension with its agreement and domination laws.
    The sealed implementation proves these obligations for the
    extended-valued seminorm specification. *)
Lemma bound (R : realType) (V : lmodType R)
    (N : V -> \bar R) (hN : is_extended_seminorm N) (G : V -> R^o -> Prop)
    (hG : linear_graph G) (hdom : forall x a, G x a -> (a%:E <= N x)%E) x :
  ((@extension R V N hN G hG hdom x)%:E <= N x)%E.
Proof. exact: extended_dominated_linear_extension_bound. Qed.
End ExtendedHahnBanach.
