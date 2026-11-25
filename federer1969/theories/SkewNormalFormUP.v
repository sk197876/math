(** Federer (1969), 1.7.3, pp. 29-30: orthonormal pairs and nonnegative
    coefficients for the alternating two-form. Pairs are indexed by
    (i,false),(i,true), corresponding to consecutive entries 2i+1,2i+2 in
    the book's one-based sequence. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [paired_family]: Federer 1.7.3, p. 29,
    supporting indexing of a sequence by its consecutive pairs. *)
Definition paired_family (T : Type) m (a b : 'I_m -> T) (p : 'I_m * bool) :=
  if p.2 then b p.1 else a p.1.

(** Source for [skew_pair_form]: Federer 1.7.3, pp. 29-30,
    supporting scalar expression for the wedge of the one-covectors
    corresponding to a and b by the inner-product polarity. *)
Definition skew_pair_form (R : fieldType) (V : lmodType R)
    (B : V -> V -> R) (a b x y : V) := B x a * B y b - B x b * B y a.

(** Source for [is_skew_normal_form_on]: Federer 1.7.3,
    pp. 29-30, supporting relative normal-form specification:
    orthonormal pairs in W with nonnegative coefficients express
    f(x).y whenever x belongs to W. It includes the empty family. *)
Record is_skew_normal_form_on (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (f : {linear V -> V}) (W : subspace V)
    m (a b : 'I_m -> V) (lambda : 'I_m -> R) : Prop := {
  skew_normal_first_in : forall i, W (a i);
  skew_normal_second_in : forall i, W (b i);
  skew_normal_orthonormal : orthonormal_family B (paired_family a b);
  skew_normal_nonnegative : forall i, 0 <= lambda i;
  skew_normal_equation : forall x, W x -> forall y,
    B (f x) y = \sum_i lambda i * skew_pair_form B (a i) (b i) x y
}.
