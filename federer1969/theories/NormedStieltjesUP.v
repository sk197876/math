(** Federer (1969), 3.1.11, pp. 220–221:
    normed-vector Riemann–Stieltjes limits in the Taylor
    formula, using the tagged partitions of 2.5.17,
    pp. 110–111. A limit is specified by its approximation
    law; its existence is proved for the particular integrands. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP StieltjesSums.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_stieltjes_sum]:
    the vector-valued version of the finite sums of
    Federer 2.5.17, p. 110, used for the
    Taylor integral in 3.1.11, pp. 220–221.
    The real integrator increment acts by scalar multiplication. *)
Fixpoint normed_stieltjes_sum (R : realType) (Y : lmodType R)
    (f : R->Y) (g : R->R) (w : seq R) : Y :=
  match w with
  | t::u::((t'::_) as rest) =>
      (g t'-g t)*:f u+@normed_stieltjes_sum R Y f g rest
  | _=>0
  end.

(** Source for [has_normed_stieltjes_integral]:
    the norm-limit characterization of the Taylor integral
    in Federer 3.1.11, pp. 220–221, following
    the tagged-sum definition in 2.5.17, pp. 110–111.
    The target is only normed; the definition does not
    assert that every continuous integrand has a target-valued limit. *)
Definition has_normed_stieltjes_integral (R : realType) (Y : lmodType R)
    (NY : Y->R) (f : R->Y) (g : R->R) (a b : R) (v : Y) :=
  a<=b /\ forall e : R, 0<e -> exists d : R, 0<d /\
    forall w, is_tagged_partition a b w -> tagged_mesh_lt d w ->
      NY (normed_stieltjes_sum f g w-v)<e.
