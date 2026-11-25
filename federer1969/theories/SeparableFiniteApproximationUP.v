(** Federer (1969), 2.4.12, p. 87: finite-image density for finite p, with
    the erratum's additional finite-dimensional restriction when p=infinity.
    This supporting specification records finite Borel approximants on such
    a subspace, with a norm majorant for bounded convergence. The
    approximants are total on the ambient space, but error and convergence
    laws apply only on the given subspace. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric ModuleQuotient BorelFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_separable_finite_approximation]: abstract supporting
    approximation laws for Federer 2.4.12, p. 87 A nearest-prefix partition
    supplies the majorant; its implementation is not part of this
    definition. *)
Record is_separable_finite_approximation (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (Z : subspace V)
    (a : nat -> real_norm_metric_space hN -> real_norm_metric_space hN) : Prop := {
  (** Source for [separable_finite_borel]: Borel approximation maps
      supporting Federer 2.4.12, p. 87. *)
  separable_finite_borel : forall n, is_borel_function (a n);
  (** Source for [separable_finite_image]: finite images required
      for the density assertion in Federer 2.4.12, p. 87. *)
  separable_finite_image : forall n, finite_set (a n @` setT);
  (** Source for [separable_finite_range]: supporting preservation of
      the separable linear range in Federer 2.4.12, p. 87. *)
  separable_finite_range : forall n x, Z (a n x);
  (** Source for [separable_finite_error]: norm majorant supporting
      bounded convergence in Federer 2.4.12, p. 87. *)
  separable_finite_error : forall n x, Z x -> N (x-a n x) <= N x;
  (** Source for [separable_finite_converges]: pointwise approximation
      supporting finite-image density in Federer 2.4.12, p. 87. *)
  separable_finite_converges : forall x : real_norm_metric_space hN, Z x -> (fun n => a n x) @ \oo --> x
}.
