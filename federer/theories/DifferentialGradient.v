(** Public gradient of Federer (1969), 3.1.1, p. 209. Only the
    opaque pairing equation is used; no coordinates or projection
    construction appear in downstream proofs. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom InnerProductUP InnerNorm InnerNormInequalities
  RealNormUP NormDifferentialUP NormDifferentialDirectional
  DifferentialGradientUP DifferentialGradientSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(** Source for [norm_gradient]: grad f(a) in Federer 3.1.1, p. 209.
    A differentiability proof supplies the continuous differential; the
    sealed interface supplies its unique inner-product representative. *)
Definition norm_gradient (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hspace : differential_gradient_space hB) (A : V -> Prop)
    (f : V -> R) (a : V) (L : Hom V R^o)
    (hf : has_norm_differential (inner_norm hB) (fun t : R^o => `|t|) A f a L) : V :=
  @DifferentialGradient.value R V B hB hspace L (norm_differential_bounded hf).

(** Source for [norm_gradient_pairing]: the defining equation
    Df(a)(v)=v.grad f(a), Federer 3.1.1, p. 209. *)
Theorem norm_gradient_pairing (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hspace : differential_gradient_space hB) (A : V -> Prop)
    (f : V -> R) (a : V) (L : Hom V R^o)
    (hf : has_norm_differential (inner_norm hB) (fun t : R^o => `|t|) A f a L) v :
  L v = B v (norm_gradient hspace hf).
Proof. exact: DifferentialGradient.laws. Qed.

(** Source for [norm_gradient_characterisation]: the gradient of
    Federer 3.1.1, p. 209, is exactly the vector satisfying its printed
    pairing equation. In particular, the selected vector is intrinsic. *)
Theorem norm_gradient_characterisation (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hspace : differential_gradient_space hB) (A : V -> Prop)
    (f : V -> R) (a : V) (L : Hom V R^o)
    (hf : has_norm_differential (inner_norm hB) (fun t : R^o => `|t|) A f a L) u :
  is_differential_gradient B L u <-> u = norm_gradient hspace hf.
Proof.
split=> [hu|->]; last exact: DifferentialGradient.laws.
exact: (@differential_gradient_unique R V B hB L u
  (norm_gradient hspace hf) hu (DifferentialGradient.laws hspace _)).
Qed.

(** Source for [norm_gradient_independent]: intrinsicness of grad f(a)
    in Federer 3.1.1, p. 209. Neither the proof of differentiability,
    its candidate linear map, nor the choice of the finite-dimensional
    or complete-space existence argument affects the resulting vector. *)
Theorem norm_gradient_independent (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hspace hspace' : differential_gradient_space hB) (A : V -> Prop)
    (f : V -> R) (a : V) (L M : Hom V R^o)
    (hf : has_norm_differential (inner_norm hB) (fun t : R^o => `|t|) A f a L)
    (hg : has_norm_differential (inner_norm hB) (fun t : R^o => `|t|) A f a M) :
  norm_gradient hspace hf = norm_gradient hspace' hg.
Proof.
have hN : is_real_norm (inner_norm hB).
  split.
  - split; [exact: inner_norm_nonnegative|exact: inner_normZ|exact: inner_norm_triangle].
  - move=> x hx; apply/eqP; by rewrite -(inner_norm_eq0 hB) hx eqxx.
have hLM := norm_differential_unique hN (@scalar_absolute_value_norm R) hf hg.
apply: (@differential_gradient_unique R V B hB L).
- exact: norm_gradient_pairing.
- move=> v; rewrite hLM; exact: norm_gradient_pairing.
Qed.
