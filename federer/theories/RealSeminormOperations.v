(** Federer (1969), 1.10.5, pp. 47-48: supporting seminorm estimates on
    finite sums and linear images. Source context: RealNormUP.v. These
    elementary consequences of the supplied laws support the decomposition
    proof, without a coordinate construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_seminorm_sequence_sum]: Federer 1.10.5,
    p. 48, supporting triangle inequality for a finite decomposition,
    allowing repetitions and the empty sum. *)
Lemma real_seminorm_sequence_sum (R : realFieldType) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) (I : Type) (s : seq I) (f : I -> V) :
  N (\sum_(i <- s) f i) <= \sum_(i <- s) N (f i).
Proof.
elim: s=> [|i s ih]; first by rewrite !big_nil (real_seminorm_zero hN).
rewrite !big_cons; apply: le_trans (real_seminorm_triangle hN _ _) _.
exact: lerD (lexx _) ih.
Qed.

(** Source for [real_seminorm_linear_precompose]: Federer 1.10.5,
    pp. 47-48, supporting pullback of a seminorm under a linear
    map. The map need not be injective or surjective. *)
Lemma real_seminorm_linear_precompose (R : realFieldType) (V W : lmodType R)
    (N : W -> R) (hN : is_real_seminorm N) (f : V -> W) (hf : linear f) :
  is_real_seminorm (fun x => N (f x)).
Proof.
constructor.
- move=> x; exact: real_seminorm_nonnegative hN (f x).
- move=> a x; by rewrite (linZ hf) (real_seminorm_scale hN).
- move=> x y; rewrite (linD hf); exact: real_seminorm_triangle hN (f x) (f y).
Qed.

(** Source for [real_seminorm_positive_multiple]: Federer 1.10.5,
    p. 48, supporting rescaling of the bound used in the Hahn-Banach
    argument. A nonnegative scalar multiple of a seminorm is a seminorm. *)
Lemma real_seminorm_positive_multiple (R : realFieldType) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) C (hC : 0 <= C) :
  is_real_seminorm (fun x => C * N x).
Proof.
constructor.
- move=> x; exact: mulr_ge0 hC (real_seminorm_nonnegative hN x).
- move=> a x; by rewrite (real_seminorm_scale hN) mulrCA.
- move=> x y; rewrite -mulrDr.
  exact (ler_wpM2l hC (real_seminorm_triangle hN x y)).
Qed.

(** Source for [real_norm_injective_precompose]: Federer 1.10.5,
    p. 48, supporting restriction of the norm to a finite-dimensional
    subspace. Injectivity preserves positive definiteness. *)
Lemma real_norm_injective_precompose (R : realFieldType) (V W : lmodType R)
    (N : W -> R) (hN : is_real_norm N) (f : {linear V -> W})
    (hf : injective f) : is_real_norm (fun x => N (f x)).
Proof.
split; first exact (@real_seminorm_linear_precompose R V W N (proj1 hN) f (linearP f)).
move=> x hx; apply: hf; rewrite linear0; exact: (proj2 hN).
Qed.
