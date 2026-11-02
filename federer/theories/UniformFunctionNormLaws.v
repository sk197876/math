(** Laws of Federer's uniform norm, 2.5.19, p. 113, supporting the dense
    extension in 2.6.6, p. 120. Proofs use only the least-bound
    specification, not a chosen maximum or supremum. Source context and
    conventions: UniformFunctionNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP UniformFunctionNormUP VectorFunctionLattice FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [uniform_function_norm_zero]: the norm of zero is zero,
    supporting the normed-space argument in Federer 2.6.6, p. 120. *)
Lemma uniform_function_norm_zero (R : realType) (X : Type) :
  is_uniform_function_norm (fun _ : X => (0 : R)) 0.
Proof. constructor=> // x; by rewrite normr0. Qed.

(** Source for [uniform_function_norm_separates]: the uniform norm
    separates literal functions, as required for the norm of K(X) in
    Federer 2.5.19, p. 113, and 2.6.6, p. 120. *)
Lemma uniform_function_norm_separates (R : realType) (X : Type) (f : X -> R) :
  is_uniform_function_norm f 0 -> forall x, f x=0.
Proof.
move=> hn x; apply/eqP; rewrite -normr_eq0 eq_le normr_ge0 andbT.
exact: uniform_function_norm_bound hn x.
Qed.

(** Source for [uniform_function_norm_scale]: absolute homogeneity
    of nu, supporting Federer 2.6.6, p. 120. *)
Lemma uniform_function_norm_scale (R : realType) (X : Type) (f : X -> R) n c :
  is_uniform_function_norm f n ->
  is_uniform_function_norm (fun x => c*f x) (`|c|*n).
Proof.
move=> hn; constructor.
- exact: mulr_ge0 (normr_ge0 c) (uniform_function_norm_nonnegative hn).
- move=> x; rewrite normrM; apply: ler_wpM2l; [exact: normr_ge0|exact: uniform_function_norm_bound hn x].
- move=> b hb hcb; case: (eqVneq c 0)=> hc.
  + by rewrite hc normr0 mul0r.
  + have hcpos : 0<`|c| by rewrite normr_gt0.
    rewrite mulrC -ler_pdivlMr //.
    apply: (@uniform_function_norm_least R X f n hn (b/`|c|)); first exact: divr_ge0 hb (normr_ge0 c).
    move=> x; rewrite ler_pdivlMr // mulrC -normrM; exact: hcb.
Qed.

(** Source for [uniform_function_norm_triangle]: the triangle bound
    for nu, supporting the continuous extension in Federer 2.6.6,
    p. 120; the sum need not attain its maximum at either factor's
    maximum point. *)
Lemma uniform_function_norm_triangle (R : realType) (X : Type) (f g : X -> R) n m k :
  is_uniform_function_norm f n -> is_uniform_function_norm g m ->
  is_uniform_function_norm (fun x => f x+g x) k -> k<=n+m.
Proof.
move=> hf hg hs; apply: (@uniform_function_norm_least R X _ k hs (n+m)).
- exact: addr_ge0 (uniform_function_norm_nonnegative hf) (uniform_function_norm_nonnegative hg).
- move=> x; exact: le_trans (ler_normD _ _) (lerD (uniform_function_norm_bound hf x) (uniform_function_norm_bound hg x)).
Qed.

(** Source for [uniform_function_norm_seminorm]: all finite seminorm
    laws of nu, Federer 2.5.19, p. 113, on any vector lattice
    where its least-bound values exist; used in 2.6.6, p. 120. *)
Theorem uniform_function_norm_seminorm (R : realType) (X : Type)
    (L : set (X -> R)) (N : (X -> R) -> R) :
  is_vector_function_lattice L ->
  (forall f, L f -> is_uniform_function_norm f (N f)) ->
  is_finite_function_seminorm L N.
Proof.
move=> hL hN; constructor.
- move=> f hf; exact: uniform_function_norm_nonnegative (hN f hf).
- move=> c f hf; exact (@uniform_function_norm_unique R X (fun x=>c*f x) _ _
    (hN _ (hL.2.2 c f hf)) (@uniform_function_norm_scale R X f (N f) c (hN f hf))).
- move=> f g hf hg; exact: uniform_function_norm_triangle (hN f hf) (hN g hg)
    (hN _ (@function_lattice_add R X L hL.1 f g hf hg)).
Qed.
