(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import TensorUP FreeVector Bilinear.
From Federer Require Import LinearBasis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.3.2: finite coefficient spaces, written
    as functions on the index set. No matrix representation is used. *)
Section Coordinates.
Variable K : fieldType.
(** Source for [coordinate_space]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Definition or construction used to formalise this
    passage. *)
Definition coordinate_space n : lmodType K :=
  GRing.Lmodule.clone K {ffun 'I_n -> K^o} _.

(** Source for [coordinate_basis]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Definition or construction used to formalise this
    passage. *)
Definition coordinate_basis n (i : 'I_n) : coordinate_space n :=
  [ffun j => if j == i then 1 else 0].
(** Source for [coordinate_from_free]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition coordinate_from_free n (c : free_vector K (Choice.clone 'I_n _)) : coordinate_space n :=
  [ffun i => (c i : K^o)].
(** Source for [coordinate_from_free_linear]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_from_free_linear n : linear (@coordinate_from_free n).
Proof.
move=> a x y; apply/ffunP=> i; rewrite /coordinate_from_free !ffunE free_addE free_scaleE.
by [].
Qed.
HB.instance Definition _ n := GRing.isLinear.Build K
  (free_vector K (Choice.clone 'I_n _)) (coordinate_space n)
  *:%R (@coordinate_from_free n) (@coordinate_from_free_linear n).
(** Source for [coordinate_to_free]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition coordinate_to_free n (v : coordinate_space n) : free_vector K (Choice.clone 'I_n _) :=
  [fsfun i in [fset j | j : 'I_n] => v i | 0].
(** Source for [coordinate_to_freeE]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_to_freeE n (v : coordinate_space n) i : coordinate_to_free v i = v i.
Proof. by rewrite /coordinate_to_free fsfunE inE. Qed.
(** Source for [coordinate_to_free_linear]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_to_free_linear n : linear (@coordinate_to_free n).
Proof.
move=> a x y; apply/fsfunP=> i.
by rewrite !coordinate_to_freeE free_addE free_scaleE !coordinate_to_freeE !ffunE.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build K (coordinate_space n)
  (free_vector K (Choice.clone 'I_n _)) *:%R (@coordinate_to_free n) (@coordinate_to_free_linear n).
(** Source for [coordinate_from_freeK]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_from_freeK n : cancel (@coordinate_from_free n) (@coordinate_to_free n).
Proof. by move=> c; apply/fsfunP=> i; rewrite coordinate_to_freeE /coordinate_from_free ffunE. Qed.
(** Source for [coordinate_to_freeK]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_to_freeK n : cancel (@coordinate_to_free n) (@coordinate_from_free n).
Proof. by move=> v; apply/ffunP=> i; rewrite /coordinate_from_free ffunE coordinate_to_freeE. Qed.
(** Source for [coordinate_from_free_delta]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_from_free_delta n i : coordinate_from_free (delta K i) = @coordinate_basis n i.
Proof. by apply/ffunP=> j; rewrite /coordinate_from_free /coordinate_basis !ffunE deltaE. Qed.

(** Source for [coordinate_basisP]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_basisP n : is_basis (@coordinate_basis n).
Proof.
have h := @basis_transport K (Choice.clone 'I_n _)
  (GRing.Lmodule.clone K (free_vector K (Choice.clone 'I_n _)) _) (coordinate_space n)
  (@delta K (Choice.clone 'I_n _))
  (GRing.Linear.clone _ _ _ _ (@coordinate_from_free n) _)
  (GRing.Linear.clone _ _ _ _ (@coordinate_to_free n) _)
  (@coordinate_from_freeK n) (@coordinate_to_freeK n) (free_basis K (Choice.clone 'I_n _)).
exact: basis_congr (coordinate_from_free_delta (n:=n)) h.
Qed.

(** Source for [coordinate_zero]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma coordinate_zero (v : coordinate_space 0) : v = 0.
Proof. apply/ffunP=> i; have h := valP i; by rewrite ltn0 in h. Qed.

(** Federer 1.3.2: splitting off the first basis vector gives the three
    identities required of f, phi, g, psi in the direct-sum argument. *)
Variable n : nat.
(** Source for [coordinate_head]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Definition or construction used to formalise this
    passage. *)
Definition coordinate_head (v : coordinate_space n.+1) : K^o := v ord0.
(** Source for [coordinate_head_linear]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_head_linear : linear coordinate_head.
Proof. by move=> a v w; rewrite /coordinate_head !ffunE. Qed.
HB.instance Definition _ := GRing.isLinear.Build K (coordinate_space n.+1) K^o
  *:%R coordinate_head coordinate_head_linear.
(** Source for [coordinate_tail]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Definition or construction used to formalise this
    passage. *)
Definition coordinate_tail (v : coordinate_space n.+1) : coordinate_space n :=
  [ffun i => v (lift ord0 i)].
(** Source for [coordinate_tail_linear]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_tail_linear : linear coordinate_tail.
Proof. by move=> a v w; apply/ffunP=> i; rewrite /coordinate_tail !ffunE. Qed.
HB.instance Definition _ := GRing.isLinear.Build K (coordinate_space n.+1) (coordinate_space n)
  *:%R coordinate_tail coordinate_tail_linear.
(** Source for [coordinate_head_inclusion]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition coordinate_head_inclusion (a : K^o) : coordinate_space n.+1 :=
  [ffun i => if i == ord0 then a else 0].
(** Source for [coordinate_head_inclusion_linear]: Federer (1969), 1.3.2,
    pp. 14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_head_inclusion_linear : linear coordinate_head_inclusion.
Proof.
move=> a v w; apply/ffunP=> i; rewrite /coordinate_head_inclusion !ffunE.
by case: ifP=> _; rewrite ?scaler0 ?add0r.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K K^o (coordinate_space n.+1)
  *:%R coordinate_head_inclusion coordinate_head_inclusion_linear.
(** Source for [coordinate_tail_inclusion]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition coordinate_tail_inclusion (v : coordinate_space n) : coordinate_space n.+1 :=
  [ffun i => if unlift ord0 i is Some j then v j else 0].
(** Source for [coordinate_tail_inclusion_linear]: Federer (1969), 1.3.2,
    pp. 14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_tail_inclusion_linear : linear coordinate_tail_inclusion.
Proof.
move=> a v w; apply/ffunP=> i; rewrite /coordinate_tail_inclusion !ffunE.
by case: (unlift ord0 i) => [j|]; rewrite ?ffunE ?scaler0 ?add0r.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K (coordinate_space n) (coordinate_space n.+1)
  *:%R coordinate_tail_inclusion coordinate_tail_inclusion_linear.

(** Source for [coordinate_headK]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma coordinate_headK : cancel coordinate_head_inclusion coordinate_head.
Proof. by move=> a; rewrite /coordinate_head /coordinate_head_inclusion ffunE eqxx. Qed.
(** Source for [coordinate_tailK]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma coordinate_tailK : cancel coordinate_tail_inclusion coordinate_tail.
Proof.
by move=> v; apply/ffunP=> i; rewrite /coordinate_tail /coordinate_tail_inclusion !ffunE liftK.
Qed.
(** Source for [coordinate_decomposition]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_decomposition v :
  coordinate_head_inclusion (coordinate_head v) + coordinate_tail_inclusion (coordinate_tail v) = v.
Proof.
apply/ffunP=> i; rewrite /coordinate_head_inclusion /coordinate_tail_inclusion !ffunE.
case: (unliftP ord0 i) => [j ->|->].
- by rewrite lift_eqF add0r /coordinate_tail ffunE.
- by rewrite eqxx addr0.
Qed.
(** Source for [coordinate_head_basis]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_head_basis : coordinate_head_inclusion 1 = coordinate_basis ord0.
Proof. by []. Qed.
(** Source for [coordinate_tail_basis]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma coordinate_tail_basis i :
  coordinate_tail_inclusion (coordinate_basis i) = coordinate_basis (lift ord0 i).
Proof.
apply/ffunP=> j; rewrite /coordinate_tail_inclusion /coordinate_basis !ffunE.
case: (unliftP ord0 j) => [k ->|->].
- by rewrite ffunE (inj_eq (@lift_inj _ ord0)).
- by rewrite eq_liftF.
Qed.
End Coordinates.
Arguments coordinate_space K n : assert.
