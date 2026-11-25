(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import TensorUP FreeVector Bilinear GradedAlgebra GradedComponents.
From Federer Require Import LinearBasis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for the basis assertion of Federer 1.3.2: injective
    relabellings of coefficient indices and the degree-n part of a graded basis. *)
Section InjectiveRelabelling.
Variable K : fieldType.
Variables I J : choiceType.
Variable h : I -> J.
Hypothesis hi : injective h.
Local Notation FI := (GRing.Lmodule.clone K (free_vector K I) _).
Local Notation FJ := (GRing.Lmodule.clone K (free_vector K J) _).

(** Source for [free_map_evaluation]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma free_map_evaluation i x : free_map K h x (h i) = x i.
Proof.
apply: (free_linear_ext
  (linear_comp (GRing.Linear.clone _ _ _ _ (@free_eval K J (h i)) _) (free_map K h))
  (GRing.Linear.clone _ _ _ _ (@free_eval K I i) _)) x => j.
change (free_map K h (delta K j) (h i) = delta K j i).
by rewrite free_mapE !deltaE (inj_eq hi).
Qed.
(** Source for [free_map_injective]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma free_map_injective : injective (free_map K h).
Proof.
move=> x y hxy; apply/fsfunP=> i.
exact: eq_trans (esym (free_map_evaluation i x))
  (eq_trans (congr1 (fun z : FJ => z (h i)) hxy) (free_map_evaluation i y)).
Qed.
End InjectiveRelabelling.

Section GradedBasis.
Variable K : fieldType.
Variable I : choiceType.
Variable V : lmodType K.
Variable G : grading V.
Variable e : I -> V.
Variable d : I -> nat.
Hypotheses (hb : is_basis e) (he : forall i, homogeneous G (d i) (e i)).
Variable n : nat.
Local Notation In := (Choice.clone {i : I | d i == n} _).
Local Notation Vn := (graded_component G n).
Local Notation Fn := (GRing.Lmodule.clone K (free_vector K In) _).

(** Source for [component_basis_homogeneous]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma component_basis_homogeneous (i : In) : homogeneous G n (e (val i)).
Proof.
have h := he (val i); have hn := eqP (valP i).
by rewrite hn in h.
Qed.
(** Source for [component_basis]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Definition or construction used to formalise this
    passage. *)
Definition component_basis (i : In) : Vn :=
  @Component K V G n (e (val i)) (introT eqP (component_basis_homogeneous i)).
(** Source for [component_basisE]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma component_basisE i : component_val (component_basis i) = e (val i).
Proof. by []. Qed.

(** Source for [component_basis_synthesis]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma component_basis_synthesis c :
  component_val (basis_synthesis component_basis c) =
  basis_synthesis e (free_map K (fun i : In => (val i : I)) c).
Proof.
apply: (free_linear_ext
  (linear_comp (GRing.Linear.clone _ _ _ _ (@component_val K V G n) _)
    (basis_synthesis component_basis))
  (linear_comp (basis_synthesis e) (free_map K (fun i : In => (val i : I))))) c => i.
change (component_val (basis_synthesis component_basis (delta K i)) =
  basis_synthesis e (free_map K (fun i : In => (val i : I)) (delta K i))).
by rewrite free_mapE !basis_synthesisE.
Qed.

(** Source for [component_basis_synthesis_injective]: Federer (1969), 1.3.2,
    pp. 14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma component_basis_synthesis_injective : injective (basis_synthesis component_basis).
Proof.
move=> x y hxy; apply: (@free_map_injective K In I (fun i : In => (val i : I)) val_inj).
apply: (basis_synthesis_injective hb).
by rewrite -!component_basis_synthesis hxy.
Qed.

(** Source for [component_basis_spans]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma component_basis_spans x : exists c, basis_synthesis component_basis c = x.
Proof.
have hs : forall v, exists c, basis_synthesis component_basis c = component G n v.
  apply: (basis_induction hb) => [|v w [a ha] [b hb']|a v [c hc]|i].
  - exists 0; by rewrite !linear0.
  - exists (a + b); by rewrite !linearD ha hb'.
  - exists (a *: c); by rewrite !linearZ hc.
  case hdi: (d i == n).
  - exists (delta K (Sub i hdi : In)); rewrite basis_synthesisE.
    apply/val_inj; change (e i = grade G n (e i)).
    by rewrite (grade_homogeneous n (he i)) eq_sym hdi.
  - exists 0; rewrite linear0; apply/val_inj.
    change (component_val (0 : Vn) = grade G n (e i)).
    by rewrite linear0 (grade_homogeneous n (he i)) eq_sym hdi.
have [c hc] := hs (component_val x); exists c.
by rewrite componentK in hc.
Qed.

(** Source for [component_basisP]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem component_basisP : is_basis component_basis.
Proof.
apply/basisP; split; [exact: component_basis_synthesis_injective | exact: component_basis_spans].
Qed.
End GradedBasis.
