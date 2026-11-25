(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorMultiplication.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.2: compare a multivector by pairing with the dual
    Grassmann basis, just as a covector is compared on the vector basis. *)
(** Source for [pairing_covector_basis_ext]: Federer (1969), 1.5.2, p. 22,
    the two inclusion cases and the definitions of M and N. In words: A
    basis interior product vanishes unless the contracted index set is
    contained in the other; otherwise it is the complementary basis product
    with the appropriate crossing-count sign. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem pairing_covector_basis_ext (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n m (e : 'I_n -> V) (omega : 'I_n -> A_m V K^o 1)
  (he : is_basis e)
  (hdual : forall i j, omega i [tuple e j] = if i == j then 1 else 0)
  (xi eta : exterior_power V m) :
  (forall lambda : Lambda n m,
    pairing xi (omega_lambda h2 omega lambda) = pairing eta (omega_lambda h2 omega lambda)) ->
  xi = eta.
Proof.
move=> h; apply: pairing_vectors_separate => phi.
exact (@basis_linear_ext K (Choice.clone (Lambda n m) _) (A_m V K^o m)
  (@omega_lambda K h2 V n omega m) (@omega_lambda_basis K h2 V n m e omega he hdual)
  K^o (pairing_right xi) (pairing_right eta) h phi).
Qed.
