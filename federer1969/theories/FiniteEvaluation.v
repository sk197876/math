(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From mathcomp.classical Require Import boolp.
From Federer Require Import AlternatingCoordinates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.4: a finite family of linear
    functionals is recovered from finitely many evaluations. This is
    the finite part of the dual-basis argument; V remains arbitrary. *)
Section FiniteEvaluation.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [evaluation_reconstruction]: Federer (1969), 1.4.4, p. 19,
    monomorphism assertion and basis argument. In words: Omega is injective
    because it takes exterior products of independent covectors to their
    independent alternating products. Definition or construction used to
    formalise this passage. *)
Definition evaluation_reconstruction n (e : 'I_n -> V) (omega : 'I_n -> Hom V K^o)
    (phi : Hom V K^o) : Hom V K^o := \sum_i (phi (e i) : K) *: omega i.
(** Source for [evaluation_reconstructionE]: Federer (1969), 1.4.4, p. 19,
    monomorphism assertion and basis argument. In words: Omega is injective
    because it takes exterior products of independent covectors to their
    independent alternating products. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma evaluation_reconstructionE n (e : 'I_n -> V) omega phi v :
  evaluation_reconstruction e omega phi v = \sum_i phi (e i) * omega i v.
Proof. rewrite /evaluation_reconstruction hom_sumE; apply: eq_bigr => i _; exact: hom_scaleE. Qed.
(** Source for [evaluation_reconstruction_step]: Federer (1969), 1.4.4, p.
    19, monomorphism assertion and basis argument. In words: Omega is
    injective because it takes exterior products of independent covectors to
    their independent alternating products. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma evaluation_reconstruction_step n (e : 'I_n -> V) (omega : 'I_n -> Hom V K^o) (r phi : Hom V K^o) v c :
  evaluation_reconstruction (ordinal_cons v e)
    (ordinal_cons (c *: r) (fun i => omega i - (c * omega i v) *: r)) phi =
  evaluation_reconstruction e omega phi +
    (c * (phi v - evaluation_reconstruction e omega phi v)) *: r.
Proof.
have hc : (\sum_i phi (e i) * (c * omega i v)) =
    c * evaluation_reconstruction e omega phi v.
  rewrite evaluation_reconstructionE mulr_sumr; apply: eq_bigr => i _.
  exact: mulrCA.
have ht : (\sum_i (phi (e i) : K) *: (omega i - (c * omega i v) *: r)) =
    evaluation_reconstruction e omega phi - (c * evaluation_reconstruction e omega phi v) *: r.
  under eq_bigr do rewrite scalerBr scalerA.
  by rewrite sumrB -scaler_suml hc.
rewrite /evaluation_reconstruction big_ord_recl !ordinal_cons0 scalerA.
under [X in _ + X = _]eq_bigr do rewrite !ordinal_consS.
change ((phi v*c : K) *: r + (\sum_i (phi (e i) : K) *: (omega i - (c*omega i v) *: r)) =
  evaluation_reconstruction e omega phi + (c*(phi v-evaluation_reconstruction e omega phi v)) *: r).
by rewrite ht mulrBr scalerBl [phi v*c]mulrC addrCA.
Qed.
(** Source for [finite_evaluation_reconstruction]: Federer (1969), 1.4.4, p.
    19, monomorphism assertion and basis argument. In words: Omega is
    injective because it takes exterior products of independent covectors to
    their independent alternating products. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Theorem finite_evaluation_reconstruction (s : seq (Hom V K^o)) :
  exists n (e : 'I_n -> V) (omega : 'I_n -> Hom V K^o),
    forall phi, phi \in s -> evaluation_reconstruction e omega phi = phi.
Proof.
elim: s => [|a s [n [e [omega he]]]].
- exists 0%N, (fun _ : 'I_0 => 0), (fun _ : 'I_0 => 0); by move=> phi; rewrite in_nil.
- pose r := a - evaluation_reconstruction e omega a.
  case hr : (r == 0).
  + exists n, e, omega => phi; rewrite in_cons => /orP [/eqP ->|hp]; last exact: he hp.
    have /eqP ha : a == evaluation_reconstruction e omega a by move: hr; rewrite /r subr_eq0.
    exact (esym ha).
  + have [v hv] := nonzero_hom_vector (negbT hr).
    pose c : K := (r v)^-1.
    exists n.+1, (ordinal_cons v e),
      (ordinal_cons (c *: r) (fun i => omega i - (c * omega i v) *: r)) => phi hp.
    rewrite evaluation_reconstruction_step.
    move: hp; rewrite in_cons => /orP [/eqP ->|hp].
    * have hc : c * (a v - evaluation_reconstruction e omega a v) = 1.
        change ((r v)^-1 * r v = 1); exact: mulVf hv.
      by rewrite hc scale1r /r addrCA subrr addr0.
    * by rewrite (he phi hp) subrr mulr0 scale0r addr0.
Qed.
End FiniteEvaluation.
