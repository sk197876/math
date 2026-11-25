(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    def:sv: existence of the number sv_m(X) for 1 <= m <= dim V. The
    supremum of the real numbers t admitting P in G(V,m) with
    t <= |X(v)| for v in P, |v| = 1, is taken in the complete field R;
    this set is nonempty since G(V,m) is nonempty, and bounded above by
    the operator norm ||X|| (Federer 1.7.6). Private: later files use
    DgprSingularValue.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets boolp.
From Federer Require Import InnerProductUP InnerNorm LinearBasis Hom OperatorNorm
  GrassmannSubspaces.
From DPGPR Require Import DgprSingularValueUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dgpr_sv_exists]: blueprint def:sv, existence of the
    supremum defining sv_m(X) when 1 <= m <= n and V has a basis of n
    members. *)
Theorem dgpr_sv_exists (R : realType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m <= n)%N)
    (X : Hom V W) :
  exists s, is_dgpr_sv hB hC m X s.
Proof.
have /andP [hm0 hmn] := hm.
pose S : set R := [set t | exists P : G V m, dgpr_sv_lower_bound hB hC X P t].
have [P0 _] := dgpr_grassmann_nonempty he hmn.
have hS0 : S 0.
  exists P0 => v _ _; exact: inner_norm_nonnegative.
pose M := linear_operator_norm hB hC he (hom_as_linear X).
have hSM : ubound S M.
  move=> t [P hP]; have [v [hv hv1]] := dgpr_grassmann_unit_vector hB P hm0.
  apply: le_trans (hP v hv hv1) _.
  have := linear_operator_norm_bound hB hC he (hom_as_linear X) v.
  by rewrite hom_as_linearE hv1 mulr1.
have hsup : has_sup S by split; [exists 0|exists M].
exists (sup S); constructor.
- move=> P t hP; apply: (ub_le_sup hsup.2); by exists P.
- move=> r hr; have hpos : 0 < sup S - r by rewrite subr_gt0.
  have [t [P hP] ht] := sup_adherent hpos hsup.
  exists P; apply: (dgpr_sv_lower_bound_mono _ hP).
  by move: ht; rewrite opprB addrCA subrr addr0 => /ltW.
Qed.
