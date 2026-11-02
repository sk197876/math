(** Federer (1969), 1.10.5, p. 48: existence of the positive-degree mass
    infimum. editions in SymmetricMassInfimumUP.v. This private construction
    uses real completeness and the previously proved existence and
    nonnegative costs of decompositions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP SymmetricAlgebra SymmetricGrading
  SymmetricDecompositions SymmetricDecompositionCosts SymmetricMassInfimumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [symmetric_mass_infimum_exists]: Federer 1.10.5,
    p. 48, supporting existence of the infimum. Every positive-degree
    symmetric vector admits a finite decomposition and all its costs
    are nonnegative, so the infimum is a finite real number. *)
Theorem symmetric_mass_infimum_exists (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) m (hm : (0<m)%N)
    (x : symmetric_power V m) : exists c, is_symmetric_mass_infimum N x c.
Proof.
pose S := symmetric_decomposition_costs N x.
have hn : S !=set0.
  have [s hs] := symmetric_decomposition_exists hm x.
  exists (symmetric_decomposition_cost N s); by exists s.
have hl : lbound S 0.
  move=> r [s [hs ->]]; exact (@symmetric_decomposition_cost_nonnegative R V N hN m s).
have hb : has_lbound S by exists 0.
have hi : has_inf S by split.
exists (inf S); constructor.
- exact: lb_le_inf hn hl.
- move=> s hs; apply: (ge_inf hb); exists s; by [].
- move=> eps he; have [r [s [hs hr]] hh] := inf_adherent he hi.
  exists s; split=> //; by rewrite -hr.
Qed.
